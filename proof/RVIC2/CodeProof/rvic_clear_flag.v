Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RVIC.Layer.
Require Import RVIC2.Code.rvic_clear_flag.

Require Import RVIC2.LowSpecs.rvic_clear_flag.

Local Open Scope Z_scope.

Section CodeProof.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Let L : compatlayer (cdata RData) :=
    _interrupt_bitmap_dword ↦ gensem interrupt_bitmap_dword_spec
      ⊕ _interrupt_bit ↦ gensem interrupt_bit_spec
      ⊕ _get_bitmap_loc ↦ gensem get_bitmap_loc_spec
      ⊕ _atomic_bit_clear_release_64 ↦ gensem atomic_bit_clear_release_64_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_interrupt_bitmap_dword: block.
    Hypothesis h_interrupt_bitmap_dword_s : Genv.find_symbol ge _interrupt_bitmap_dword = Some b_interrupt_bitmap_dword.
    Hypothesis h_interrupt_bitmap_dword_p : Genv.find_funct_ptr ge b_interrupt_bitmap_dword
                                            = Some (External (EF_external _interrupt_bitmap_dword
                                                             (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                                   (Tcons tulong Tnil) tulong cc_default).
    Local Opaque interrupt_bitmap_dword_spec.

    Variable b_interrupt_bit: block.
    Hypothesis h_interrupt_bit_s : Genv.find_symbol ge _interrupt_bit = Some b_interrupt_bit.
    Hypothesis h_interrupt_bit_p : Genv.find_funct_ptr ge b_interrupt_bit
                                   = Some (External (EF_external _interrupt_bit
                                                    (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                          (Tcons tulong Tnil) tulong cc_default).
    Local Opaque interrupt_bit_spec.

    Variable b_get_bitmap_loc: block.
    Hypothesis h_get_bitmap_loc_s : Genv.find_symbol ge _get_bitmap_loc = Some b_get_bitmap_loc.
    Hypothesis h_get_bitmap_loc_p : Genv.find_funct_ptr ge b_get_bitmap_loc
                                    = Some (External (EF_external _get_bitmap_loc
                                                     (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) Tptr cc_default))
                                           (Tcons Tptr (Tcons tulong Tnil)) Tptr cc_default).
    Local Opaque get_bitmap_loc_spec.

    Variable b_atomic_bit_clear_release_64: block.
    Hypothesis h_atomic_bit_clear_release_64_s : Genv.find_symbol ge _atomic_bit_clear_release_64 = Some b_atomic_bit_clear_release_64.
    Hypothesis h_atomic_bit_clear_release_64_p : Genv.find_funct_ptr ge b_atomic_bit_clear_release_64
                                                 = Some (External (EF_external _atomic_bit_clear_release_64
                                                                  (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                                        (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque atomic_bit_clear_release_64_spec.

    Lemma rvic_clear_flag_body_correct:
      forall m d d' env le intid bitmap_base bitmap_offset
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTintid: PTree.get _intid le = Some (Vlong intid))
             (HPTbitmap: PTree.get _bitmap le = Some (Vptr bitmap_base (Int.repr bitmap_offset)))
             (Hspec: rvic_clear_flag_spec0 (VZ64 (Int64.unsigned intid)) (bitmap_base, bitmap_offset) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) rvic_clear_flag_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec rvic_clear_flag_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
