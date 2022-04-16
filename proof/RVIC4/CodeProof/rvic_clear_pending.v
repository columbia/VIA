Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import RVIC2.Spec.
Require Import AbsAccessor.Spec.
Require Import RVIC3.Layer.
Require Import RVIC4.Code.rvic_clear_pending.

Require Import RVIC4.LowSpecs.rvic_clear_pending.

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
    _rvic_clear_flag ↦ gensem rvic_clear_flag_spec
      ⊕ _get_rvic_pending_bits ↦ gensem get_rvic_pending_bits_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_rvic_clear_flag: block.
    Hypothesis h_rvic_clear_flag_s : Genv.find_symbol ge _rvic_clear_flag = Some b_rvic_clear_flag.
    Hypothesis h_rvic_clear_flag_p : Genv.find_funct_ptr ge b_rvic_clear_flag
                                     = Some (External (EF_external _rvic_clear_flag
                                                      (signature_of_type (Tcons tulong (Tcons Tptr Tnil)) tvoid cc_default))
                                            (Tcons tulong (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque rvic_clear_flag_spec.

    Variable b_get_rvic_pending_bits: block.
    Hypothesis h_get_rvic_pending_bits_s : Genv.find_symbol ge _get_rvic_pending_bits = Some b_get_rvic_pending_bits.
    Hypothesis h_get_rvic_pending_bits_p : Genv.find_funct_ptr ge b_get_rvic_pending_bits
                                           = Some (External (EF_external _get_rvic_pending_bits
                                                            (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                                  (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rvic_pending_bits_spec.

    Lemma rvic_clear_pending_body_correct:
      forall m d d' env le rvic_base rvic_offset intid
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrvic: PTree.get _rvic le = Some (Vptr rvic_base (Int.repr rvic_offset)))
             (HPTintid: PTree.get _intid le = Some (Vlong intid))
             (Hspec: rvic_clear_pending_spec0 (rvic_base, rvic_offset) (VZ64 (Int64.unsigned intid)) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) rvic_clear_pending_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec rvic_clear_pending_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
