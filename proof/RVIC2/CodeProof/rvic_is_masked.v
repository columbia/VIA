Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RVIC.Spec.
Require Import RVIC.Layer.
Require Import RVIC2.Code.rvic_is_masked.

Require Import RVIC2.LowSpecs.rvic_is_masked.

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
    _get_rvic_mask_bits ↦ gensem get_rvic_mask_bits_spec
      ⊕ _rvic_test_flag ↦ gensem rvic_test_flag_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_get_rvic_mask_bits: block.
    Hypothesis h_get_rvic_mask_bits_s : Genv.find_symbol ge _get_rvic_mask_bits = Some b_get_rvic_mask_bits.
    Hypothesis h_get_rvic_mask_bits_p : Genv.find_funct_ptr ge b_get_rvic_mask_bits
                                        = Some (External (EF_external _get_rvic_mask_bits
                                                         (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                               (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rvic_mask_bits_spec.

    Variable b_rvic_test_flag: block.
    Hypothesis h_rvic_test_flag_s : Genv.find_symbol ge _rvic_test_flag = Some b_rvic_test_flag.
    Hypothesis h_rvic_test_flag_p : Genv.find_funct_ptr ge b_rvic_test_flag
                                    = Some (External (EF_external _rvic_test_flag
                                                     (signature_of_type (Tcons tulong (Tcons Tptr Tnil)) tuint cc_default))
                                           (Tcons tulong (Tcons Tptr Tnil)) tuint cc_default).
    Local Opaque rvic_test_flag_spec.

    Lemma rvic_is_masked_body_correct:
      forall m d env le rvic_base rvic_offset intid res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrvic: PTree.get _rvic le = Some (Vptr rvic_base (Int.repr rvic_offset)))
             (HPTintid: PTree.get _intid le = Some (Vlong intid))
             (Hspec: rvic_is_masked_spec0 (rvic_base, rvic_offset) (VZ64 (Int64.unsigned intid)) d = Some (Int.unsigned res)),
           exists le', (exec_stmt ge env le ((m, d): mem) rvic_is_masked_body E0 le' (m, d) (Out_return (Some (Vint res, tuint)))).
    Proof.
      solve_code_proof Hspec rvic_is_masked_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
