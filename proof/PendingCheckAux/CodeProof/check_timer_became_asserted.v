Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RVIC4.Layer.
Require Import PendingCheckAux.Code.check_timer_became_asserted.

Require Import PendingCheckAux.LowSpecs.check_timer_became_asserted.

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
    _get_timer_asserted ↦ gensem get_timer_asserted_spec
      ⊕ _timer_is_masked ↦ gensem timer_is_masked_spec
      ⊕ _set_timer_masked ↦ gensem set_timer_masked_spec
      ⊕ _get_timer_masked ↦ gensem get_timer_masked_spec
      ⊕ _timer_condition_met ↦ gensem timer_condition_met_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_get_timer_asserted: block.
    Hypothesis h_get_timer_asserted_s : Genv.find_symbol ge _get_timer_asserted = Some b_get_timer_asserted.
    Hypothesis h_get_timer_asserted_p : Genv.find_funct_ptr ge b_get_timer_asserted
                                        = Some (External (EF_external _get_timer_asserted
                                                         (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                               (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque get_timer_asserted_spec.

    Variable b_timer_is_masked: block.
    Hypothesis h_timer_is_masked_s : Genv.find_symbol ge _timer_is_masked = Some b_timer_is_masked.
    Hypothesis h_timer_is_masked_p : Genv.find_funct_ptr ge b_timer_is_masked
                                     = Some (External (EF_external _timer_is_masked
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
    Local Opaque timer_is_masked_spec.

    Variable b_set_timer_masked: block.
    Hypothesis h_set_timer_masked_s : Genv.find_symbol ge _set_timer_masked = Some b_set_timer_masked.
    Hypothesis h_set_timer_masked_p : Genv.find_funct_ptr ge b_set_timer_masked
                                      = Some (External (EF_external _set_timer_masked
                                                       (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                             (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque set_timer_masked_spec.

    Variable b_get_timer_masked: block.
    Hypothesis h_get_timer_masked_s : Genv.find_symbol ge _get_timer_masked = Some b_get_timer_masked.
    Hypothesis h_get_timer_masked_p : Genv.find_funct_ptr ge b_get_timer_masked
                                      = Some (External (EF_external _get_timer_masked
                                                       (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                             (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque get_timer_masked_spec.

    Variable b_timer_condition_met: block.
    Hypothesis h_timer_condition_met_s : Genv.find_symbol ge _timer_condition_met = Some b_timer_condition_met.
    Hypothesis h_timer_condition_met_p : Genv.find_funct_ptr ge b_timer_condition_met
                                         = Some (External (EF_external _timer_condition_met
                                                          (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                                (Tcons tulong Tnil) tuint cc_default).
    Local Opaque timer_condition_met_spec.

    Lemma check_timer_became_asserted_body_correct:
      forall m d d' env le timer_base timer_offset cntx_ctl res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTtimer: PTree.get _timer le = Some (Vptr timer_base (Int.repr timer_offset)))
             (HPTcntx_ctl: PTree.get _cntx_ctl le = Some (Vlong cntx_ctl))
             (Hspec: check_timer_became_asserted_spec0 (timer_base, timer_offset) (VZ64 (Int64.unsigned cntx_ctl)) d = Some (d',Int.unsigned res)),
           exists le', (exec_stmt ge env le ((m, d): mem) check_timer_became_asserted_body E0 le' (m, d') (Out_return (Some (Vint res, tuint)))).
    Proof.
      solve_code_proof Hspec check_timer_became_asserted_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
