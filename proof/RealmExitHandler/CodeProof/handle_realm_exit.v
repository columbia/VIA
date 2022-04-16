Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmExitHandlerAux.Spec.
Require Import RealmExitHandlerAux.Layer.
Require Import RealmExitHandler.Code.handle_realm_exit.

Require Import RealmExitHandler.LowSpecs.handle_realm_exit.

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
    _set_rec_run_exit_reason ↦ gensem set_rec_run_exit_reason_spec
      ⊕ _handle_exception_sync ↦ gensem handle_exception_sync_spec
      ⊕ _handle_excpetion_irq_lel ↦ gensem handle_excpetion_irq_lel_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_set_rec_run_exit_reason: block.
    Hypothesis h_set_rec_run_exit_reason_s : Genv.find_symbol ge _set_rec_run_exit_reason = Some b_set_rec_run_exit_reason.
    Hypothesis h_set_rec_run_exit_reason_p : Genv.find_funct_ptr ge b_set_rec_run_exit_reason
                                             = Some (External (EF_external _set_rec_run_exit_reason
                                                              (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                                    (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_rec_run_exit_reason_spec.

    Variable b_handle_exception_sync: block.
    Hypothesis h_handle_exception_sync_s : Genv.find_symbol ge _handle_exception_sync = Some b_handle_exception_sync.
    Hypothesis h_handle_exception_sync_p : Genv.find_funct_ptr ge b_handle_exception_sync
                                           = Some (External (EF_external _handle_exception_sync
                                                            (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                                  (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque handle_exception_sync_spec.

    Variable b_handle_excpetion_irq_lel: block.
    Hypothesis h_handle_excpetion_irq_lel_s : Genv.find_symbol ge _handle_excpetion_irq_lel = Some b_handle_excpetion_irq_lel.
    Hypothesis h_handle_excpetion_irq_lel_p : Genv.find_funct_ptr ge b_handle_excpetion_irq_lel
                                              = Some (External (EF_external _handle_excpetion_irq_lel
                                                               (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                                     (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque handle_excpetion_irq_lel_spec.

    Lemma handle_realm_exit_body_correct:
      forall m d d' env le rec_base rec_offset exception res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTexception: PTree.get _exception le = Some (Vint exception))
             (Hspec: handle_realm_exit_spec0 (rec_base, rec_offset) (Int.unsigned exception) d = Some (d',Int.unsigned res)),
           exists le', (exec_stmt ge env le ((m, d): mem) handle_realm_exit_body E0 le' (m, d') (Out_return (Some (Vint res, tuint)))).
    Proof.
      solve_code_proof Hspec handle_realm_exit_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
