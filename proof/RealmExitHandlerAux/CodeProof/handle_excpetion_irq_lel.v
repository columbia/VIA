Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmSyncHandler.Layer.
Require Import RealmExitHandlerAux.Code.handle_excpetion_irq_lel.

Require Import RealmExitHandlerAux.LowSpecs.handle_excpetion_irq_lel.

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
    _sysreg_read ↦ gensem sysreg_read_spec
      ⊕ _set_rec_run_exit_reason ↦ gensem set_rec_run_exit_reason_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_sysreg_read: block.
    Hypothesis h_sysreg_read_s : Genv.find_symbol ge _sysreg_read = Some b_sysreg_read.
    Hypothesis h_sysreg_read_p : Genv.find_funct_ptr ge b_sysreg_read
                                 = Some (External (EF_external _sysreg_read
                                                  (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                        (Tcons tuint Tnil) tulong cc_default).
    Local Opaque sysreg_read_spec.

    Variable b_set_rec_run_exit_reason: block.
    Hypothesis h_set_rec_run_exit_reason_s : Genv.find_symbol ge _set_rec_run_exit_reason = Some b_set_rec_run_exit_reason.
    Hypothesis h_set_rec_run_exit_reason_p : Genv.find_funct_ptr ge b_set_rec_run_exit_reason
                                             = Some (External (EF_external _set_rec_run_exit_reason
                                                              (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                                    (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_rec_run_exit_reason_spec.

    Lemma handle_excpetion_irq_lel_body_correct:
      forall m d d' env le rec_base rec_offset res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (Hspec: handle_excpetion_irq_lel_spec0 (rec_base, rec_offset) d = Some (d',Int.unsigned res)),
           exists le', (exec_stmt ge env le ((m, d): mem) handle_excpetion_irq_lel_body E0 le' (m, d') (Out_return (Some (Vint res, tuint)))).
    Proof.
      solve_code_proof Hspec handle_excpetion_irq_lel_body; eexists; solve_proof_low. rewrite <- H1.
      solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
