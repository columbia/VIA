Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RealmExitHandlerAux.Spec.
Require Import RealmExitHandler.Specs.handle_realm_exit.
Require Import RealmSyncHandler.Spec.
Require Import RealmExitHandler.LowSpecs.handle_realm_exit.
Require Import RealmExitHandler.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       set_rec_run_exit_reason_spec
       handle_exception_sync_spec
       handle_excpetion_irq_lel_spec
    .

  Lemma handle_realm_exit_spec_exists:
    forall habd habd'  labd rec exception res
           (Hspec: handle_realm_exit_spec rec exception habd = Some (habd', res))
            (Hrel: relate_RData habd labd),
    exists labd', handle_realm_exit_spec0 rec exception labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque handle_sysreg_access_trap_spec handle_data_abort_spec handle_realm_rsi_spec.
    intros. destruct Hrel. destruct rec.
    unfold handle_realm_exit_spec, handle_realm_exit_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite; repeat simpl_update_reg;
        repeat (simpl_htarget; grewrite; simpl in * );
        try solve [eexists; split; [reflexivity|constructor; reflexivity]].
  Qed.

End Refine.

