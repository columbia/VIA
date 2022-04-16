Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RealmTimerHandler.Spec.
Require Import RealmSyncHandlerAux.Specs.handle_timer_sysreg_trap.
Require Import RealmSyncHandlerAux.LowSpecs.handle_timer_sysreg_trap.
Require Import RealmSyncHandlerAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       ESR_EL2_SYSREG_IS_WRITE_spec
       sysreg_write_spec
       sysreg_read_spec
    .

  Lemma handle_timer_sysreg_trap_spec_exists:
    forall habd habd'  labd rec esr
      (Hspec: handle_timer_sysreg_trap_spec rec esr habd = Some habd')
      (Hrel: relate_RData habd labd),
    exists labd', handle_timer_sysreg_trap_spec0 rec esr labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque
          handle_vtimer_sysreg_write_spec
          handle_ptimer_sysreg_write_spec
          handle_vtimer_sysreg_read_spec
          handle_ptimer_sysreg_read_spec.
    intros. destruct Hrel. destruct rec.
    unfold handle_timer_sysreg_trap_spec, handle_timer_sysreg_trap_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat (repeat destruct_con; repeat destruct_dis); simpl in *; srewrite; repeat simpl_update_reg;
        repeat (simpl_htarget; grewrite; simpl in *; try solve_bool_range);
        try solve[eexists; split; [reflexivity|constructor; reflexivity]].
  Qed.

End Refine.

