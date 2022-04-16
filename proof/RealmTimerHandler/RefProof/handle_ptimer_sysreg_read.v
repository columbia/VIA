Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RealmTimerHandler.Specs.handle_ptimer_sysreg_read.
Require Import RealmTimerHandler.LowSpecs.handle_ptimer_sysreg_read.
Require Import RealmTimerHandler.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       ESR_EL2_SYSREG_ISS_RT_spec
       sysreg_read_spec
       set_rec_regs_spec
       emulate_timer_ctl_read_spec
       get_rec_ptimer_spec
    .

  Lemma handle_ptimer_sysreg_read_spec_exists:
    forall habd habd'  labd rec esr
      (Hspec: handle_ptimer_sysreg_read_spec rec esr habd = Some habd')
      (Hrel: relate_RData habd labd),
    exists labd', handle_ptimer_sysreg_read_spec0 rec esr labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. destruct rec.
    unfold handle_ptimer_sysreg_read_spec, handle_ptimer_sysreg_read_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite; repeat simpl_update_reg;
        repeat (simpl_htarget; grewrite; simpl in * );
        try solve[repeat (solve_bool_range; grewrite); eexists; split; [reflexivity|constructor; reflexivity]].
    destruct_if. extract_if. apply andb_true_iff; split; bool_rel. somega. apply or_le_64; somega. grewrite.
    eexists; split; [reflexivity|constructor; reflexivity].
    solve_bool_range; grewrite; eexists; split; [reflexivity|constructor; reflexivity].
  Qed.

End Refine.

