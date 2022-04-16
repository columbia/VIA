Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import PendingCheckAux.Spec.
Require Import RVIC4.Spec.
Require Import PendingCheck.Specs.check_pending_vtimers.
Require Import PendingCheck.LowSpecs.check_pending_vtimers.
Require Import PendingCheck.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       get_rec_g_rec_spec
       sysreg_read_spec
       check_timer_became_asserted_spec
       get_rec_vtimer_spec
       granule_lock_spec
       sysreg_write_spec
       get_rec_sysregs_spec
       set_rec_sysregs_spec
       set_rec_vtimer_asserted_spec
       rvic_set_pending_spec
       get_rec_rvic_spec
       granule_unlock_spec
    .

  Lemma check_pending_vtimers_spec_exists:
    forall habd habd'  labd rec
           (Hspec: check_pending_vtimers_spec rec habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', check_pending_vtimers_spec0 rec labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. inv id_rdata. destruct rec.
    unfold check_pending_vtimers_spec, check_pending_vtimers_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite; repeat simpl_update_reg;
        repeat (simpl_htarget; grewrite; simpl in * );
        try solve[repeat (solve_bool_range; grewrite); eexists; split; [reflexivity|constructor; reflexivity]].
    - solve_bool_range; grewrite. solve_bool_range; grewrite. solve_peq. simpl.
      repeat (simpl_htarget; grewrite; simpl in * ).
      extract_if. apply andb_true_iff; split; bool_rel. somega. apply or_le_64; somega. grewrite.
      unfold ref_accessible in *. simpl. srewrite.
      simpl_hyp C15; contra. grewrite.
      repeat (grewrite; simpl_htarget; repeat simpl_update_reg; repeat simpl_field; simpl).
      assert(0 <= 27 / 64 < 512) by (replace (27 / 64) with 0 by reflexivity; omega).
      extract_if. apply andb_true_iff; split; bool_rel. somega. apply or_le_64; somega. grewrite.
      repeat (solve_bool_range; grewrite). simpl_htarget.
      repeat swap_fields; repeat simpl_field.
      eexists; split; [reflexivity|constructor; try reflexivity].
      rewrite C13, <- C14, <- Prop0; repeat simpl_field. reflexivity.
    - solve_bool_range; grewrite. solve_bool_range; grewrite. solve_peq. simpl.
      eexists; split; [reflexivity|constructor; try reflexivity].
    - solve_bool_range; grewrite. solve_bool_range; grewrite. solve_peq. simpl.
      eexists; split; [reflexivity|constructor; try reflexivity].
  Qed.

End Refine.

