Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RealmSyncHandlerAux.Spec.
Require Import RealmSyncHandler.Specs.handle_data_abort.
Require Import RealmSyncHandler.LowSpecs.handle_data_abort.
Require Import RealmSyncHandler.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       sysreg_read_spec
       access_in_par_spec
       set_rec_last_run_info_esr_spec
       esr_is_write_spec
       get_write_value_spec
       set_rec_run_esr_spec
       set_rec_run_far_spec
       set_rec_run_hpfar_spec
       set_rec_run_emulated_write_val_spec
    .

  Lemma handle_data_abort_spec_exists:
    forall habd habd'  labd rec esr
      (Hspec: handle_data_abort_spec rec esr habd = Some habd')
      (Hrel: relate_RData habd labd),
    exists labd', handle_data_abort_spec0 rec esr labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. destruct rec.
    unfold handle_data_abort_spec, handle_data_abort_spec0 in *.
    repeat autounfold in *. simpl in *.
    rewrite get_reg_85, get_reg_94.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec; repeat destruct_con;
      destruct (Z.land (r_spsr_el2 (cpu_regs (priv labd))) 16 =? 0);
      repeat destruct_dis; try match goal with
                               | [H: negb ?a = true |- _] => apply negb_true_iff in H
                               | [H: negb ?a = false |- _] => apply negb_false_iff in H
                               end; simpl;
        repeat (repeat grewrite; simpl; try solve_bool_range);
        try solve[eexists; split; [reflexivity|constructor; reflexivity]].
    - unfold ref_accessible in *.
      destruct (__esr_is_write z0);
        repeat (repeat grewrite; simpl; try solve_bool_range; try rewrite ZMap.gss; repeat simpl_update_reg).
      destruct (__esr_srt z0 =? 31); simpl.
      eexists; split. reflexivity. constructor; simpl. reflexivity.
      solve_bool_range. grewrite.
      eexists; split. reflexivity. constructor; simpl. reflexivity.
      assumption. assumption.
      eexists; split. reflexivity. constructor; simpl. reflexivity.
    - unfold ref_accessible in *.
      destruct (__esr_is_write (Z.land z0 18446744073692774399));
        repeat (repeat grewrite; simpl; try solve_bool_range; try rewrite ZMap.gss; repeat simpl_update_reg).
      destruct (__esr_srt  (Z.land z0 18446744073692774399) =? 31); simpl.
      eexists; split. reflexivity. constructor; simpl. reflexivity.
      solve_bool_range. grewrite.
      eexists; split. reflexivity. constructor; simpl. reflexivity.
      assumption. assumption.
      eexists; split. reflexivity. constructor; simpl. reflexivity.
  Qed.

End Refine.

