Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RealmSyncHandler.Spec.
Require Import RealmExitHandlerAux.Specs.handle_exception_sync.
Require Import RealmExitHandlerAux.LowSpecs.handle_exception_sync.
Require Import RealmExitHandlerAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       sysreg_read_spec
       set_rec_run_esr_spec
       set_rec_last_run_info_esr_spec
       set_rec_run_gprs_spec
       get_rec_regs_spec
       sysreg_write_spec
       handle_instruction_abort_spec
       set_rec_run_far_spec
       set_rec_run_hpfar_spec
    .

  Lemma handle_exception_sync_spec_exists:
    forall habd habd'  labd rec res
      (Hspec: handle_exception_sync_spec rec habd = Some (habd', res))
      (Hrel: relate_RData habd labd),
    exists labd', handle_exception_sync_spec0 rec labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque handle_sysreg_access_trap_spec handle_data_abort_spec handle_realm_rsi_spec.
    intros. destruct Hrel. destruct rec.
    unfold handle_exception_sync_spec, handle_exception_sync_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite; repeat simpl_update_reg;
        repeat (simpl_htarget; grewrite; simpl in * );
        try solve [eexists; split; [reflexivity|constructor; reflexivity]].
    - extract_if. reflexivity. grewrite.
      solve_bool_range; grewrite.
      eexists; split; [reflexivity|constructor; reflexivity].
    - destruct regs_is_int64_dec in C6; [|inversion C6].
      extract_if. reflexivity. grewrite.
      solve_bool_range; grewrite.
      autounfold in *. grewrite; simpl. grewrite.
      solve_peq. simpl.
      rewrite ZMap.gss. simpl. grewrite. simpl.
      unfold ref_accessible in *. grewrite.
      repeat(simpl; grewrite; try rewrite ZMap.gss; simpl; grewrite;
             simpl; rewrite e; extract_if; try reflexivity; grewrite; extract_if; try reflexivity; grewrite;
             repeat (repeat simpl_field; repeat swap_fields; try rewrite ZMap.gss;
                     try rewrite ZMap.set2; simpl)).
      simpl; grewrite; try rewrite ZMap.gss; simpl; grewrite. simpl. rewrite e.
      extract_if; try reflexivity; grewrite.
      eexists; split; [reflexivity|constructor; reflexivity]. inv C.
    - simpl_update_reg. solve_bool_range. grewrite. solve_bool_range. grewrite.
      eexists; split; [reflexivity|constructor; reflexivity].
    - solve_bool_range. grewrite.
      eexists; split; [reflexivity|constructor; reflexivity].
  Qed.

End Refine.

