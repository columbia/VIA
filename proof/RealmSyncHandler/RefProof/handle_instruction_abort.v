Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RealmSyncHandler.Specs.handle_instruction_abort.
Require Import RealmSyncHandler.LowSpecs.handle_instruction_abort.
Require Import RealmSyncHandler.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       sysreg_read_spec
       shiftl_spec
       is_addr_in_par_rec_spec
       is_addr_in_par_spec
       set_rec_run_hpfar_spec
       set_rec_run_esr_spec
    .

  Lemma handle_instruction_abort_spec_exists:
    forall habd habd'  labd rec esr res
      (Hspec: handle_instruction_abort_spec rec esr habd = Some (habd', res))
      (Hrel: relate_RData habd labd),
    exists labd', handle_instruction_abort_spec0 rec esr labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. destruct rec.
    unfold handle_instruction_abort_spec, handle_instruction_abort_spec0 in *.
    repeat autounfold in *. simpl in *.
    replace (Z.lor 4227858432 63) with 4227858495 by reflexivity.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite; repeat simpl_update_reg;
        repeat (simpl_htarget; grewrite; simpl in * );
        repeat (solve_bool_range; grewrite);
        try solve[eexists; split; [reflexivity|constructor; reflexivity]].
    eexists; split. reflexivity. constructor. repeat (repeat simpl_field; repeat swap_fields). rewrite zmap_comm. reflexivity.
    red; intro T; inv T.
  Qed.

End Refine.

