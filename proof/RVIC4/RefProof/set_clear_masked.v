Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import RVIC3.Spec.
Require Import AbsAccessor.Spec.
Require Import RVIC2.Spec.
Require Import RVIC4.Specs.set_clear_masked.
Require Import RVIC4.LowSpecs.set_clear_masked.
Require Import RVIC4.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       get_target_rec_spec
       set_rvic_result_x0_spec
       get_rec_rvic_spec
       rvic_set_masked_spec
       rvic_is_masked_spec
       need_ns_notify_spec
       set_rvic_result_ns_notify_spec
       set_rvic_result_target_spec
       rvic_clear_masked_spec
       get_rec_g_rec_spec
       buffer_unmap_spec
       granule_unlock_spec
    .

  Lemma set_clear_masked_spec_exists:
    forall habd habd'  labd rec target intid masked
      (Hspec: set_clear_masked_spec rec target intid masked habd = Some habd')
      (Hrel: relate_RData habd labd),
    exists labd', set_clear_masked_spec0 rec target intid masked labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq validate_and_lookup_target_spec.
    intros. inv Hrel. destruct rec.
    unfold set_clear_masked_spec, set_clear_masked_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con.
    - simpl in *; srewrite. bool_rel. repeat (simpl_htarget; srewrite; simpl in * ).
      repeat (solve_bool_range; grewrite).
      eexists; split. reflexivity. constructor. rewrite <- C16.
      repeat (repeat simpl_field; repeat swap_fields). reflexivity.
    - simpl in *; srewrite. bool_rel. grewrite. simpl. srewrite.
      repeat (solve_peq; simpl);
        repeat (
            match goal with
            | H:?P |- context [prop_dec ?P] =>
              let tmp := fresh "He" in
              destruct (prop_dec P) as [tmp| tmp]; [ simpl; clear tmp | apply tmp in H; inversion H ]
            | |- context [prop_dec (?a = ?a)] => destruct (prop_dec (a = a)); [ simpl | contra ]
            end; grewrite; simpl).
      repeat (destruct_if; repeat (simpl_htarget; grewrite; simpl); repeat (solve_bool_range; grewrite));
        try solve[eexists; split; [reflexivity|constructor; rewrite <- C16; reflexivity]].
    - eexists; split; [reflexivity|constructor; reflexivity].
  Qed.

End Refine.

