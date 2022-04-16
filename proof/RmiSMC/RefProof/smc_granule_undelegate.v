Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RmiOps.Spec.
Require Import RmiSMC.Specs.smc_granule_undelegate.
Require Import RmiSMC.LowSpecs.smc_granule_undelegate.
Require Import RmiSMC.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       find_lock_granule_spec
       is_null_spec
       granule_undelegate_ops_spec
    .

  Lemma smc_granule_undelegate_spec_exists:
    forall habd habd'  labd addr res
           (Hspec: smc_granule_undelegate_spec addr habd = Some (habd', res))
            (Hrel: relate_RData habd labd),
    exists labd', smc_granule_undelegate_spec0 addr labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. inv id_rdata. duplicate valid_o. destruct D.
    unfold smc_granule_undelegate_spec, smc_granule_undelegate_spec0 in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; simpl in * ).
    - solve_ptr_eq; simpl. simpl_ACQ.
      repeat (simpl_htarget; try grewrite; repeat swap_fields; repeat simpl_field; simpl in * ).
      eexists; split. reflexivity. constructor; simpl; try assumption. rewrite <- Prop3. simpl_field. reflexivity.
    - eexists; split. reflexivity. constructor; simpl; try assumption. simpl_field. reflexivity.
    - destruct_dis; solve_ptr_eq; simpl;
        (eexists; split; [reflexivity|constructor; simpl; try assumption; reflexivity]).
  Qed.

End Refine.

