Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RVIC.Spec.
Require Import RVIC2.Specs.rvic_is_masked.
Require Import RVIC2.LowSpecs.rvic_is_masked.
Require Import RVIC2.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       get_rvic_mask_bits_spec
       rvic_test_flag_spec
    .

  Lemma rvic_is_masked_spec_exists:
    forall habd  labd rvic intid res
           (Hspec: rvic_is_masked_spec rvic intid habd = Some res)
            (Hrel: relate_RData habd labd),
    rvic_is_masked_spec0 rvic intid labd = Some res.
  Proof.
    intros. inv Hrel. destruct rvic.
    unfold rvic_is_masked_spec, rvic_is_masked_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; simpl in * ).
    - solve_bool_range. grewrite. solve_peq. reflexivity.
    - solve_bool_range. grewrite. solve_peq. reflexivity.
  Qed.

End Refine.

