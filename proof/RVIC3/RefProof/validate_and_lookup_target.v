Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import RVIC2.Spec.
Require Import RVIC.Spec.
Require Import AbsAccessor.Spec.
Require Import RVIC3.Specs.validate_and_lookup_target.
Require Import RVIC3.LowSpecs.validate_and_lookup_target.
Require Import RVIC3.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       rvic_target_is_valid_spec
       is_untrusted_intid_spec
       is_trusted_intid_spec
       find_lock_map_target_rec_spec
       get_target_rec_spec
       is_null_spec
    .

  Lemma validate_and_lookup_target_spec_exists:
    forall habd habd'  labd rec target intid res
           (Hspec: validate_and_lookup_target_spec rec target intid habd = Some (habd', res))
            (Hrel: relate_RData habd labd),
    exists labd', validate_and_lookup_target_spec0 rec target intid labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. inv Hrel. destruct rec.
    unfold validate_and_lookup_target_spec, validate_and_lookup_target_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; simpl in *; srewrite;
        repeat (solve_bool_range; grewrite; try solve_ptr_eq; simpl);
        try (destruct_dis; repeat (solve_bool_range; grewrite; try solve_ptr_eq; simpl));
        (eexists; split; [reflexivity|constructor;reflexivity]).
  Qed.

End Refine.

