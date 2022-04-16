Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RVIC2.Spec.
Require Import RVIC3.Specs.rvic_clear_masked.
Require Import RVIC3.LowSpecs.rvic_clear_masked.
Require Import RVIC3.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       get_rvic_mask_bits_spec
       rvic_clear_flag_spec
    .

  Lemma rvic_clear_masked_spec_exists:
    forall habd habd'  labd rvic intid
      (Hspec: rvic_clear_masked_spec rvic intid habd = Some habd')
      (Hrel: relate_RData habd labd),
    exists labd', rvic_clear_masked_spec0 rvic intid labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    intros. inv Hrel. destruct rvic.
    unfold rvic_clear_masked_spec, rvic_clear_masked_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; simpl in * );
        repeat (solve_bool_range; grewrite); try solve_peq;
        (eexists; split; [reflexivity|constructor;reflexivity]).
  Qed.

End Refine.

