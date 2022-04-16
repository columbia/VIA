Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import PendingCheckAux.Specs.check_timer_became_asserted.
Require Import PendingCheckAux.LowSpecs.check_timer_became_asserted.
Require Import PendingCheckAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       get_timer_asserted_spec
       timer_is_masked_spec
       set_timer_masked_spec
       get_timer_masked_spec
       timer_condition_met_spec
    .

  Lemma check_timer_became_asserted_spec_exists:
    forall habd habd'  labd timer cntx_ctl res
           (Hspec: check_timer_became_asserted_spec timer cntx_ctl habd = Some (habd', res))
            (Hrel: relate_RData habd labd),
    exists labd', check_timer_became_asserted_spec0 timer cntx_ctl labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    intros. inv Hrel. destruct timer.
    unfold check_timer_became_asserted_spec, check_timer_became_asserted_spec0 in *.
    repeat autounfold in *; unfold ref_accessible in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite; try destruct_if;
        repeat (simpl_htarget; grewrite; simpl in * );
        (eexists; split; [reflexivity| constructor; reflexivity]).
  Qed.

End Refine.

