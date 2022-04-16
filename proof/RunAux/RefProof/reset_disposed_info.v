Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RunAux.Specs.reset_disposed_info.
Require Import RunAux.LowSpecs.reset_disposed_info.
Require Import RunAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       set_rec_dispose_pending_spec
    .

  Lemma reset_disposed_info_spec_exists:
    forall habd habd'  labd rec
      (Hspec: reset_disposed_info_spec rec habd = Some habd')
      (Hrel: relate_RData habd labd),
    exists labd', reset_disposed_info_spec0 rec labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    intros. destruct Hrel. destruct rec.
    unfold reset_disposed_info_spec, reset_disposed_info_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite; repeat simpl_update_reg;
        repeat (simpl_htarget; grewrite; simpl in * );
        (eexists; split; [reflexivity|constructor;reflexivity]).
  Qed.

End Refine.

