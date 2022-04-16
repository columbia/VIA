Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import PSCI.Specs.psci_features.
Require Import PSCI.LowSpecs.psci_features.
Require Import PSCI.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       set_psci_result_x0_spec
  .

  Lemma psci_features_spec_exists:
    forall habd habd'  labd rec psci_func_id
           (Hspec: psci_features_spec rec psci_func_id habd = Some habd')
           (Hrel: relate_RData habd labd),
    exists labd', psci_features_spec0 rec psci_func_id labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    intros. inv Hrel. destruct rec.
    unfold psci_features_spec, psci_features_spec0 in *.
    autounfold in *; simpl in *.
    hsimpl_hyp Hspec; inv Hspec; repeat destruct_con.
    repeat (destruct_dis; try solve[bool_rel; grewrite; simpl; eexists; split; [reflexivity|constructor;reflexivity]]).
    grewrite. eexists; split; [reflexivity|constructor;reflexivity].
  Qed.

End Refine.

