Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import PSCI.Specs.psci_version.
Require Import PSCI.LowSpecs.psci_version.
Require Import PSCI.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       set_psci_result_x0_spec
  .

  Lemma psci_version_spec_exists:
    forall habd habd'  labd rec
      (Hspec: psci_version_spec rec habd = Some habd')
      (Hrel: relate_RData habd labd),
    exists labd', psci_version_spec0 rec labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    intros. inv Hrel. destruct rec.
    unfold psci_version_spec, psci_version_spec0 in *. inv Hspec.
    eexists; split. reflexivity. constructor. reflexivity.
  Qed.

End Refine.

