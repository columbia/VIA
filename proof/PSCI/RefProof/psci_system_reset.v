Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import PSCIAux2.Spec.
Require Import AbsAccessor.Spec.
Require Import PSCI.Specs.psci_system_reset.
Require Import PSCI.LowSpecs.psci_system_reset.
Require Import PSCI.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       set_psci_result_forward_psci_call_spec
  .

  Lemma psci_system_reset_spec_exists:
    forall habd habd'  labd rec
      (Hspec: psci_system_reset_spec rec habd = Some habd')
      (Hrel: relate_RData habd labd),
    exists labd', psci_system_reset_spec0 rec labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    intros. inv Hrel. destruct rec.
    unfold psci_system_reset_spec, psci_system_reset_spec0 in *.
    autounfold in *. hsimpl_hyp Hspec; inv Hspec.
    eexists; split. reflexivity. constructor. reflexivity.
  Qed.

End Refine.

