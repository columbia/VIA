Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import PSCI.Specs.psci_cpu_suspend.
Require Import PSCI.LowSpecs.psci_cpu_suspend.
Require Import PSCI.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       set_psci_result_forward_psci_call_spec
       set_psci_result_x0_spec
    .

  Lemma psci_cpu_suspend_spec_exists:
    forall habd habd'  labd rec entry_point_address context_id
           (Hspec: psci_cpu_suspend_spec rec entry_point_address context_id habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', psci_cpu_suspend_spec0 rec entry_point_address context_id labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    intros. inv Hrel. destruct rec.
    unfold psci_cpu_suspend_spec, psci_cpu_suspend_spec0 in *.
    destruct entry_point_address, context_id.
    eexists; split. reflexivity. constructor. inv Hspec. reflexivity.
  Qed.

End Refine.

