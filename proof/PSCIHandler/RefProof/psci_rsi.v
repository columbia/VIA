Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import PSCI.Spec.
Require Import AbsAccessor.Spec.
Require Import PSCIHandler.Specs.psci_rsi.
Require Import PSCIHandler.LowSpecs.psci_rsi.
Require Import PSCIHandler.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       set_psci_result_x0_spec
       set_psci_result_forward_psci_call_spec
  .

  Lemma psci_rsi_spec_exists:
    forall habd habd'  labd rec function_id arg0 arg1 arg2
      (Hspec: psci_rsi_spec rec function_id arg0 arg1 arg2 habd = Some habd')
      (Hrel: relate_RData habd labd),
    exists labd', psci_rsi_spec0 rec function_id arg0 arg1 arg2 labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque
          psci_version_spec
          psci_cpu_suspend_spec
          psci_cpu_off_spec
          psci_cpu_on_spec
          psci_affinity_info_spec
          psci_system_off_spec
          psci_system_reset_spec
          psci_features_spec.
    intros. inv Hrel. destruct rec.
    unfold psci_rsi_spec, psci_rsi_spec0 in *.
    autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; repeat destruct_con; repeat destruct_dis; grewrite; simpl;
      repeat (extract_if; [bool_rel;omega|grewrite]);
      try solve[eexists; split; [reflexivity|constructor;reflexivity]].
  Qed.

End Refine.

