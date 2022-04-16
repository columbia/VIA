Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import PSCI.Specs.psci_cpu_off.
Require Import PSCI.LowSpecs.psci_cpu_off.
Require Import PSCI.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       set_psci_result_forward_psci_call_spec
       set_rec_runnable_spec
       set_psci_result_x0_spec
    .

  Lemma psci_cpu_off_spec_exists:
    forall habd habd'  labd rec
           (Hspec: psci_cpu_off_spec rec habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', psci_cpu_off_spec0 rec labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    intros. destruct rec. inv Hrel.
    unfold psci_cpu_off_spec, psci_cpu_off_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        try solve[eexists; split; [reflexivity|constructor; reflexivity]].
  Qed.

End Refine.

