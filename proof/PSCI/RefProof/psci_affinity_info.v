Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import PSCIAux2.Spec.
Require Import PSCI.Specs.psci_affinity_info.
Require Import PSCI.LowSpecs.psci_affinity_info.
Require Import PSCI.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       set_psci_result_x0_spec
       is_null_spec
       granule_map_spec
       get_rec_runnable_spec
       buffer_unmap_spec
       granule_unlock_spec
    .

  Lemma psci_affinity_info_spec_exists:
    forall habd habd'  labd rec target_affinity lowest_affinity_level
           (Hspec: psci_affinity_info_spec rec target_affinity lowest_affinity_level habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', psci_affinity_info_spec0 rec target_affinity lowest_affinity_level labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque psci_lookup_target_spec ptr_eq.
    intros. destruct rec. inv Hrel.
    unfold psci_affinity_info_spec, psci_affinity_info_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; simpl in * );
        repeat (repeat simpl_field; repeat swap_fields); try rewrite <- C14;
        try solve[eexists; split; [reflexivity|constructor; reflexivity]].
  Qed.

End Refine.

