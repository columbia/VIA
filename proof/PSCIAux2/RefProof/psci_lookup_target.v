Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import PSCIAux.Spec.
Require Import PSCIAux2.Specs.psci_lookup_target.
Require Import PSCIAux2.LowSpecs.psci_lookup_target.
Require Import PSCIAux2.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       mpidr_is_valid_spec
       null_ptr_spec
       get_rec_g_rd_spec
       get_rec_g_rec_spec
       get_rec_g_rec_list_spec
       granule_map_spec
       find_lock_rec_spec
       mpidr_to_rec_idx_spec
       buffer_unmap_spec
    .

  Lemma psci_lookup_target_spec_exists:
    forall habd habd'  labd rec target res
           (Hspec: psci_lookup_target_spec rec target habd = Some (habd', res))
            (Hrel: relate_RData habd labd),
    exists labd', psci_lookup_target_spec0 rec target labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. destruct rec, target.
    unfold psci_lookup_target_spec, psci_lookup_target_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; simpl in * );
        repeat (solve_bool_range; grewrite);
        try solve [eexists; split; [reflexivity|
                          constructor; repeat (repeat simpl_field; repeat swap_fields);
                          reflexivity]].
    ptr_ne 3%positive 3%positive. inversion e1. srewrite; contra. simpl.
    eexists; split; [reflexivity| constructor; simpl; repeat (repeat simpl_field; repeat swap_fields)].
    rewrite ZMap.set2. rewrite <- Prop1. rewrite zmap_set_id. simpl_field. reflexivity.
  Qed.

End Refine.

