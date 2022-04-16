Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import PSCIAux2.Spec.
Require Import PSCI.Specs.psci_cpu_on.
Require Import PSCI.LowSpecs.psci_cpu_on.
Require Import PSCI.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       get_rec_par_base_spec
       get_rec_par_end_spec
       set_psci_result_x0_spec
       mpidr_to_rec_idx_spec
       get_rec_rec_idx_spec
       is_null_spec
       granule_map_spec
       psci_cpu_on_target_spec
    .

  Lemma psci_lookup_target_priv:
    forall rec target adt adt' p (Hspec: psci_lookup_target_spec rec target adt = Some (adt', p)),
      priv adt' = priv adt.
  Proof.
    intros. hsimpl_func Hspec; simpl_query_oracle; try reflexivity.
  Qed.

  Lemma psci_cpu_on_spec_exists:
    forall habd habd'  labd rec target_cpu entry_point_address context_id
           (Hspec: psci_cpu_on_spec rec target_cpu entry_point_address context_id habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', psci_cpu_on_spec0 rec target_cpu entry_point_address context_id labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque psci_lookup_target_spec ptr_eq.
    intros. destruct rec. inv Hrel.
    unfold psci_cpu_on_spec, psci_cpu_on_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; repeat destruct_dis; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; simpl in * );
        repeat (repeat simpl_field; repeat swap_fields);
        try solve[eexists; split; [reflexivity|constructor; reflexivity]].
    - extract_if. bool_rel. omega. grewrite. extract_if. bool_rel. omega. grewrite.
      eexists; split; [reflexivity|constructor; reflexivity].
    - extract_if. bool_rel. omega. grewrite. extract_if. bool_rel. omega. grewrite.
      inversion e. simpl.
      eexists; split; [reflexivity|constructor; reflexivity].
    - extract_if. bool_rel. omega. grewrite. extract_if. bool_rel. omega. grewrite.
      bool_rel. subst. rewrite ZMap.gso; try omega.
      rewrite (psci_lookup_target_priv _ _ _ _ _ C18).
      repeat (simpl_htarget; grewrite; simpl in * ).
      repeat (repeat simpl_field; repeat swap_fields).
      repeat simpl_update_reg. rewrite <- Prop2.
      solve_bool_range; grewrite. red in Prop1; simpl_htarget.
      eexists; split; [reflexivity|constructor; reflexivity]. discriminate.
    - extract_if. bool_rel. omega. grewrite. extract_if. bool_rel. omega. grewrite.
      bool_rel. subst. rewrite ZMap.gso; try omega.
      rewrite (psci_lookup_target_priv _ _ _ _ _ C18).
      repeat (simpl_htarget; grewrite; simpl in * ).
      repeat (repeat simpl_field; repeat swap_fields).
      solve_bool_range; grewrite. red in Prop1; simpl_htarget.
      eexists; split; [reflexivity|constructor; reflexivity]. discriminate.
  Qed.

End Refine.
