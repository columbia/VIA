Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import PSCIAux.Spec.
Require Import PSCIAux2.Specs.psci_cpu_on_target.
Require Import PSCIAux2.LowSpecs.psci_cpu_on_target.
Require Import PSCIAux2.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       get_rec_runnable_spec
       buffer_unmap_spec
       granule_unlock_spec
       set_psci_result_x0_spec
       psci_reset_rec_spec
       set_rec_pc_spec
       set_rec_runnable_spec
       set_psci_result_forward_psci_call_spec
       set_psci_result_forward_x1_spec
    .

  Lemma psci_cpu_on_target_spec_exists:
    forall habd habd'  labd g_target_rec target_rec rec entry_point_address target_cpu
           (Hspec: psci_cpu_on_target_spec g_target_rec target_rec rec entry_point_address target_cpu habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', psci_cpu_on_target_spec0 g_target_rec target_rec rec entry_point_address target_cpu labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. destruct g_target_rec, target_rec, rec.
    unfold psci_cpu_on_target_spec, psci_cpu_on_target_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; simpl in * ).
    unfold ref_accessible in *; simpl.
    repeat (simpl_htarget; srewrite; simpl in * ).
    eexists; split. reflexivity. constructor; simpl.
    repeat simpl_update_reg.
    repeat (repeat simpl_field; repeat swap_fields).
    rewrite <- C12. reflexivity.
    eexists; split. reflexivity. constructor. rewrite <- C12. reflexivity.
  Qed.

End Refine.

