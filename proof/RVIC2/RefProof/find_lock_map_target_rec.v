Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import PSCIAux.Spec.
Require Import RVIC2.Specs.find_lock_map_target_rec.
Require Import RVIC2.LowSpecs.find_lock_map_target_rec.
Require Import RVIC2.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       mpidr_to_rec_idx_spec
       get_rec_rec_idx_spec
       get_rec_g_rec_spec
       granule_lock_spec
       granule_map_spec
       set_target_rec_spec
       get_rec_g_rd_spec
       get_rec_g_rec_list_spec
       find_lock_rec_spec
       buffer_unmap_spec
       is_null_spec
       null_ptr_spec
    .

  Lemma find_lock_map_target_rec_spec_exists:
    forall habd habd'  labd rec target
           (Hspec: find_lock_map_target_rec_spec rec target habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', find_lock_map_target_rec_spec0 rec target labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. inv Hrel. destruct rec.
    unfold find_lock_map_target_rec_spec, find_lock_map_target_rec_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; simpl in *; srewrite; repeat grewrite; simpl; bool_rel;
        repeat (simpl_htarget; srewrite; simpl in * );
        repeat (solve_bool_range; grewrite); try solve_peq;
          try solve[eexists; split; [reflexivity|constructor;reflexivity]].
    ptr_ne 3%positive 3%positive. inversion e1. contra.
    repeat (simpl_htarget; grewrite; simpl in * ).
    eexists; split. reflexivity. constructor. reflexivity.
  Qed.

End Refine.

