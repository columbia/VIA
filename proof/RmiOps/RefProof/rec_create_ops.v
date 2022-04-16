Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RmiAux2.Spec.
Require Import RmiOps.Specs.rec_destroy_ops.
Require Import RmiOps.LowSpecs.rec_destroy_ops.
Require Import RmiOps.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       get_g_rec_rd_spec
       granule_map_spec
       get_rec_g_rec_spec
       get_rec_g_rec_list_spec
       get_rec_rec_idx_spec
       null_ptr_spec
       realm_set_rec_entry_spec
       buffer_unmap_spec
       set_g_rec_rd_spec
       granule_memzero_spec
       granule_set_state_spec
       granule_unlock_spec
       granule_put_spec
       atomic_granule_put_release_spec
    .

  Lemma rec_destroy_ops_spec_exists:
    forall habd habd'  labd g_rec
           (Hspec: rec_destroy_ops_spec g_rec habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', rec_destroy_ops_spec0 g_rec labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. inv id_rdata. destruct g_rec.
    unfold rec_destroy_ops_spec, rec_destroy_ops_spec0 in *.
    repeat autounfold in *. unfold ref_accessible.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; simpl in * ).
    assert(6 <> 3) by omega.
    assert(z <> (g_rec_rec_list (grec (gs (share labd)) @ z))) by (red; intro T; rewrite <- T in *; omega).
    assert((g_rd (ginfo (gs (share labd)) @ z)) <> z) by (red; intro T; srewrite; omega).
    assert((g_rd (ginfo (gs (share labd)) @ z)) <> (g_rec_rec_list (grec (gs (share labd)) @ z))) by (red; intro T; srewrite; omega).
    repeat (simpl_htarget; try grewrite; repeat swap_fields; repeat simpl_field; simpl in * ).
    repeat (solve_bool_range; grewrite).
    solve_peq.
    repeat (simpl_htarget; try grewrite; repeat swap_fields; repeat simpl_field; simpl in * ).
    eexists; split. reflexivity.
    constructor. simpl_htarget. rewrite (zmap_comm 3 6). simpl_htarget.
    rewrite Prop0, <- Prop1. simpl_htarget. simpl_field. reflexivity.
    red; intro T; inv T.
  Qed.

End Refine.
