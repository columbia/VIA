Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RmiOps.Specs.realm_destroy_ops.
Require Import RmiOps.LowSpecs.realm_destroy_ops.
Require Import RmiOps.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       null_ptr_spec
       set_g_rtt_rd_spec
       granule_set_state_spec
       granule_unlock_spec
       granule_memzero_spec
       granule_lock_spec
    .

  Lemma realm_destroy_ops_spec_exists:
    forall habd habd'  labd g_rtt g_rec_list g_rd
           (Hspec: realm_destroy_ops_spec g_rtt g_rec_list g_rd habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', realm_destroy_ops_spec0 g_rtt g_rec_list g_rd labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. inv id_rdata. destruct g_rtt, g_rec_list, g_rd.
    unfold realm_destroy_ops_spec, realm_destroy_ops_spec0 in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; repeat swap_fields; repeat simpl_field; simpl in * ).
    assert(zneq1: z <> z0) by (red; intro T; inv T; omega).
    assert(zneq2: z <> z1) by (red; intro T; inv T; omega).
    assert(zneq3: z0 <> z1) by (red; intro T; inv T; omega).
    repeat (simpl_htarget; grewrite; repeat swap_fields; repeat simpl_field; simpl in * ).
    solve_peq.
    repeat (simpl_htarget; grewrite; repeat swap_fields; repeat simpl_field; simpl in * ).
    repeat (
        try rewrite (zmap_comm z z0);
        try rewrite (zmap_comm z z1);
        try rewrite (zmap_comm z0 z1));
      try assumption.
    eexists; split. reflexivity.
    constructor. simpl_htarget. rewrite <- Prop3. simpl_field. grewrite. reflexivity.
  Qed.

End Refine.

