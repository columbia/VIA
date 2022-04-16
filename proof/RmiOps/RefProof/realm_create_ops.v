Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RmiAux.Spec.
Require Import RmiOps.Specs.realm_create_ops.
Require Import RmiOps.LowSpecs.realm_create_ops.
Require Import RmiOps.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       get_locked_granule_spec
       set_g_rtt_rd_spec
       granule_set_state_spec
       granule_unlock_spec
       granule_map_spec
       set_rd_state_spec
       get_realm_params_spec
       get_realm_params_par_base_spec
       get_realm_params_par_size_spec
       set_rd_par_base_spec
       set_rd_par_end_spec
       set_rd_g_rtt_spec
       set_rd_g_rec_list_spec
       get_realm_params_measurement_algo_spec
       set_rd_measurement_algo_spec
       measurement_start_spec
       buffer_unmap_spec
  .

  Lemma realm_create_ops_spec_exists:
    forall habd habd'  labd
      (Hspec: realm_create_ops_spec  habd = Some habd')
      (Hrel: relate_RData habd labd),
    exists labd', realm_create_ops_spec0  labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. inv id_rdata.
    unfold realm_create_ops_spec, realm_create_ops_spec0 in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; repeat swap_fields; repeat simpl_field; simpl in * ).
    bool_rel; repeat (simpl_htarget; grewrite; repeat swap_fields; repeat simpl_field; simpl in * ).
    repeat (solve_bool_range; grewrite).
    destruct_if; bool_rel;
      repeat (simpl_htarget; grewrite; repeat swap_fields; repeat simpl_field; simpl in * );
      repeat (
          try rewrite (zmap_comm ((locked_g (priv labd)) @ 0) ((locked_g (priv labd)) @ 2));
          try rewrite (zmap_comm ((locked_g (priv labd)) @ 1) ((locked_g (priv labd)) @ 2));
          try rewrite (zmap_comm ((locked_g (priv labd)) @ 0) ((locked_g (priv labd)) @ 1)));
      try assumption;
      eexists; (split; [reflexivity| constructor; try reflexivity]).
  Qed.

End Refine.

