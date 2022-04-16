Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import TableAux2.Spec.
Require Import TableAux3.Specs.table_create_aux.
Require Import TableAux3.LowSpecs.table_create_aux.
Require Import TableAux3.RefProof.RefRel.
Require Import TableAux.Specs.granule_fill_table.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       granule_map_spec
       table_create_init_vacant_spec
       table_create_init_absent_spec
       table_create_init_present_spec
       assert_cond_spec
       buffer_unmap_spec
       granule_get_spec
       granule_set_state_spec
       set_g_rtt_rd_spec
       pgte_write_spec
       link_table_spec
  .

  Lemma table_create_aux_spec_exists:
    forall habd habd'  labd g_rd g_llt g_rtt llt_pte ll_table level index map_addr rtt_addr
      (Hspec: table_create_aux_spec g_rd g_llt g_rtt llt_pte ll_table level index map_addr rtt_addr habd = Some habd')
      (Hrel: relate_RData habd labd),
    exists labd', table_create_aux_spec0 g_rd g_llt g_rtt llt_pte ll_table level index map_addr rtt_addr labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq peq fill_table. pose proof orb_64_range as orr.
    pose proof pte_4096_range as p4096.
    pose proof pte_2011_4096_range as p2_4096.
    intros. destruct Hrel. inv id_rdata. destruct g_rd, g_llt, g_rtt, ll_table.
    unfold table_create_aux_spec, table_create_aux_spec0 in *; repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; extract_prop_dec.
    - solve_table_range. simpl in *. inv Prop2.
      destruct_dis.
      + solve_peq; simpl. repeat (grewrite; try simpl_htarget; simpl in * ).
        simpl. assert(z0 <> z1). red; intro T. inv T. bool_rel; srewrite. omega.
        assert(z1 = z0 -> False). intro T; inv T. contra.
        repeat (grewrite; try simpl_htarget; simpl in * ).
        solve_peq. rewrite orr. simpl. grewrite. simpl.
        repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl).
        eexists; split. reflexivity. constructor.
        repeat rewrite (zmap_comm _ _ H). simpl_htarget. reflexivity.
        assumption. reflexivity. inversion C10.
      + solve_peq; simpl. repeat (grewrite; try simpl_htarget; simpl in * ).
        simpl. assert(z0 <> z1). red; intro T. inv T. bool_rel; srewrite. omega.
        assert(z1 = z0 -> False). intro T; inv T. contra.
        repeat (grewrite; try simpl_htarget; simpl in * ).
        solve_peq. rewrite orr. simpl. grewrite. simpl.
        repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl).
        eexists; split. reflexivity. constructor.
        repeat rewrite (zmap_comm _ _ H). simpl_htarget. reflexivity.
        assumption. reflexivity. inversion C10.
      + solve_peq; simpl. repeat (grewrite; try simpl_htarget; simpl in * ).
        simpl. assert(z0 <> z1). red; intro T. inv T. bool_rel; srewrite. omega.
        assert(z1 = z0 -> False). intro T; inv T. contra.
        repeat (grewrite; try simpl_htarget; simpl in * ).
        solve_peq. rewrite orr. simpl. grewrite. simpl.
        repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl).
        eexists; split. reflexivity. constructor.
        repeat rewrite (zmap_comm _ _ H). simpl_htarget. reflexivity.
        assumption. reflexivity. inversion C10.
    - solve_table_range. simpl in *. inv Prop2.
      apply orb_false_iff in C25. destruct C25. grewrite.
      repeat (grewrite; try simpl_htarget; simpl in * ).
      simpl. assert(z0 <> z1). red; intro T. inv T. bool_rel; srewrite. omega.
      assert(z1 = z0 -> False). intro T; inv T. contra.
      solve_table_range. rewrite orr. rewrite p4096.
      repeat (grewrite; try simpl_htarget; simpl in * ).
      solve_peq. rewrite orr. simpl. grewrite. simpl.
      repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl).
      eexists; split. reflexivity. constructor.
      repeat rewrite (zmap_comm _ _ H1). simpl_htarget. reflexivity.
      assumption. reflexivity. inversion C10. assumption. omega. reflexivity. solve_table_range. reflexivity.
    - solve_table_range. simpl in *. inv Prop2.
      apply orb_false_iff in C25. destruct C25. grewrite.
      repeat (grewrite; try simpl_htarget; simpl in * ).
      simpl. assert(z0 <> z1). red; intro T. inv T. bool_rel; srewrite. omega.
      assert(z1 = z0 -> False). intro T; inv T. contra.
      solve_table_range. rewrite orr. rewrite p2_4096.
      repeat (grewrite; try simpl_htarget; simpl in * ).
      bool_rel; srewrite. rewrite ZMap.gso. grewrite.
      assert(z0 = z1 -> False). intro T; inv T. contra. simpl_htarget.
      repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl).
      solve_peq. rewrite orr. simpl. grewrite. simpl.
      repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl).
      repeat rewrite (zmap_comm _ _ H1). simpl_htarget.
      eexists; split. reflexivity. constructor. reflexivity.
      assumption. reflexivity. inversion C10. red; intro T; inv T.
      assumption. omega. apply orr. reflexivity. solve_table_range. reflexivity. reflexivity.
  Qed.

End Refine.
