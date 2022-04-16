Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import TableAux2.Spec.
Require Import TableAux.Spec.
Require Import TableAux3.Specs.table_destroy_aux.
Require Import TableAux3.LowSpecs.table_destroy_aux.
Require Import TableAux3.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       granule_map_spec
       get_g_rtt_refcount_spec
       table_delete_spec
       table_fold_spec
       pgte_write_spec
       invalidate_page_spec
       invalidate_pages_in_block_spec
       invalidate_block_spec
       granule_put_spec
       null_ptr_spec
       set_g_rtt_rd_spec
       granule_memzero_mapped_spec
       granule_memzero_spec
       granule_set_state_spec
       buffer_unmap_spec
    .


  Lemma table_destroy_aux_spec_exists:
    forall habd habd'  labd g_llt g_tbl ll_table level index map_addr res
      (Hspec: table_destroy_aux_spec g_llt g_tbl ll_table level index map_addr habd = Some (habd', res))
      (Hrel: relate_RData habd labd),
    exists labd', table_destroy_aux_spec0 g_llt g_tbl ll_table level index map_addr labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq peq fill_table. pose proof orb_64_range as orr.
    pose proof IPA_PTE_IPA as ipi. pose proof IPA_PTE_IPA2 as ipi2.
    pose proof pte_4096_range as p4096.
    pose proof pte_2011_4096_range as p2_4096.
    intros. destruct Hrel. inv id_rdata. destruct g_llt, g_tbl, ll_table.
    unfold table_destroy_aux_spec, table_destroy_aux_spec0 in *; repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; extract_prop_dec.
    - simpl in *. grewrite. inv Prop2.
      match goal with
      | |- context [prop_dec (?a = ?a)] => destruct (prop_dec (a = a)); [ simpl | contra ]
      end.
      grewrite. solve_peq. simpl.
      repeat (grewrite; try simpl_htarget; simpl in * ).
      rewrite table_a5_d7. extract_if. bool_rel. grewrite. reflexivity. grewrite.
      extract_if. destruct_if; reflexivity. grewrite.
      rewrite ZMap.gso. repeat (grewrite; try simpl_htarget; simpl in * ).
      solve_bool_range. grewrite.
      destruct_if. destruct_if' Case; inversion Case.
      rewrite ZMap.gso. repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl).
      extract_if. bool_rel; grewrite. omega. grewrite. solve_peq.
      repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl).
      eexists; split. reflexivity. constructor.
      rewrite (zmap_comm _ _ Prop3). bool_rel. grewrite. simpl.
      destruct_if. reflexivity. reflexivity.
      red; intro T; inv T. red; intro T; inv T. destruct_if; reflexivity.
    - simpl in *. grewrite. inv Prop2.
      match goal with
      | |- context [prop_dec (?a = ?a)] => destruct (prop_dec (a = a)); [ simpl | contra ]
      end.
      grewrite. solve_peq. simpl.
      repeat (grewrite; try simpl_htarget; simpl in * ).
      solve_bool_range. grewrite. solve_bool_range. grewrite.
      extract_if. bool_rel; grewrite. omega. grewrite.
      extract_if. destruct_if. apply orb_64_range. autounfold. apply orb_64_range. autounfold.
      rewrite table_a5_d7_m7. reflexivity. apply Prop1. autounfold. apply entry_to_phys_range. apply Prop1. reflexivity.
      apply orb_64_range. autounfold. rewrite table_a5_d7_m7. reflexivity.
      apply Prop1. autounfold. apply entry_to_phys_range. apply Prop1. grewrite.
      repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl).
      rewrite ZMap.gso. repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl).
      solve_bool_range. grewrite. solve_bool_range. grewrite.
      destruct (Z.land (g_data (gnorm (gs (share labd)) @ z0)) @ 0 504403158265495552 / 72057594037927936 =? 2) eqn:ipa.
      + rewrite ipi. grewrite. rewrite ZMap.gso. grewrite.
        simpl_htarget. grewrite. simpl. simpl_htarget.
        extract_if. bool_rel. grewrite. omega. grewrite. simpl.
        repeat simpl_field; repeat swap_fields; simpl_htarget. solve_peq.
        simpl. simpl_htarget. repeat simpl_field; repeat swap_fields; simpl_htarget.
        repeat rewrite (zmap_comm _ _ Prop4).
        simpl. simpl_htarget. repeat simpl_field; repeat swap_fields; simpl_htarget.
        eexists. split. reflexivity. constructor. bool_rel. grewrite. simpl. reflexivity.
        red; intro T; inv T. apply Prop1. apply Prop1. omega.
      + rewrite ipi2. grewrite. rewrite ZMap.gso. grewrite.
        simpl_htarget. grewrite. simpl. simpl_htarget.
        extract_if. bool_rel. grewrite. omega. grewrite. simpl.
        repeat simpl_field; repeat swap_fields; simpl_htarget. solve_peq.
        simpl. simpl_htarget. repeat simpl_field; repeat swap_fields; simpl_htarget.
        repeat rewrite (zmap_comm _ _ Prop4).
        simpl. simpl_htarget. repeat simpl_field; repeat swap_fields; simpl_htarget.
        eexists. split. reflexivity. constructor. bool_rel. grewrite. simpl. reflexivity.
        red; intro T; inv T. apply Prop1. apply Prop1.
      + red; intro T; inv T.
  Qed.

End Refine.

