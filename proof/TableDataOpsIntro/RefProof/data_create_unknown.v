Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import TableWalk.Spec.
Require Import AbsAccessor.Spec.
Require Import TableDataOpsIntro.Specs.data_create_unknown.
Require Import TableDataOpsIntro.LowSpecs.data_create_unknown.
Require Import TableDataOpsIntro.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       table_walk_lock_unlock_spec
       get_wi_g_llt_spec
       get_wi_index_spec
       is_null_spec
       granule_map_spec
       pgte_read_spec
       pgte_write_spec
       set_mapping_spec
       granule_get_spec
       buffer_unmap_spec
       granule_unlock_spec
  .

  Lemma data_create_unknown_spec_exists:
    forall habd habd'  labd g_rd data_addr map_addr g_data res
      (Hspec: data_create_unknown_spec g_rd data_addr map_addr g_data habd = Some (habd', res))
      (Hrel: relate_RData habd labd),
    exists labd', data_create_unknown_spec0 g_rd data_addr map_addr g_data labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque peq ptr_eq.
    assert(ne51: 5<>1) by (red; intro T; inv T).
    assert(ne50: 5<>0) by (red; intro T; inv T).
    assert(ne10: 1<>0) by (red; intro T; inv T).
    intros. destruct Hrel. inv id_rdata. destruct g_data, g_rd.
    unfold data_create_unknown_spec, data_create_unknown_spec0 in *. simpl.
    unfold table_walk_lock_unlock_spec. simpl. unfold Assertion in *.
    rm_bind Hspec; rm_bind'. simpl in *. repeat simpl_hyp Hspec.
    unfold Assertion; rm_bind'.
    repeat simpl_hyp Hspec.
    hsimpl_hyp Hspec; inv Hspec; extract_prop_dec.
    - repeat destruct_con. simpl_query_oracle.
      match type of Hcond6 with
      | is_gidx ?gidx = true => remember gidx as lv1_gidx eqn:Hlv1_gidx; symmetry in Hlv1_gidx
      end.
      match type of Hcond3 with
      | is_gidx ?gidx = true => remember gidx as lv2_gidx eqn:Hlv2_gidx; symmetry in Hlv2_gidx
      end.
      match type of Hcond0 with
      | is_gidx ?gidx = true => remember gidx as llt_gidx eqn:Hllt_gidx; symmetry in Hllt_gidx
      end.
      repeat simpl_field; repeat swap_fields; repeat simpl_field.
      assert(nelz: llt_gidx <> (__addr_to_gidx z2)) by (bool_rel; red; intro T; rewrite T in *; autounfold in *; omega).
      repeat autounfold in *. simpl in *.
      destruct_if. repeat destruct_con. bool_rel; omega.
      solve_bool_range. grewrite. repeat solve_table_range.
      repeat (try solve_peq; try solve_ptr_eq; simpl). simpl_htarget.
      repeat (grewrite; try simpl_htarget; simpl; repeat solve_table_range).
      repeat (repeat simpl_field; repeat swap_fields; simpl_htarget).
      extract_if. reflexivity. grewrite. solve_table_range.
      repeat (grewrite; try simpl_htarget; simpl; repeat solve_table_range).
      eexists; split. reflexivity. constructor.
      repeat (try rewrite (zmap_comm _ _ ne51);
              try rewrite (zmap_comm _ _ nelz)).
      repeat (repeat simpl_field; repeat swap_fields; simpl_htarget).
      rewrite <- Prop1. simpl_field. rewrite Z.mul_1_l. bool_rel. grewrite.
      rewrite <- C38. simpl_field. reflexivity.
    - repeat destruct_con. simpl_query_oracle.
      match type of Hcond6 with
      | is_gidx ?gidx = true => remember gidx as lv1_gidx eqn:Hlv1_gidx; symmetry in Hlv1_gidx
      end.
      match type of Hcond3 with
      | is_gidx ?gidx = true => remember gidx as lv2_gidx eqn:Hlv2_gidx; symmetry in Hlv2_gidx
      end.
      match type of Hcond0 with
      | is_gidx ?gidx = true => remember gidx as llt_gidx eqn:Hllt_gidx; symmetry in Hllt_gidx
      end.
      repeat simpl_field; repeat swap_fields; repeat simpl_field.
      repeat autounfold in *. simpl in *.
      destruct_if. repeat destruct_con. bool_rel; omega.
      solve_bool_range. grewrite. repeat solve_table_range.
      repeat (try solve_peq; try solve_ptr_eq; simpl). simpl_htarget.
      repeat (grewrite; try simpl_htarget; simpl; repeat solve_table_range).
      inversion Hspec. clear Hspec. extract_prop_dec.
      eexists; split. reflexivity. constructor.
      repeat rewrite (zmap_comm _ _ ne51).
      bool_rel. simpl_htarget. clear H0. grewrite.
      repeat (repeat simpl_field; repeat swap_fields; repeat simpl_field; simpl_htarget; simpl).
      rewrite <- Prop0, <- C38. repeat simpl_field. simpl_htarget. simpl_field. reflexivity.
    - unfold get_wi_g_llt_spec, is_null_spec; simpl. solve_ptr_eq; simpl.
      autounfold in *; solve_table_range. inv Hspec. eexists; split. reflexivity. constructor.
      reflexivity.
    - unfold get_wi_g_llt_spec, is_null_spec; simpl. solve_ptr_eq; simpl.
      autounfold in *; solve_table_range. inv Hspec. eexists; split. reflexivity. constructor.
      reflexivity.
    - unfold get_wi_g_llt_spec, is_null_spec; simpl. solve_ptr_eq; simpl.
      autounfold in *; solve_table_range. inv Hspec. eexists; split. reflexivity. constructor.
      reflexivity.
  Qed.

End Refine.

