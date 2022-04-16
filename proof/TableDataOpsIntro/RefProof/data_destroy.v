Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import TableWalk.Spec.
Require Import AbsAccessor.Spec.
Require Import TableDataOpsIntro.Specs.data_destroy.
Require Import TableDataOpsIntro.LowSpecs.data_destroy.
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
       find_lock_granule_spec
       pgte_write_spec
       granule_put_spec
       granule_memzero_spec
       granule_set_state_spec
       granule_unlock_spec
       buffer_unmap_spec
    .

  Lemma data_destroy_spec_exists:
    forall habd habd'  labd g_rd map_addr res
      (Hspec: data_destroy_spec g_rd map_addr habd = Some (habd', res))
      (Hrel: relate_RData habd labd),
    exists labd', data_destroy_spec0 g_rd map_addr labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    assert(ne51: 5 <> 1) by (red; intro T; inv T).
    Local Opaque peq ptr_eq.
    intros. destruct Hrel. inv id_rdata. destruct g_rd.
    unfold data_destroy_spec, data_destroy_spec0 in *. simpl.
    unfold table_walk_lock_unlock_spec. simpl. unfold Assertion in *.
    rm_bind Hspec; rm_bind'. simpl in *. repeat simpl_hyp Hspec.
    unfold Assertion; rm_bind'.
    repeat simpl_hyp Hspec.
    hsimpl_hyp Hspec; inv Hspec; extract_prop_dec.
    - repeat destruct_con. simpl_query_oracle. simpl in *.
      match type of Hcond6 with
      | is_gidx ?gidx = true => remember gidx as lv1_gidx eqn:Hlv1_gidx; symmetry in Hlv1_gidx
      end.
      match type of Hcond3 with
      | is_gidx ?gidx = true => remember gidx as lv2_gidx eqn:Hlv2_gidx; symmetry in Hlv2_gidx
      end.
      match type of Hcond0 with
      | is_gidx ?gidx = true => remember gidx as llt_gidx eqn:Hllt_gidx; symmetry in Hllt_gidx
      end.
      match type of Prop0 with
      | glock ?a @ ?gidx = None => remember gidx as data_gidx eqn:Hdata_gidx; symmetry in Hdata_gidx
      end.
      assert(nez: llt_gidx <> data_gidx) by (bool_rel; red; intro T; rewrite T in *; autounfold in *; omega).
      repeat autounfold in *. simpl in *.
      destruct_if. repeat destruct_con. bool_rel; omega.
      solve_bool_range. grewrite. repeat solve_table_range.
      repeat (try solve_peq; try solve_ptr_eq; simpl). simpl_htarget.
      repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl; repeat solve_table_range).
      repeat (solve_bool_range; grewrite). repeat (rewrite ZMap.gss in * ); simpl in *.
      grewrite. simpl in *. repeat (repeat solve_table_range; solve_bool_range; grewrite).
      repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl).
      solve_bool_range. grewrite. repeat (try solve_peq; try solve_ptr_eq; simpl).
      extract_if. reflexivity. grewrite.
      eexists; split. reflexivity. constructor.
      repeat (try rewrite (zmap_comm _ _ ne51);
              try rewrite (zmap_comm _ _ nez)).
      bool_rel. replace (3 * 72057594037927936) with 216172782113783808 by reflexivity.
      grewrite; rewrite <- Prop0, <- C40.
      repeat (repeat simpl_field; repeat swap_fields; repeat simpl_field; simpl_htarget; simpl).
      reflexivity.
    - repeat destruct_con. simpl_query_oracle. simpl in *. extract_prop_dec.
      match type of Hcond6 with
      | is_gidx ?gidx = true => remember gidx as lv1_gidx eqn:Hlv1_gidx; symmetry in Hlv1_gidx
      end.
      match type of Hcond3 with
      | is_gidx ?gidx = true => remember gidx as lv2_gidx eqn:Hlv2_gidx; symmetry in Hlv2_gidx
      end.
      match type of Hcond0 with
      | is_gidx ?gidx = true => remember gidx as llt_gidx eqn:Hllt_gidx; symmetry in Hllt_gidx
      end.
      repeat autounfold in *. simpl in *.
      destruct_if. repeat destruct_con. bool_rel; omega.
      solve_bool_range. grewrite. repeat solve_table_range.
      repeat (try solve_peq; try solve_ptr_eq; simpl). simpl_htarget.
      repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl; repeat solve_table_range).
      repeat (solve_bool_range; grewrite). repeat (rewrite ZMap.gss in * ); simpl in *.
      grewrite. simpl in *. repeat (repeat solve_table_range; solve_bool_range; grewrite).
      repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl).
      inversion Hspec. clear Hspec. eexists; split.  reflexivity. constructor.
      repeat rewrite (zmap_comm _ _ ne51).
      bool_rel. replace (3 * 72057594037927936) with 216172782113783808 by reflexivity.
      clear H0 H1. grewrite; rewrite <- Prop0, <- C33. repeat simpl_field.
      repeat swap_fields; repeat simpl_field; simpl_htarget; simpl. reflexivity.
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

