Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import TableWalk.Spec.
Require Import AbsAccessor.Spec.
Require Import TableDataOpsIntro.Specs.table_map.
Require Import TableDataOpsIntro.LowSpecs.table_map.
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
       entry_is_table_spec
       pgte_write_spec
       buffer_unmap_spec
       granule_unlock_spec
    .

  Lemma table_map_spec_exists:
    forall habd habd'  labd g_rd map_addr level res
      (Hspec: table_map_spec g_rd map_addr level habd = Some (habd', res))
      (Hlevel: level = VZ64 3)
      (Hrel: relate_RData habd labd),
    exists labd', table_map_spec0 g_rd map_addr level labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque peq ptr_eq.
    intros. destruct level as [level]. inv Hlevel.
    destruct Hrel. inv id_rdata. destruct g_rd.
    unfold table_map_spec, table_map_spec0 in *. simpl.
    unfold table_walk_lock_unlock_spec. simpl. unfold Assertion in *.
    rm_bind Hspec; rm_bind'. simpl in *. repeat simpl_hyp Hspec.
    unfold Assertion; rm_bind'.
    repeat simpl_hyp Hspec.
    hsimpl_hyp Hspec; inv Hspec; extract_prop_dec.
    - repeat destruct_con.
      match type of Hcond3 with
      | is_gidx ?gidx = true => remember gidx as lv1_gidx eqn:Hlv1_gidx; symmetry in Hlv1_gidx
      end.
      match type of Hcond0 with
      | is_gidx ?gidx = true => remember gidx as llt_gidx eqn:Hllt_gidx; symmetry in Hllt_gidx
      end.
      repeat autounfold in *. simpl in *.
      destruct_if. repeat destruct_con. bool_rel; omega.
      solve_bool_range. grewrite. repeat solve_table_range.
      repeat (try solve_peq; try solve_ptr_eq; simpl). simpl_htarget.
      repeat (grewrite; try simpl_htarget; simpl; repeat solve_table_range).
      unfold map_table in *. autounfold in *. simpl in *. repeat simpl_hyp H0; inversion H0; clear H0.
      + repeat (first[solve_table_range; solve_bool_range; grewrite]).
        repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl; repeat solve_table_range).
        eexists; split. reflexivity. constructor. rewrite <- H1. clear H1.
        repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl).
        rewrite <- Prop0. simpl_field. bool_rel. rewrite C, <- C2. simpl_field.
        rewrite Prop0, C2, <- Prop4. simpl_htarget. simpl_query_oracle. simpl_htarget. reflexivity.
      + repeat (first[solve_table_range; solve_bool_range; grewrite]).
        repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl; repeat solve_table_range).
        eexists; split. reflexivity. constructor. rewrite <- H1. clear H1.
        rewrite <- Prop0. simpl_field. bool_rel. rewrite C, <- C2. simpl_field.
        repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl).
        rewrite <- Prop4. simpl_query_oracle. simpl_htarget. reflexivity.
    - unfold get_wi_g_llt_spec, is_null_spec; simpl. solve_ptr_eq; simpl.
      autounfold in *; solve_table_range. inv Hspec. eexists; split. reflexivity. constructor.
      reflexivity.
    - unfold get_wi_g_llt_spec, is_null_spec; simpl. solve_ptr_eq; simpl.
      autounfold in *; solve_table_range. inv Hspec. eexists; split. reflexivity. constructor.
      reflexivity.
  Qed.

End Refine.

