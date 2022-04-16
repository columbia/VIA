Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import TableWalk.Spec.
Require Import AbsAccessor.Spec.
Require Import TableAux3.Spec.
Require Import TableDataOpsIntro.Specs.table_create.
Require Import TableDataOpsIntro.LowSpecs.table_create.
Require Import TableDataOpsIntro.RefProof.RefRel.
Require Import TableAux.Specs.granule_fill_table.

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
       buffer_unmap_spec
       granule_unlock_spec
    .

  Lemma table_create_spec_exists:
    forall habd habd'  labd g_rd map_addr level g_rtt rtt_addr res
      (Hspec: table_create_spec g_rd map_addr level g_rtt rtt_addr habd = Some (habd', res))
      (Hlevel: level = (VZ64 2))
      (Hrel: relate_RData habd labd),
    exists labd', table_create_spec0 g_rd map_addr level g_rtt rtt_addr labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque peq ptr_eq fill_table.
    intros. destruct level as [level]. inv Hlevel.
    destruct Hrel. inv id_rdata. destruct g_rd, g_rtt.
    unfold table_create_spec, table_create_spec0 in *. simpl.
    unfold table_walk_lock_unlock_spec. simpl in *.
    unfold Assertion in *.
    rm_bind Hspec; rm_bind'. simpl in *.
    repeat simpl_hyp Hspec; extract_prop_dec.
    - repeat destruct_con. simpl_query_oracle. simpl in *.
      match type of Hcond0 with
      | is_gidx ?gidx = true => remember gidx as llt_gidx eqn:Hllt_gidx; symmetry in Hllt_gidx
      end.
      repeat autounfold in *. simpl in *.
      destruct_if. repeat destruct_con. bool_rel; omega.
      solve_bool_range. grewrite. repeat solve_table_range.
      repeat (try solve_peq; try solve_ptr_eq; simpl). simpl_htarget.
      repeat (grewrite; try simpl_htarget; simpl; repeat solve_table_range).
      unfold create_table in *. autounfold in *. simpl in *. repeat simpl_hyp Hspec; inversion Hspec; clear Hspec.
      + simpl. clear H0. repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl; repeat solve_table_range).
        eexists; split. reflexivity. constructor. rewrite <- Prop0. simpl_field. bool_rel. rewrite C, <- C0. simpl_field.
        simpl_htarget. simpl_field. reflexivity.
      + simpl. clear H0. rewrite ZMap.gso. bool_rel.
        assert(Hne1:  __addr_to_gidx z2 <> llt_gidx). red; intro T; srewrite; omega.
        repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl; repeat solve_table_range).
        eexists; split. reflexivity. constructor. rewrite <- Prop0. simpl_field.
        repeat rewrite (zmap_comm _ _ Hne1). simpl_htarget. rewrite <- C0. simpl_field. reflexivity.
        red; intro T; inv T.
    - unfold get_wi_g_llt_spec, is_null_spec; simpl. solve_ptr_eq; simpl.
      autounfold in *; solve_table_range. inv Hspec. eexists; split. reflexivity. constructor.
      reflexivity.
  Qed.

End Refine.
