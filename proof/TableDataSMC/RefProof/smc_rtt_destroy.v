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
Require Import TableDataOpsIntro.Specs.table_destroy.
Require Import TableDataOpsIntro.LowSpecs.table_destroy.
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
       find_lock_granule_spec
       assert_cond_spec
       granule_unlock_spec
       buffer_unmap_spec
    .

  Lemma table_destroy_spec_exists:
    forall habd habd'  labd g_rd map_addr rtt_addr level res
      (Hspec: table_destroy_spec g_rd map_addr rtt_addr level habd = Some (habd', res))
      (Hlevel: level = (VZ64 2))
      (Hrel: relate_RData habd labd),
    exists labd', table_destroy_spec0 g_rd map_addr rtt_addr level labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque peq ptr_eq fill_table table_destroy_aux_spec.
    intros. destruct level as [level]. inv Hlevel.
    destruct Hrel. inv id_rdata. destruct g_rd.
    unfold table_destroy_spec, table_destroy_spec0 in *. simpl.
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
      repeat (try solve_peq; try solve_ptr_eq; simpl).
      repeat (grewrite; try simpl_htarget; simpl; repeat solve_table_range).
      unfold destroy_table in *. repeat autounfold in *. simpl in *. repeat simpl_hyp Hspec; inversion Hspec; clear Hspec.
      + simpl. clear H0. srewrite. repeat destruct_con.
        assert(Hne1:  llt_gidx <> __addr_to_gidx z1). bool_rel; red; intro T; rewrite <- T in *; omega.
        assert(hne2: 5 <> 7). red; intro T; inv T.
        repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl; repeat solve_table_range).
        solve_bool_range. grewrite. unfold query_oracle in *; simpl in *. autounfold in *. repeat simpl_hyp C16. inv C16. simpl in *.
        extract_prop_dec. repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl; repeat solve_table_range).
        solve_bool_range. grewrite. solve_ptr_eq. simpl.
        Local Transparent table_destroy_aux_spec. unfold table_destroy_aux_spec.
        repeat autounfold. simpl. repeat (grewrite; try solve_peq; try solve_ptr_eq; simpl).
        repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl; repeat solve_table_range).
        rewrite ZMap.gso. repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl).
        match goal with
        | |- context [prop_dec (?a = ?a)] => destruct (prop_dec (a = a)); [ simpl | contra ]
        end.
        red in Hne1. simpl_htarget.
        repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl).
        eexists. split. reflexivity. constructor.
        repeat rewrite (zmap_comm _ _ Hne1).
        repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl).
        bool_rel. srewrite. rewrite <- Prop8, <- C29. simpl_field. reflexivity.
        red; intro T; inv T.
      + simpl. clear H0. srewrite. repeat destruct_con.
        destruct_dis;
          repeat (grewrite; try simpl_htarget; repeat simpl_field; repeat swap_fields; simpl; repeat solve_table_range).
        solve_bool_range. grewrite.
        eexists; split. reflexivity. constructor. rewrite <- Prop0. simpl_field.
        bool_rel. grewrite. rewrite <- C0. simpl_field. simpl_htarget. simpl_field. reflexivity.
        eexists; split. reflexivity. constructor. rewrite <- Prop0. simpl_field.
        bool_rel. grewrite. rewrite <- C0. simpl_field. simpl_htarget. simpl_field. reflexivity.
        eexists; split. reflexivity. constructor. rewrite <- Prop0. simpl_field.
        bool_rel. grewrite. rewrite <- C0. simpl_field. simpl_htarget. simpl_field. reflexivity.
    - unfold get_wi_g_llt_spec, is_null_spec; simpl. solve_ptr_eq; simpl.
      autounfold in *; solve_table_range. inv Hspec. eexists; split. reflexivity. constructor.
      reflexivity.
  Qed.

End Refine.
