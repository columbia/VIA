Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import TableAux.Spec.
Require Import TableWalk.Specs.table_walk_lock_unlock.
Require Import TableWalk.LowSpecs.table_walk_lock_unlock.
Require Import TableWalk.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       granule_map_spec
       get_rd_g_rtt_spec
       buffer_unmap_spec
       granule_lock_spec
       is_null_spec
       addr_to_idx_spec
       find_next_level_idx_spec
       granule_unlock_spec
       set_wi_g_llt_spec
       set_wi_index_spec
    .

    Lemma table_walk_lock_unlock_spec_exists_0:
      forall habd habd'  labd g_rd map_addr level
        (Hspec: table_walk_lock_unlock_spec g_rd map_addr level habd = Some habd')
        (Hrel: relate_RData habd labd)
        (Hlevel: level = (VZ64 0)),
      exists labd', table_walk_lock_unlock_spec0 g_rd map_addr level labd = Some labd' /\ relate_RData habd' labd'.
    Proof.
      pose proof addr_to_idx_range as ar.
      pose proof entry_to_gidx_range as er.
      intros. destruct level as [level]. inv Hlevel.
      destruct Hrel. inv id_rdata.
      unfold table_walk_lock_unlock_spec0, table_walk_lock_unlock_spec in *.
      repeat autounfold in *. simpl in *.
      hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
        repeat destruct_con; bool_rel; simpl in *; srewrite;
          repeat (grewrite; simpl_htarget; simpl in * ).
      rewrite ar.
      eexists; split. reflexivity. constructor; simpl; try assumption. reflexivity.
      apply andb_true_iff. split; bool_rel; assumption.
    Qed.

    Ltac simpl_prop :=
      match goal with
      | H:?P |- context [prop_dec ?P] =>
        let tmp := fresh "He" in
        destruct (prop_dec P) as [tmp| tmp]; [ simpl; clear tmp | apply tmp in H; inversion H ]
      end.

    Lemma table_walk_lock_unlock_spec_exists_1:
      forall habd habd'  labd g_rd map_addr level
        (Hspec: table_walk_lock_unlock_spec g_rd map_addr level habd = Some habd')
        (Hrel: relate_RData habd labd)
        (Hlevel: level = (VZ64 1)),
      exists labd', table_walk_lock_unlock_spec0 g_rd map_addr level labd = Some labd' /\ relate_RData habd' labd'.
    Proof.
      pose proof addr_to_idx_range as ar.
      pose proof entry_to_phys_range as er.
      pose proof entry_to_gidx_range as aer.
      intros. destruct level as [level]. inv Hlevel.
      destruct Hrel. inv id_rdata.
      unfold table_walk_lock_unlock_spec0, table_walk_lock_unlock_spec in *.
      repeat autounfold in *. simpl in *. repeat autounfold in *; simpl in *.
      hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
        repeat destruct_con; bool_rel; simpl in *; srewrite.
      - rewrite ZMap.gss. simpl. simpl_prop. grewrite. simpl.
        repeat (solve_peq; simpl).
        repeat (grewrite; simpl_htarget; simpl).
        repeat (try rewrite ar; try rewrite er; try rewrite aer); try (apply andb_true_iff; split; bool_rel; assumption).
        solve_peq. simpl. solve_bool_range. grewrite. simpl_ACQ. rewrite repl_nil.
        simpl. rewrite ZMap.gso.
        simpl_prop. simpl. rewrite ZMap.gso. rewrite ZMap.gss.
        repeat (simpl_htarget; grewrite; simpl).
        extract_if. reflexivity. grewrite.
        eexists. split. reflexivity. constructor; simpl; try assumption.
        repeat (simpl_field; swap_fields).
        rewrite zmap_comm. rewrite ZMap.set2.
        rewrite <- Prop1. simpl_field. rewrite <- C12. simpl_field. rewrite zmap_set_id.
        reflexivity.
        red; intro T; repeat srewrite. inv C9.
        red; intro T. rewrite <- T in C16. rewrite C16 in *. inv C9.
        red; intro T; repeat srewrite. inv C9.
      - solve_peq; simpl. rewrite ZMap.gss. simpl. simpl_prop. grewrite. simpl.
        repeat (solve_peq; simpl).
        repeat (grewrite; simpl_htarget; simpl).
        repeat (try rewrite ar; try rewrite er; try rewrite aer); try (apply andb_true_iff; split; bool_rel; assumption).
        solve_peq. solve_ptr_eq. simpl.
        repeat (grewrite; simpl_htarget; simpl). solve_peq. solve_bool_range. grewrite.
        eexists. split. reflexivity. constructor; simpl; try assumption.
        repeat (simpl_field; swap_fields).
        rewrite <- Prop0. simpl_field. rewrite <- C12. simpl_field. rewrite zmap_set_id.
        simpl_field. reflexivity.
    Qed.

End Refine.

