Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import TableAux.Specs.table_has_destroyed.
Require Import TableAux.LowSpecs.table_has_destroyed.
Require Import TableAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       pgte_read_spec
  .

  Lemma table_has_destroyed_spec_exists:
    forall habd  labd table res
      (Hspec: table_has_destroyed_spec table habd = Some res)
      (Hrel: relate_RData habd labd),
      table_has_destroyed_spec0 table labd = Some res.
  Proof.
    intros. destruct Hrel. inv id_rdata. destruct table.
    unfold table_has_destroyed_spec, table_has_destroyed_spec0 in *. autounfold in *.
    repeat simpl_hyp Hspec; inv Hspec.
    assert(forall n (Hn: 0 <= Z.of_nat n <= PGTES_PER_TABLE),
              let gn := (gs (share labd)) @ z0 in
              table_has_destroyed_loop0 n 0 0 (p, z) labd =
              Some (Z.of_nat n,
                    if prop_dec (exists i, 0 <= i < Z.of_nat n /\ PTE_TO_IPA_STATE ((g_data (gnorm gn)) @ i) = IPA_STATE_DESTROYED)
                    then 1 else 0)).
    { induction n.
      - simpl. intros. destruct_if. destruct e. omega. reflexivity.
      - rewrite Nat2Z.inj_succ, succ_plus_1 in *. intros.
        simpl in *. exploit IHn. autounfold in *. omega. intro T. rewrite T. autounfold in *.
        solve_bool_range. grewrite. repeat destruct_con.
        extract_if. destruct_if; reflexivity. grewrite.
        extract_prop_dec. rewrite Prop0.
        repeat destruct_if; try reflexivity; bool_rel.
        red in n0. exploit n0. eexists. instantiate(1:=Z.of_nat n). split. omega. assumption. intro F; inv F.
        red in n0. exploit n0. destruct e. exists x. destruct a. split. omega. assumption. intro F; inv F.
        destruct e. destruct a. destruct (x =? Z.of_nat n) eqn:Hx; bool_rel. rewrite <- Hx in *.
        replace ((gs (share labd)) @ z0) with gn in Case by reflexivity. rewrite e in Case. contra.
        assert(0 <= x < Z.of_nat n) by omega.
        red in n0. exploit n0. exists x. split. assumption. assumption. intro F; inv F. }
    simpl in H. erewrite H. simpl. extract_if. destruct_if; reflexivity. grewrite.
    autounfold. reflexivity. autounfold; simpl; omega.
  Qed.

End Refine.

