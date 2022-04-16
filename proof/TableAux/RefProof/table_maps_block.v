Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import TableAux.Specs.table_maps_block.
Require Import TableAux.LowSpecs.table_maps_block.
Require Import TableAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       pgte_read_spec
       entry_to_phys_spec
       addr_is_level_aligned_spec
    .

  Lemma table_maps_block_spec_exists:
    forall habd  labd table level ipa_state res
           (Hspec: table_maps_block_spec table level ipa_state habd = Some res)
            (Hrel: relate_RData habd labd),
    table_maps_block_spec0 table level ipa_state labd = Some res.
  Proof.
    intros. destruct Hrel. inv id_rdata. destruct table.
    unfold table_maps_block_spec, table_maps_block_spec0 in *. autounfold in *.
    repeat simpl_hyp Hspec; inv Hspec. extract_prop_dec.
    rewrite Prop0. solve_bool_range; grewrite.
    assert(forall n (Hn: 0 <= Z.of_nat n <= PGTES_PER_TABLE),
              let gn := (gs (share labd)) @ z2 in
              table_maps_block_loop0 n 0 1 (p, z) (__entry_to_phys (g_data (gnorm (gs (share labd)) @ z2)) @ 0 z0) z0 z1 labd =
              Some (Z.of_nat n, if prop_dec (forall i (Hi: 0 <= i < Z.of_nat n),
                                                let e := (g_data (gnorm (gs (share labd)) @ z2)) @ i in
                                                let pa := __entry_to_phys e z0 in
                                                let base_pa := __entry_to_phys (g_data (gnorm (gs (share labd)) @ z2)) @ 0 z0 in
                                                PTE_TO_IPA_STATE e = z1 /\ pa = base_pa + i * GRANULE_SIZE)
                                then 1 else 0)).
    { induction n.
      - simpl. intros. destruct_if. reflexivity. red in n. exploit n. intros. omega. intro F; inv F.
      - rewrite Nat2Z.inj_succ, succ_plus_1 in *. intros.
        simpl in *. exploit IHn. autounfold in *. omega. intro T. rewrite T. autounfold in *.
        solve_bool_range. grewrite. repeat destruct_con.
        extract_if. destruct_if; reflexivity. grewrite.
        extract_prop_dec. repeat (simpl_htarget; grewrite; simpl). rewrite Prop0.
        assert(0 <= Z.of_nat n < 512) by omega.
        solve_bool_range. grewrite. pose proof entry_to_phys_range as er. autounfold in er.
        rewrite er; try apply Prop0.
        repeat destruct_if; try reflexivity; bool_rel; extract_prop_dec; clear_hyp.
        red in n0. exploit n0. intros. destruct (i =? Z.of_nat n) eqn:Hii; bool_rel.
        rewrite <- Hii in *. split; assumption. apply a. omega. intro F; inv F.
        red in n0. exploit n0. intros. apply a. omega. intro F; inv F.
        pose proof (a (Z.of_nat n)). destruct H0. omega. omega.
        pose proof (a (Z.of_nat n)). destruct H0. omega. omega. }
    rewrite H. simpl.
    extract_if. destruct_if; reflexivity. grewrite. reflexivity. autounfold; simpl. omega.
    simpl. extract_prop_dec. rewrite Prop0. solve_bool_range. grewrite. reflexivity.
  Qed.

End Refine.

