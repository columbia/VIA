Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import TableAux.Specs.granule_fill_table.
Require Import TableAux.LowSpecs.granule_fill_table.
Require Import TableAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       pgte_write_spec
       barrier_spec
    .

  Lemma mul_ge:
    forall a b c, 0 <= a -> 0 <= b -> b <= c -> a * b <= a * c.
  Proof.
    intros. auto with zarith.
  Qed.

  Lemma granule_fill_table_spec_exists:
    forall habd habd'  labd pte pte_val pte_inc
           (Hspec: granule_fill_table_spec pte pte_val pte_inc habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', granule_fill_table_spec0 pte pte_val pte_inc labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    intros. destruct Hrel. inv id_rdata. destruct pte.
    unfold granule_fill_table_spec, granule_fill_table_spec0 in *. autounfold in *.
    repeat simpl_hyp Hspec; inv Hspec.
    assert(forall n table' i' pte_val'
             (Hfill: fill_table n (g_data (gnorm (gs (share labd)) @ z2)) 0 z0 z1 = (table', i', pte_val'))
             (Hn: 0 <= Z.of_nat n <= PGTES_PER_TABLE),
              let gn := (gs (share labd)) @ z2 in
              let g' := gn {gnorm : (gnorm gn) {g_data : table'}} in
              granule_fill_table_loop0 n 0 (p, z) z0 z1 labd = Some (i', pte_val', labd {share : (share labd) {gs : (gs (share labd)) # z2 == g'}}) /\
              i' = Z.of_nat n /\
              pte_val' = z0 + z1 * (Z.of_nat n)).
    { clear C8. induction n.
      - simpl. intros. inv Hfill. repeat (simpl_field; simpl_htarget).
        split. reflexivity. split. reflexivity. omega.
      - rewrite Nat2Z.inj_succ, succ_plus_1 in *. intros until pte_val'. simpl. intros.
        repeat simpl_hyp Hfill. exploit IHn. reflexivity. omega.
        simpl in *. intros. destruct H as (T1 & T2 & T3). repeat grewrite. autounfold in *.
        solve_bool_range. grewrite. repeat destruct_con.
        assert(0 <= Z.of_nat n < 512). omega.
        assert(z1 * 0 <= z1 * Z.of_nat n <= z1 * 512).
        split; bool_rel. destruct Hn. apply mul_ge; omega. apply mul_ge; omega.
        solve_bool_range. grewrite. repeat (simpl_htarget; grewrite; simpl in * ).
        inversion Hfill; grewrite. split. repeat (simpl_field; simpl_htarget; simpl).
        rewrite <- H2. rewrite <- H3, <- H4, T2, T3. reflexivity.
        split. omega. rewrite <- H4, T3. rewrite  Z.mul_add_distr_l. omega. }
    exploit (H _ _ _ _ C8). autounfold. simpl. omega. intros.
    destruct H0 as (T1 & T2 & T3). rewrite T1. grewrite; simpl.
    grewrite. eexists; split. reflexivity. constructor. reflexivity.
  Qed.

End Refine.

