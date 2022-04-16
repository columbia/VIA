Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import TableAux.Spec.
Require Import AbsAccessor.Spec.
Require Import TableAux2.Specs.table_delete.
Require Import TableAux2.LowSpecs.table_delete.
Require Import TableAux2.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       table_has_destroyed_spec
       granule_put_spec
    .

  Lemma or0_eq:
    forall n, Z.lor n 0 = n.
  Proof.
    intros. rewrite Z.lor_comm. reflexivity.
  Qed.

  Lemma table_delete_spec_exists:
    forall habd habd'  labd table g_llt res
      (Hspec: table_delete_spec table g_llt habd = Some (habd', res))
      (Hrel: relate_RData habd labd),
    exists labd', table_delete_spec0 table g_llt labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. inv id_rdata. destruct table, g_llt.
    unfold table_delete_spec, table_delete_spec0 in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; repeat swap_fields; repeat simpl_field; simpl in * ).
    rewrite or0_eq. extract_if. destruct_if; reflexivity. grewrite.
    repeat (extract_if; try reflexivity; grewrite).
    destruct prop_dec; simpl; eexists; split; try reflexivity; constructor; reflexivity.
  Qed.

End Refine.

