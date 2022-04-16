Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import TableAux.Spec.
Require Import AbsAccessor.Spec.
Require Import TableAux2.Specs.table_create_init_vacant.
Require Import TableAux2.LowSpecs.table_create_init_vacant.
Require Import TableAux2.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       granule_fill_table_spec
       granule_get_spec
    .

  Lemma or0_eq:
    forall n, Z.lor n 0 = n.
  Proof.
    intros. rewrite Z.lor_comm. reflexivity.
  Qed.

  Lemma table_create_init_vacant_spec_exists:
    forall habd habd'  labd ipa_state pte g_llt
           (Hspec: table_create_init_vacant_spec ipa_state pte g_llt habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', table_create_init_vacant_spec0 ipa_state pte g_llt labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq fill_table.
    intros. destruct Hrel. inv id_rdata. destruct pte, g_llt.
    unfold table_create_init_vacant_spec, table_create_init_vacant_spec0 in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; repeat swap_fields; repeat simpl_field; simpl in * ).
    rewrite or0_eq. repeat (solve_bool_range; grewrite).
    simpl. simpl_htarget. eexists; split. reflexivity. constructor. reflexivity.
  Qed.

End Refine.

