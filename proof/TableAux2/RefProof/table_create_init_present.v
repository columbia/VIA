Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import TableAux.Spec.
Require Import TableAux2.Specs.table_create_init_present.
Require Import TableAux2.LowSpecs.table_create_init_present.
Require Import TableAux2.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       pgte_write_spec
       invalidate_block_spec
       entry_to_phys_spec
       granule_fill_table_spec
       granule_refcount_inc_spec
       assert_cond_spec
    .

  Lemma table_create_init_present_spec_exists:
    forall habd habd'  labd level ll_table index map_addr llt_pte pte g_rtt
           (Hspec: table_create_init_present_spec level ll_table index map_addr llt_pte pte g_rtt habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', table_create_init_present_spec0 level ll_table index map_addr llt_pte pte g_rtt labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq fill_table.
    intros. destruct Hrel. inv id_rdata. destruct pte, g_rtt, ll_table.
    unfold table_create_init_present_spec, table_create_init_present_spec0 in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; repeat swap_fields; repeat simpl_field; simpl in * ).
    inv Prop3. solve_bool_range; grewrite.
    extract_if. apply andb_true_iff. split; bool_rel. somega. apply or_le_64; try solve[somega]. grewrite.
    eexists. split. reflexivity. constructor. repeat rewrite (zmap_comm _ _ Prop2).
    repeat swap_fields; repeat simpl_field. repeat simpl_htarget.
    repeat match goal with
    | |- context[?a {gs: ?b} {tlbs: ?c}] =>
      replace (a {gs: b} {tlbs: c}) with (a {tlbs: c} {gs: b}) by reflexivity
    end.
    repeat simpl_field. repeat simpl_htarget. reflexivity.
  Qed.

End Refine.

