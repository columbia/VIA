Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import TableAux.Spec.
Require Import TableAux2.Specs.table_fold.
Require Import TableAux2.LowSpecs.table_fold.
Require Import TableAux2.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       pgte_read_spec
       entry_to_phys_spec
       table_maps_block_spec
       granule_refcount_dec_spec
    .

  Lemma table_fold_spec_exists:
    forall habd habd'  labd table level g_tbl res
      (Hspec: table_fold_spec table level g_tbl habd = Some (habd', res))
      (Hrel: relate_RData habd labd),
    exists labd', table_fold_spec0 table level g_tbl labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. inv id_rdata. destruct table, g_tbl.
    unfold table_fold_spec, table_fold_spec0 in *.
    pose proof entry_to_phys_range as er.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; repeat swap_fields; repeat simpl_field; simpl in * ).
    inv Prop4. pose proof (Prop1 0). destruct_con; bool_rel.
    solve_bool_range. grewrite. solve_bool_range. grewrite.
    solve_bool_range. grewrite. rewrite er. simpl. repeat destruct_con; bool_rel.
    extract_if. apply andb_true_iff. split; bool_rel. somega.
    match goal with | |- context[?a/?b*?b] => assert(a/b*b <= a) end.
    rewrite Z.mul_comm. apply Z_mult_div_ge. omega. omega. grewrite. destruct_con; bool_rel.
    match goal with
    | |- context[__entry_to_phys ?entry ?level] => exploit (entry_to_phys_range entry level)
    end.
    apply Prop1. intros. autounfold in H. destruct_con; bool_rel.
    extract_if. apply andb_true_iff. split; bool_rel. somega.
    apply or_le_64; somega. grewrite. destruct_con; bool_rel. destruct_if.
    + extract_if. apply andb_true_iff. split; bool_rel. somega.
      apply or_le_64; somega. grewrite.
      eexists. split. reflexivity. constructor. reflexivity.
    + rewrite or0_eq. solve_bool_range. grewrite.
      eexists. split. reflexivity. constructor. reflexivity.
    + apply Prop1.
  Qed.

End Refine.

