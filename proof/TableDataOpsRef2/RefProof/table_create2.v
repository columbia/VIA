Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import TableDataOpsIntro.Spec.
Require Import TableDataOpsRef1.Spec.
Require Import TableDataOpsRef2.Specs.table_create2.
Require Import TableDataOpsRef2.LowSpecs.table_create2.
Require Import TableDataOpsRef2.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       table_create_spec
       table_create1_spec
    .

  Lemma table_create2_spec_exists:
    forall habd habd'  labd g_rd map_addr level g_rtt rtt_addr res
      (Hspec: table_create2_spec g_rd map_addr level g_rtt rtt_addr habd = Some (habd', res))
      (Hrel: relate_RData habd labd),
    exists labd', table_create2_spec0 g_rd map_addr level g_rtt rtt_addr labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque peq ptr_eq granule_fill_table.fill_table.
    intros. duplicate Hrel. destruct D. clear hrepl lrepl. destruct g_rtt, g_rd.
    unfold table_create2_spec, table_create2_spec0 in *.
    unfold Assertion in *. rm_bind Hspec; rm_bind'. simpl in *.
    unfold Assertion; rm_bind'; grewrite.
    repeat simpl_hyp Hspec; extract_prop_dec; simpl_query_oracle; rm_bind'; grewrite.
    - rewrite_oracle_rel rel_oracle C10.
      repeat (grewrite; try simpl_htarget; simpl).
      unfold create_table in *. simpl in *. autounfold in *. simpl in *. grewrite.
      repeat simpl_hyp Hspec; simpl; inversion Hspec;
        (eexists; split; [reflexivity| constructor; destruct Hrel; simpl; try assumption; try reflexivity]).
    - rewrite_oracle_rel rel_oracle C10.
      repeat (grewrite; try simpl_htarget; simpl).
      unfold create_table in *. simpl in *. autounfold in *. simpl in *. grewrite.
      repeat simpl_hyp Hspec; simpl; inversion Hspec;
        (eexists; split; [reflexivity| constructor; destruct Hrel; simpl; try assumption; try reflexivity]).
    - rewrite_oracle_rel rel_oracle C10.
      repeat (grewrite; try simpl_htarget; simpl).
      unfold create_table in *. simpl in *. autounfold in *. simpl in *. grewrite.
      repeat simpl_hyp Hspec; simpl; inversion Hspec;
        (eexists; split; [reflexivity| constructor; destruct Hrel; simpl; try assumption; try reflexivity]).
    - rewrite_oracle_rel rel_oracle C10.
      repeat (grewrite; try simpl_htarget; simpl).
      inversion Hspec; (eexists; split; [reflexivity| constructor; destruct Hrel; simpl; try assumption; try reflexivity]).
    - rewrite_oracle_rel rel_oracle C10.
      repeat (grewrite; try simpl_htarget; simpl).
      inversion Hspec; (eexists; split; [reflexivity| constructor; destruct Hrel; simpl; try assumption; try reflexivity]).
  Qed.

End Refine.

