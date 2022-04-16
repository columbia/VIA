Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import TableDataOpsIntro.Spec.
Require Import TableDataOpsRef1.Specs.table_unmap1.
Require Import TableDataOpsRef1.LowSpecs.table_unmap1.
Require Import TableDataOpsRef1.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       table_unmap_spec
    .

  Lemma table_unmap1_spec_exists:
    forall habd habd'  labd g_rd map_addr level res
           (Hspec: table_unmap1_spec g_rd map_addr level habd = Some (habd', res))
            (Hrel: relate_RData habd labd),
    exists labd', table_unmap1_spec0 g_rd map_addr level labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque peq ptr_eq.
    intros. duplicate Hrel. destruct D. clear hrepl lrepl. destruct g_rd.
    unfold table_unmap1_spec, table_unmap1_spec0 in *.
    unfold Assertion in *. rm_bind Hspec; rm_bind'. simpl in *.
    unfold Assertion; rm_bind'; grewrite.
    repeat simpl_hyp Hspec; extract_prop_dec; simpl_query_oracle; rm_bind'; grewrite.
    - rewrite_oracle_rel rel_oracle C6.
      repeat (grewrite; try simpl_htarget; simpl).
      assert(Hwalk: repl habd (oracle habd
                                      (EVT CPU_ID (RTT_WALK (g_rtt (gnorm (gs (share habd)) @ z)) z0 1) :: oracle habd (log habd) ++ log habd)) s = Some s).
      destruct Hrel. grewrite. destruct valid_ho0. rewrite Hright_log_nil. reflexivity.
      eapply RightLogMover.
      apply walk_right. omega. omega. apply RightLogOracle.
      rewrite_oracle_rel rel_oracle Hwalk; simpl in *.
      repeat (grewrite; try simpl_htarget; simpl).
      unfold unmap_table in *. simpl in *. autounfold in *. simpl in *. grewrite.
      repeat simpl_hyp Hspec; simpl; inversion Hspec; clear H0; grewrite;
        (eexists; split; [reflexivity| constructor; destruct Hrel; simpl; try assumption; try reflexivity]).
    - rewrite_oracle_rel rel_oracle C.
      repeat (grewrite; try simpl_htarget; simpl).
      assert(Hwalk: repl habd (oracle habd
                                      (EVT CPU_ID (RTT_WALK (g_rtt (gnorm (gs (share habd)) @ z)) z0 1) :: oracle habd (log habd) ++ log habd)) s0 = Some s0).
      destruct Hrel. grewrite. destruct valid_ho0. rewrite Hright_log_nil. reflexivity.
      eapply RightLogMover.
      apply walk_right. omega. omega. apply RightLogOracle.
      rewrite_oracle_rel rel_oracle Hwalk; simpl in *.
      repeat (grewrite; try simpl_htarget; simpl).
      rewrite_oracle_rel rel_oracle C6; simpl in *.
      repeat (grewrite; try simpl_htarget; simpl).
      unfold unmap_table in *. simpl in *. autounfold in *. simpl in *. grewrite.
      repeat simpl_hyp Hspec; simpl; inversion Hspec; clear H0; grewrite;
        (eexists; split; [reflexivity| constructor; destruct Hrel; simpl; try assumption; try reflexivity]).
    - rewrite_oracle_rel rel_oracle C6.
      repeat (grewrite; try simpl_htarget; simpl).
      assert(Hwalk: repl habd (oracle habd
                                      (EVT CPU_ID (RTT_WALK (g_rtt (gnorm (gs (share habd)) @ z)) z0 1) :: oracle habd (log habd) ++ log habd)) s = Some s).
      destruct Hrel. grewrite. destruct valid_ho0. rewrite Hright_log_nil. reflexivity.
      eapply RightLogMover.
      apply walk_right. omega. omega. apply RightLogOracle.
      rewrite_oracle_rel rel_oracle Hwalk; simpl in *.
      repeat (grewrite; try simpl_htarget; simpl). inversion Hspec.
      (eexists; split; [reflexivity| constructor; destruct Hrel; simpl; try assumption; try reflexivity]).
    - rewrite_oracle_rel rel_oracle C6.
      repeat (grewrite; try simpl_htarget; simpl).
      inversion Hspec. eexists; split. reflexivity.
      constructor; destruct Hrel; simpl; try assumption; try reflexivity.
    - rewrite_oracle_rel rel_oracle C6.
      repeat (grewrite; try simpl_htarget; simpl).
      inversion Hspec. eexists; split. reflexivity.
      constructor; destruct Hrel; simpl; try assumption; try reflexivity.
  Qed.

End Refine.
