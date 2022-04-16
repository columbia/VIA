Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RunAux.Spec.
Require Import RunComplete.Specs.complete_hvc_exit.
Require Import RunComplete.LowSpecs.complete_hvc_exit.
Require Import RunComplete.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       get_rec_last_run_info_esr_spec
       set_rec_regs_spec
       get_rec_run_gprs_spec
       reset_last_run_info_spec
    .

  Lemma complete_hvc_exit_spec_exists:
    forall habd habd'  labd rec
           (Hspec: complete_hvc_exit_spec rec habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', complete_hvc_exit_spec0 rec labd = Some labd' /\ relate_RData habd' labd'.
    Proof.
      intros. destruct Hrel. destruct rec. Local Transparent Z.add.
      unfold complete_hvc_exit_spec, complete_hvc_exit_spec0 in *.
      repeat autounfold in *. simpl in *.
      hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
        repeat destruct_con; simpl in *; srewrite; repeat simpl_update_reg;
          repeat (simpl_htarget; grewrite; simpl in * ).
      unfold ref_accessible in *. autounfold.
      repeat (grewrite; try rewrite ZMap.gss; try rewrite ZMap.set2; simpl; grewrite; simpl).
      eexists; split. reflexivity. constructor. repeat (repeat simpl_field; repeat swap_fields).
      repeat simpl_update_reg. reflexivity.
      eexists; split. reflexivity. constructor. reflexivity.
    Qed.

End Refine.

