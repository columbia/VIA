Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RealmExitHandlerAux.Specs.handle_excpetion_irq_lel.
Require Import RealmExitHandlerAux.LowSpecs.handle_excpetion_irq_lel.
Require Import RealmExitHandlerAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       sysreg_read_spec
       set_rec_run_exit_reason_spec
    .

  Lemma handle_excpetion_irq_lel_spec_exists:
    forall habd habd'  labd rec res
      (Hspec: handle_excpetion_irq_lel_spec rec habd = Some (habd', res))
      (Hrel: relate_RData habd labd),
    exists labd', handle_excpetion_irq_lel_spec0 rec labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    intros. destruct Hrel. destruct rec.
    unfold handle_excpetion_irq_lel_spec, handle_excpetion_irq_lel_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; repeat destruct_dis; bool_rel; simpl in *; srewrite;
        repeat simpl_update_reg; repeat (simpl_htarget; grewrite; simpl in * );
          repeat (solve_bool_range; grewrite);
          (eexists; split; [reflexivity|constructor; reflexivity]).
  Qed.

End Refine.

