Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RealmTimerHandler.Specs.handle_ptimer_sysreg_write.
Require Import RealmTimerHandler.LowSpecs.handle_ptimer_sysreg_write.
Require Import RealmTimerHandler.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       ESR_EL2_SYSREG_ISS_RT_spec
       get_rec_regs_spec
       sysreg_write_spec
       set_rec_ptimer_masked_spec
       sysreg_read_spec
       get_rec_ptimer_masked_spec
       get_rec_ptimer_spec
       timer_condition_met_spec
       set_rec_ptimer_asserted_spec
       get_rec_sysregs_spec
       set_rec_sysregs_spec
    .

  Lemma handle_ptimer_sysreg_write_spec_exists:
    forall habd habd'  labd rec esr
      (Hspec: handle_ptimer_sysreg_write_spec rec esr habd = Some habd')
      (Hrel: relate_RData habd labd),
    exists labd', handle_ptimer_sysreg_write_spec0 rec esr labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. destruct rec.
    unfold handle_ptimer_sysreg_write_spec, handle_ptimer_sysreg_write_spec0 in *.
    repeat autounfold in *. simpl in *; unfold ref_accessible in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; simpl in *; srewrite;
        repeat (repeat grewrite; simpl; repeat simpl_update_reg; simpl; try rewrite ZMap.gss; simpl;
                repeat (extract_if; [bool_rel_all; apply andb_true_iff; split; bool_rel;
                                     match goal with
                                     | [|- Z.lor ?a ?b <= ?x] => apply or_le_64; somega
                                     | _ => somega
                                     end | idtac]; grewrite; simpl));
        try solve[eexists; split;
                  [reflexivity|
                   constructor; simpl;
                   repeat (repeat simpl_field; repeat swap_fields; repeat rewrite ZMap.set2; simpl);
                   reflexivity]].
  Qed.

End Refine.

