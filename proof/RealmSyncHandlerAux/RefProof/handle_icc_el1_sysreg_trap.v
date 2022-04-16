Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RealmSyncHandlerAux.Specs.handle_icc_el1_sysreg_trap.
Require Import RealmSyncHandlerAux.LowSpecs.handle_icc_el1_sysreg_trap.
Require Import RealmSyncHandlerAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       ESR_EL2_SYSREG_ISS_RT_spec
       ESR_EL2_SYSREG_IS_WRITE_spec
       set_rec_regs_spec
    .

  Lemma handle_icc_el1_sysreg_trap_spec_exists:
    forall habd habd'  labd rec esr
      (Hspec: handle_icc_el1_sysreg_trap_spec rec esr habd = Some habd')
      (Hrel: relate_RData habd labd),
    exists labd', handle_icc_el1_sysreg_trap_spec0 rec esr labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. destruct rec.
    unfold handle_icc_el1_sysreg_trap_spec, handle_icc_el1_sysreg_trap_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite; repeat simpl_update_reg;
        repeat (simpl_htarget; grewrite; simpl in * );
        try solve[repeat (solve_bool_range; grewrite); eexists; split; [reflexivity|constructor; reflexivity]].
  Qed.

End Refine.

