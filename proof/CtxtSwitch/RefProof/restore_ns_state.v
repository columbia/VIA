Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import CtxtSwitchAux.Spec.
Require Import AbsAccessor.Spec.
Require Import CtxtSwitch.Specs.restore_ns_state.
Require Import CtxtSwitch.LowSpecs.restore_ns_state.
Require Import CtxtSwitch.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       restore_ns_state_sysreg_state_spec
       get_ns_state_spec
       sysreg_write_spec
    .

  Lemma restore_ns_state_spec_exists:
    forall habd habd'  labd
      (Hspec: restore_ns_state_spec  habd = Some habd')
      (Hrel: relate_RData habd labd),
    exists labd', restore_ns_state_spec0  labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel.
    unfold restore_ns_state_spec, restore_ns_state_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; simpl in * ).
    destruct regs_is_int64_dec in *. autounfold in e. repeat rewrite e.
    repeat simpl_update_reg.
    eexists; split. reflexivity. constructor. reflexivity.
    inv C.
  Qed.

End Refine.

