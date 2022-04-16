Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import CtxtSwitchAux.Spec.
Require Import AbsAccessor.Spec.
Require Import CtxtSwitch.Specs.save_ns_state.
Require Import CtxtSwitch.LowSpecs.save_ns_state.
Require Import CtxtSwitch.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       save_ns_state_sysreg_state_spec
       sysreg_read_spec
       set_ns_state_spec
    .

  Lemma save_ns_state_spec_exists:
    forall habd habd'  labd
      (Hspec: save_ns_state_spec  habd = Some habd')
      (Hrel: relate_RData habd labd),
    exists labd', save_ns_state_spec0  labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel.
    unfold save_ns_state_spec, save_ns_state_spec0 in *.
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

