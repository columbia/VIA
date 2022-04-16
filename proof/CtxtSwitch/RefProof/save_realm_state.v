Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import CtxtSwitchAux.Spec.
Require Import AbsAccessor.Spec.
Require Import CtxtSwitch.Specs.save_realm_state.
Require Import CtxtSwitch.LowSpecs.save_realm_state.
Require Import CtxtSwitch.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       save_sysreg_state_spec
       sysreg_read_spec
       set_rec_pc_spec
       set_rec_pstate_spec
    .

  Lemma save_realm_state_spec_exists:
    forall habd habd'  labd rec
           (Hspec: save_realm_state_spec rec habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', save_realm_state_spec0 rec labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. destruct rec.
    unfold save_realm_state_spec, save_realm_state_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; simpl in * ).
    destruct regs_is_int64_dec in *. autounfold in e. repeat rewrite e.
    unfold ref_accessible in *; simpl in *; repeat grewrite. simpl in *.
    repeat (simpl_htarget; grewrite; simpl in * ). rewrite e.
    repeat simpl_update_reg.
    eexists; split. reflexivity. constructor. reflexivity.
    inv C3.
  Qed.

End Refine.

