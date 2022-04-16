Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import CtxtSwitchAux.Specs.save_sysreg_state.
Require Import CtxtSwitchAux.LowSpecs.save_sysreg_state.
Require Import CtxtSwitchAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       sysreg_read_spec
       set_rec_sysregs_spec
    .

  Lemma save_sysreg_state_spec_exists:
    forall habd habd'  labd rec
           (Hspec: save_sysreg_state_spec rec habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', save_sysreg_state_spec0 rec labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq get_reg set_reg.
    intros. destruct Hrel. destruct rec.
    unfold save_sysreg_state_spec, save_sysreg_state_spec0 in *.
    unfold set_rec_sysregs_spec, sysreg_read_spec.
    autounfold in Hspec. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec. autounfold in *.
    destruct regs_is_int64_dec in C3; [|inversion C3].
    unfold Assertion. unfold buffer_loc. grewrite.
    unfold ref_accessible in *. unfold GRANULE_STATE_REC. autounfold in *.
    repeat (rewrite e; grewrite; simpl;
            repeat rewrite ZMap.gss; simpl_update_reg; repeat rewrite ZMap.set2; repeat simpl_field;
            simpl; grewrite; simpl).
    eexists; split. reflexivity. constructor.
    repeat (simpl_update_reg; simpl; repeat simpl_field).
    reflexivity.
  Qed.

End Refine.

