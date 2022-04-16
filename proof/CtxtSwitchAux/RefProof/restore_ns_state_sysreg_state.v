Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import CtxtSwitchAux.Specs.restore_ns_state_sysreg_state.
Require Import CtxtSwitchAux.LowSpecs.restore_ns_state_sysreg_state.
Require Import CtxtSwitchAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       get_ns_state_spec
       sysreg_write_spec
    .

  Lemma restore_ns_state_sysreg_state_spec_exists:
    forall habd habd'  labd
           (Hspec: restore_ns_state_sysreg_state_spec  habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', restore_ns_state_sysreg_state_spec0  labd = Some labd' /\ relate_RData habd' labd'.
    Proof.
      Local Opaque ptr_eq get_reg set_reg.
      intros. destruct Hrel.
      unfold restore_ns_state_sysreg_state_spec, restore_ns_state_sysreg_state_spec0 in *.
      unfold sysreg_write_spec, get_ns_state_spec.
      autounfold in Hspec.
      hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec.
      destruct regs_is_int64_dec in C; [|inversion C].
      unfold Assertion.
      repeat (unfold bind64 at 1; rewrite e; repeat simpl_update_reg; repeat (simpl priv; simpl cpu_regs; simpl_field);
              unfold bind at 1; simpl ns_regs_el2).
      eexists; split. reflexivity. constructor. reflexivity.
    Qed.

End Refine.

