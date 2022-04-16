Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import PSCIHandler.Spec.
Require Import RealmSyncHandler.Specs.handle_realm_rsi.
Require Import RealmSyncHandler.LowSpecs.handle_realm_rsi.
Require Import RealmSyncHandler.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       get_rec_regs_spec
       set_rec_regs_spec
       psci_rsi_spec
       get_psci_result_x0_spec
       get_psci_result_x1_spec
       get_psci_result_x2_spec
       get_psci_result_x3_spec
       get_psci_result_forward_psci_call_spec
       set_rec_run_exit_reason_spec
       set_rec_run_gprs_spec
       get_psci_result_forward_x1_spec
       get_psci_result_forward_x2_spec
       get_psci_result_forward_x3_spec
    .

  Lemma handle_realm_rsi_spec_exists:
    forall habd habd'  labd rec res
           (Hspec: handle_realm_rsi_spec rec habd = Some (habd', res))
            (Hrel: relate_RData habd labd),
    exists labd', handle_realm_rsi_spec0 rec labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    intros. inv Hspec.
  Qed.

End Refine.

