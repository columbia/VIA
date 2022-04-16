Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import BaremoreHandler.Spec.
Require Import AbsAccessor.Spec.
Require Import SMCHandler.Spec.
Require Import RMMHandler.Specs.rmm_handler.
Require Import RMMHandler.LowSpecs.rmm_handler.
Require Import RMMHandler.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       el3_sync_lel_spec
       enter_rmm_spec
       read_reg_spec
       handle_ns_smc_spec
       exit_rmm_spec
    .

  Lemma rmm_handler_spec_exists:
    forall habd habd'  labd
           (Hspec: rmm_handler_spec  habd = Some habd')
           (Hrel: relate_RData habd labd),
    exists labd', rmm_handler_spec0  labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    intros. inv Hrel.
    unfold rmm_handler_spec, rmm_handler_spec0 in *.
    rewrite Hspec. eexists; split. reflexivity.
    constructor; reflexivity.
  Qed.

End Refine.

