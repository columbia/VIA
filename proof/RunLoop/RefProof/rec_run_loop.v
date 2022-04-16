Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import CtxtSwitch.Spec.
Require Import AbsAccessor.Spec.
Require Import RunLoop.Specs.rec_run_loop.
Require Import RunLoop.LowSpecs.rec_run_loop.
Require Import RunLoop.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       save_ns_state_spec
       restore_realm_state_spec
       configure_realm_stage2_spec
       restore_hcr_el2_spec
       run_realm_spec
  .

  Lemma rec_run_loop_spec_exists:
    forall habd habd'  labd rec
           (Hspec: rec_run_loop_spec rec habd = Some habd')
           (Hrel: relate_RData habd labd),
    exists labd', rec_run_loop_spec0 rec labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    intros. inv Hrel. destruct rec.
    unfold rec_run_loop_spec, rec_run_loop_spec0 in *. repeat autounfold in *.
    rewrite Hspec. eexists; split. reflexivity.
    constructor; reflexivity.
  Qed.

End Refine.

