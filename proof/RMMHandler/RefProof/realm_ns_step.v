Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RMMHandler.Specs.realm_ns_step.
Require Import RMMHandler.LowSpecs.realm_ns_step.
Require Import RMMHandler.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       user_step_spec
  .

  Lemma realm_ns_step_spec_exists:
    forall habd habd'  labd ret
           (Hspec: realm_ns_step_spec  habd = Some (habd', VZ64 ret))
           (Hrel: relate_RData habd labd),
    exists labd', realm_ns_step_spec0  labd = Some (labd', VZ64 ret) /\ relate_RData habd' labd'.
  Proof.
    intros. unfold realm_ns_step_spec, realm_ns_step_spec0 in *; autounfold in *.
    inv Hrel. repeat simpl_hyp Hspec; inv Hspec;
                (eexists; split; [reflexivity|constructor;reflexivity]).
  Qed.

End Refine.

