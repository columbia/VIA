Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import RVIC.Specs.is_trusted_intid.
Require Import RVIC.LowSpecs.is_trusted_intid.
Require Import RVIC.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Lemma is_trusted_intid_spec_exists:
    forall habd  labd intid res
      (Hspec: is_trusted_intid_spec intid habd = Some res)
      (Hrel: relate_RData habd labd),
      is_trusted_intid_spec0 intid labd = Some res.
  Proof.
    intros. inv Hrel.
    unfold is_trusted_intid_spec, is_trusted_intid_spec0 in *.
    repeat hsimpl_hyp Hspec; bool_rel_all; repeat destruct_dis; inv Hspec;
      repeat simpl_htarget; reflexivity.
  Qed.

End Refine.

