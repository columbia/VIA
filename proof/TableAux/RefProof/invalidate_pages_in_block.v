Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import TableAux.Specs.invalidate_pages_in_block.
Require Import TableAux.LowSpecs.invalidate_pages_in_block.
Require Import TableAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       barrier_spec
       stage2_tlbi_ipa_spec
    .

  Lemma invalidate_pages_in_block_spec_exists:
    forall habd habd'  labd addr
      (Hspec: invalidate_pages_in_block_spec addr habd = Some habd')
      (Hrel: relate_RData habd labd),
    exists labd', invalidate_pages_in_block_spec0 addr labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    intros. destruct Hrel. inv id_rdata.
    unfold invalidate_pages_in_block_spec, invalidate_pages_in_block_spec0 in *. repeat autounfold in *.
    repeat simpl_hyp Hspec; inv Hspec.
    eexists. split. reflexivity. constructor.
    replace (2097152 / 4096) with 512 by reflexivity.
    reflexivity.
  Qed.

End Refine.

