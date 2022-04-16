Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RunAux.Specs.reset_last_run_info.
Require Import RunAux.LowSpecs.reset_last_run_info.
Require Import RunAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       set_rec_last_run_info_esr_spec
  .

  Lemma reset_last_run_info_spec_exists:
    forall habd habd'  labd rec
           (Hspec: reset_last_run_info_spec rec habd = Some habd')
           (Hrel: relate_RData habd labd),
    exists labd', reset_last_run_info_spec0 rec labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    intros. inv Hrel. destruct rec.
    unfold reset_last_run_info_spec, reset_last_run_info_spec0 in *.
    repeat autounfold in *. simpl in *. grewrite.
    eexists; split. reflexivity. constructor; reflexivity.
  Qed.

End Refine.

