Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import RmiSMC.Spec.
Require Import TableDataOpsIntro.Spec.
Require Import TableDataSMC.Spec.
Require Import RunSMC.Spec.
Require Import AbsAccessor.Spec.
Require Import SMCHandler.Specs.handle_ns_smc.
Require Import SMCHandler.LowSpecs.handle_ns_smc.
Require Import SMCHandler.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       assert_cond_spec
    .

    Lemma handle_ns_smc_spec_exists:
      forall habd habd'  labd function_id arg0 arg1 arg2 arg3 res
             (Hspec: handle_ns_smc_spec function_id arg0 arg1 arg2 arg3 habd = Some (habd', res))
             (Hrel: relate_RData habd labd),
      exists labd', handle_ns_smc_spec0 function_id arg0 arg1 arg2 arg3 labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    intros. inv Hrel.
    unfold handle_ns_smc_spec, handle_ns_smc_spec0 in *.
    repeat autounfold in *.
    repeat simpl_hyp Hspec; grewrite; destruct res.
    - eexists; split. reflexivity. constructor. reflexivity.
    - extract_if. hsimpl_func Hspec; reflexivity. grewrite.
      eexists; split. reflexivity. constructor. reflexivity.
    - extract_if. hsimpl_func Hspec; reflexivity. grewrite.
      eexists; split. reflexivity. constructor. reflexivity.
    - extract_if. hsimpl_func Hspec; reflexivity. grewrite.
      eexists; split. reflexivity. constructor. reflexivity.
    - extract_if. hsimpl_func Hspec; reflexivity. grewrite.
      eexists; split. reflexivity. constructor. reflexivity.
    - extract_if. hsimpl_func Hspec; reflexivity. grewrite.
      eexists; split. reflexivity. constructor. reflexivity.
    - extract_if. hsimpl_func Hspec; reflexivity. grewrite.
      eexists; split. reflexivity. constructor. reflexivity.
    - extract_if. hsimpl_func Hspec; reflexivity. grewrite.
      eexists; split. reflexivity. constructor. reflexivity.
    - extract_if. hsimpl_func Hspec; reflexivity. grewrite.
      eexists; split. reflexivity. constructor. reflexivity.
    - extract_if. hsimpl_func Hspec; reflexivity. grewrite.
      eexists; split. reflexivity. constructor. reflexivity.
    - extract_if. hsimpl_func Hspec; try reflexivity.
      hsimpl_func H0; reflexivity.
      hsimpl_func H0; reflexivity.
      hsimpl_func H0; reflexivity.
      grewrite.
      eexists; split. reflexivity. constructor. reflexivity.
    - extract_if. hsimpl_func Hspec; try reflexivity.
      hsimpl_func H0; reflexivity.
      hsimpl_func H0; reflexivity.
      hsimpl_func H0; reflexivity.
      grewrite.
      eexists; split. reflexivity. constructor. reflexivity.
    - bool_rel. grewrite. simpl.
      extract_if. hsimpl_func Hspec; try reflexivity.
      hsimpl_func H0; reflexivity.
      hsimpl_func H0; reflexivity.
      grewrite.
      eexists; split. reflexivity. constructor. reflexivity.
    - bool_rel. grewrite. simpl.
      extract_if. hsimpl_func Hspec; try reflexivity.
      hsimpl_func H0; reflexivity.
      hsimpl_func H0; reflexivity.
      grewrite.
      eexists; split. reflexivity. constructor. reflexivity.
  Qed.

End Refine.

