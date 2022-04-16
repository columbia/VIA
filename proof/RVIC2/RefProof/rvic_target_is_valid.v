Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import RVIC2.Specs.rvic_target_is_valid.
Require Import RVIC2.LowSpecs.rvic_target_is_valid.
Require Import RVIC2.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Lemma rvic_target_is_valid_spec_exists:
    forall habd  labd target res
           (Hspec: rvic_target_is_valid_spec target habd = Some res)
            (Hrel: relate_RData habd labd),
    rvic_target_is_valid_spec0 target labd = Some res.
  Proof.
    intros. inv Hrel.
    unfold rvic_target_is_valid_spec, rvic_target_is_valid_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; simpl in * ); reflexivity.
  Qed.

End Refine.

