Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RealmSyncHandlerAux.Specs.get_write_value.
Require Import RealmSyncHandlerAux.LowSpecs.get_write_value.
Require Import RealmSyncHandlerAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       esr_srt_spec
       access_mask_spec
       get_rec_regs_spec
    .

  Lemma get_write_value_spec_exists:
    forall habd  labd rec esr res
      (Hspec: get_write_value_spec rec esr habd = Some res)
      (Hrel: relate_RData habd labd),
      get_write_value_spec0 rec esr labd = Some res.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. destruct rec.
    unfold get_write_value_spec, get_write_value_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; simpl in *; srewrite; repeat simpl_update_reg;
        repeat (simpl_htarget; grewrite; simpl in *; try solve_bool_range); try reflexivity.
  Qed.

End Refine.

