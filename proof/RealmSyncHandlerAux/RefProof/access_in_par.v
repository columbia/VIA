Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RealmSyncHandlerAux.Specs.access_in_par.
Require Import RealmSyncHandlerAux.LowSpecs.access_in_par.
Require Import RealmSyncHandlerAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       get_rec_par_end_spec
       access_len_spec
       get_rec_par_base_spec
    .

  Lemma access_in_par_spec_exists:
    forall habd  labd rec address esr res
      (Hspec: access_in_par_spec rec address esr habd = Some res)
      (Hrel: relate_RData habd labd),
      access_in_par_spec0 rec address esr labd = Some res.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. destruct rec.
    unfold access_in_par_spec, access_in_par_spec0 in *.
    repeat autounfold in *. simpl in *; unfold ref_accessible in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; repeat destruct_dis; simpl in *; srewrite;
        repeat (repeat grewrite; simpl; repeat simpl_update_reg; simpl; try rewrite ZMap.gss; simpl;
                repeat (solve_bool_range; grewrite; simpl)); try reflexivity.
  Qed.

End Refine.

