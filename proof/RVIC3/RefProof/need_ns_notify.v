Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RVIC2.Spec.
Require Import RVIC3.Specs.need_ns_notify.
Require Import RVIC3.LowSpecs.need_ns_notify.
Require Import RVIC3.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       get_rec_rec_idx_spec
       get_rec_rvic_enabled_spec
       get_rec_rvic_spec
       rvic_is_pending_spec
       rvic_is_masked_spec
    .

  Lemma need_ns_notify_spec_exists:
    forall habd  labd rec target_rec intid res
           (Hspec: need_ns_notify_spec rec target_rec intid habd = Some res)
            (Hrel: relate_RData habd labd),
    need_ns_notify_spec0 rec target_rec intid labd = Some res.
  Proof.
    intros. inv Hrel. destruct rec, target_rec.
    unfold need_ns_notify_spec, need_ns_notify_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; simpl in * );
        repeat (solve_bool_range; grewrite); try solve_peq;
        reflexivity.
  Qed.

End Refine.

