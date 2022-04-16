Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import BaremoreService.Specs.asc_mark_nonsecure.
Require Import BaremoreService.LowSpecs.asc_mark_nonsecure.
Require Import BaremoreService.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       addr_to_gidx_spec
       check_granule_idx_spec
       find_spinlock_spec
       spinlock_acquire_spec
       get_pas_spec
       set_pas_spec
       tlbi_by_pa_spec
       spinlock_release_spec
    .

  Lemma asc_mark_nonsecure_spec_exists:
    forall habd habd'  labd addr res
           (Hspec: asc_mark_nonsecure_spec addr habd = Some (habd', res))
            (Hrel: relate_RData habd labd),
    exists labd', asc_mark_nonsecure_spec0 addr labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    intros. destruct Hrel. inv id_rdata.
    unfold asc_mark_nonsecure_spec0, asc_mark_nonsecure_spec in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl in *;
      extract_prop_dec; repeat destruct_con; bool_rel; simpl in *;
        repeat (simpl_htarget; grewrite; simpl);
        try (destruct_if; repeat destruct_dis; bool_rel; try omega);
        repeat (solve_bool_range; grewrite);
        repeat simpl_field;
        eexists; (split; [reflexivity| constructor; try reflexivity]).
  Qed.

End Refine.

