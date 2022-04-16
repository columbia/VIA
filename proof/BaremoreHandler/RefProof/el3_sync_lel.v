Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import BaremoreService.Spec.
Require Import BaremoreHandler.Specs.el3_sync_lel.
Require Import BaremoreHandler.LowSpecs.el3_sync_lel.
Require Import BaremoreHandler.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       baremore_enter_spec
       get_monitor_call_arg_spec
       asc_mark_realm_spec
       baremore_return_rmm_spec
       asc_mark_nonsecure_spec
       baremore_to_ns_spec
       baremore_to_rmm_spec
       assert_cond_spec
    .

  Lemma el3_sync_lel_spec_exists:
    forall habd habd'  labd
           (Hspec: el3_sync_lel_spec  habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', el3_sync_lel_spec0  labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    intros. destruct Hrel. inv id_rdata.
    unfold el3_sync_lel_spec0, el3_sync_lel_spec in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle;
      extract_prop_dec; repeat destruct_con; bool_rel; simpl in *;
        repeat (simpl_htarget; grewrite; simpl);
        repeat simpl_field;
        eexists; (split; [reflexivity | constructor; reflexivity]).
  Qed.

End Refine.

