Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import BaremoreHandler.Spec.
Require Import BaremoreSMC.Specs.smc_mark_realm.
Require Import BaremoreSMC.LowSpecs.smc_mark_realm.
Require Import BaremoreSMC.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       set_monitor_call_spec
       el3_sync_lel_spec
       get_monitor_call_ret_spec
       assert_cond_spec
    .

  Lemma smc_mark_realm_spec_exists:
    forall habd habd'  labd addr
           (Hspec: smc_mark_realm_spec addr habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', smc_mark_realm_spec0 addr labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Transparent Z.land Z.add.
    intros. destruct Hrel. inv id_rdata.
    unfold smc_mark_realm_spec0, smc_mark_realm_spec in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle;
      extract_prop_dec; repeat destruct_con; bool_rel; simpl in *;
        repeat (simpl_htarget; grewrite; simpl).
    solve_bool_range; grewrite; simpl.
    repeat simpl_field.
    eexists; (split; [reflexivity | constructor; reflexivity]).
  Qed.

End Refine.

