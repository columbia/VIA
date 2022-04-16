Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import BaremoreSMC.Spec.
Require Import RmiOps.Specs.granule_delegate_ops.
Require Import RmiOps.LowSpecs.granule_delegate_ops.
Require Import RmiOps.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       granule_set_state_spec
       smc_mark_realm_spec
       granule_memzero_spec
       granule_unlock_spec
    .

  Lemma granule_delegate_ops_spec_exists:
    forall habd habd'  labd g addr
           (Hspec: granule_delegate_ops_spec g addr habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', granule_delegate_ops_spec0 g addr labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    intros. destruct Hrel. inv id_rdata. destruct g, addr.
    unfold granule_delegate_ops_spec, granule_delegate_ops_spec0 in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; simpl in *).
    eexists; (split; [reflexivity| constructor; try reflexivity]).
  Qed.

End Refine.

