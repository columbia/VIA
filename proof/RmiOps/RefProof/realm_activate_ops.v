Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RmiOps.Specs.realm_activate_ops.
Require Import RmiOps.LowSpecs.realm_activate_ops.
Require Import RmiOps.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       measurement_finish_spec
       set_rd_state_spec
    .

  Lemma realm_activate_ops_spec_exists:
    forall habd habd'  labd rd
           (Hspec: realm_activate_ops_spec rd habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', realm_activate_ops_spec0 rd labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    intros. destruct Hrel. inv id_rdata. destruct rd.
    unfold realm_activate_ops_spec0, realm_activate_ops_spec in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; simpl in * );
    eexists; (split; [reflexivity| constructor; try reflexivity]).
  Qed.

End Refine.

