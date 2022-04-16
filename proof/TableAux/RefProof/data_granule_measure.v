Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import TableAux.Specs.data_granule_measure.
Require Import TableAux.LowSpecs.data_granule_measure.
Require Import TableAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       measurement_extend_data_spec
       measurement_extend_data_header_spec
    .

  Lemma data_granule_measure_spec_exists:
    forall habd habd'  labd rd data offset data_size
           (Hspec: data_granule_measure_spec rd data offset data_size habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', data_granule_measure_spec0 rd data offset data_size labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    intros. destruct Hrel. inv id_rdata. destruct rd, data.
    unfold data_granule_measure_spec0, data_granule_measure_spec in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl in *.
    extract_prop_dec; repeat destruct_con; bool_rel; simpl in *.
    simpl_htarget; grewrite; simpl.
    destruct_if; repeat (simpl_htarget; grewrite).
    rewrite ZMap.gso. simpl_htarget.
    eexists. split. reflexivity. constructor. reflexivity.
    red; intro T; inv T. srewrite. match goal with | [H: 4 = 2 |- _] => inv H end.
    eexists. split. reflexivity. constructor. repeat (simpl_field; simpl_htarget). reflexivity.
  Qed.

End Refine.

