Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RmiAux2.Specs.rec_granule_measure.
Require Import RmiAux2.LowSpecs.rec_granule_measure.
Require Import RmiAux2.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       measurement_extend_rec_header_spec
       measurement_extend_rec_regs_spec
       measurement_extend_rec_pstate_spec
       measurement_extend_rec_sysregs_spec
    .

  Lemma rec_granule_measure_spec_exists:
    forall habd habd'  labd rd rec data_size
           (Hspec: rec_granule_measure_spec rd rec data_size habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', rec_granule_measure_spec0 rd rec data_size labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    intros. destruct Hrel. inv id_rdata. destruct rd, rec, data_size.
    unfold rec_granule_measure_spec, rec_granule_measure_spec0 in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec; repeat destruct_con; bool_rel; simpl in *;
      assert(H45ne: z2 <> z3) by (red; intro T; inv T; srewrite; omega); assert(H54ne: z3 <> z2) by omega;
        repeat (autounfold; try simpl_loop_add; repeat (simpl_htarget; grewrite; try unfold ref_accessible in *; simpl in *));
                eexists; (split; [reflexivity| constructor; reflexivity]).
  Qed.

End Refine.
