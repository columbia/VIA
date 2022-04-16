Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RmiAux2.Specs.init_rec_rvic_state.
Require Import RmiAux2.LowSpecs.init_rec_rvic_state.
Require Import RmiAux2.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       set_rvic_mask_bits_spec
    .

  Lemma init_rec_rvic_state_spec_exists:
    forall habd habd'  labd rvic
           (Hspec: init_rec_rvic_state_spec rvic habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', init_rec_rvic_state_spec0 rvic labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. inv id_rdata. destruct rvic.
    unfold init_rec_rvic_state_spec0, init_rec_rvic_state_spec in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle;
      extract_prop_dec; repeat destruct_con; bool_rel; simpl in *;
        repeat (autounfold; try simpl_loop_add;
                repeat (simpl_htarget; repeat simpl_update_reg; repeat simpl_field; repeat swap_fields;
                        grewrite; try unfold ref_accessible in *; simpl in *)).
    eexists; split. reflexivity. constructor; reflexivity.
  Qed.

End Refine.
