Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RmiAux.Specs.init_rec_sysregs.
Require Import RmiAux.LowSpecs.init_rec_sysregs.
Require Import RmiAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       set_rec_sysregs_spec
    .

  Lemma init_rec_sysregs_spec_exists:
    forall habd habd'  labd rec mpidr
           (Hspec: init_rec_sysregs_spec rec mpidr habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', init_rec_sysregs_spec0 rec mpidr labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. inv id_rdata. destruct rec.
    unfold init_rec_sysregs_spec0, init_rec_sysregs_spec in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle;
      extract_prop_dec; repeat destruct_con; repeat destruct_dis; bool_rel; simpl in *;
        repeat (simpl_htarget; grewrite; try solve_ptr_eq; try unfold ref_accessible in *; simpl in *).
    repeat simpl_update_reg.
    eexists; (split; [reflexivity| constructor; reflexivity]).
  Qed.

End Refine.

