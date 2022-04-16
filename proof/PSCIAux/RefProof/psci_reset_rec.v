Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import PSCIAux.Specs.psci_reset_rec.
Require Import PSCIAux.LowSpecs.psci_reset_rec.
Require Import PSCIAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       set_rec_pstate_spec
       set_rec_sysregs_spec
       get_rec_sysregs_spec
    .

  Lemma psci_reset_rec_spec_exists:
    forall habd habd'  labd rec target_rec
           (Hspec: psci_reset_rec_spec rec target_rec habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', psci_reset_rec_spec0 rec target_rec labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. destruct rec, target_rec.
    unfold psci_reset_rec_spec, psci_reset_rec_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; simpl in * ).
    unfold ref_accessible in *; simpl in *.
    repeat (simpl_htarget; repeat simpl_update_reg; grewrite; simpl in * ).
    repeat (solve_bool_range; grewrite).
    eexists; split. reflexivity. constructor. reflexivity.
  Qed.

End Refine.

