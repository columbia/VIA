Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RunAux.Specs.emulate_mmio_read.
Require Import RunAux.LowSpecs.emulate_mmio_read.
Require Import RunAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       access_mask_spec
       get_rec_run_emulated_read_val_spec
       esr_sign_extend_spec
       access_len_spec
       shiftl_spec
       esr_sixty_four_spec
       set_rec_regs_spec
    .

  Lemma emulate_mmio_read_spec_exists:
    forall habd habd'  labd esr rt rec
      (Hspec: emulate_mmio_read_spec esr rt rec habd = Some habd')
      (Hrel: relate_RData habd labd),
    exists labd', emulate_mmio_read_spec0 esr rt rec labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    intros. destruct Hrel. destruct rec.
    unfold emulate_mmio_read_spec, emulate_mmio_read_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite; repeat simpl_update_reg;
        repeat (simpl_htarget; grewrite; simpl in * );
        repeat (solve_bool_range; grewrite).
    - eexists; split; [reflexivity|constructor; reflexivity].
    - extract_if. bool_rel; omega. grewrite.
      eexists; split; [reflexivity|constructor; reflexivity].
    - extract_if. bool_rel; omega. grewrite.
      repeat (solve_bool_range; grewrite).
      eexists; split; [reflexivity|constructor; reflexivity].
  Qed.

End Refine.

