Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RunAux.Spec.
Require Import RunComplete.Specs.complete_mmio_emulation.
Require Import RunComplete.LowSpecs.complete_mmio_emulation.
Require Import RunComplete.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       get_rec_run_is_emulated_mmio_spec
       get_rec_last_run_info_esr_spec
       esr_srt_spec
       esr_is_write_spec
       emulate_mmio_read_spec
       get_rec_pc_spec
       set_rec_pc_spec
    .

  Lemma complete_mmio_emulation_spec_exists:
    forall habd habd'  labd rec res
           (Hspec: complete_mmio_emulation_spec rec habd = Some (habd', res))
            (Hrel: relate_RData habd labd),
    exists labd', complete_mmio_emulation_spec0 rec labd = Some (labd', res) /\ relate_RData habd' labd'.
    Proof.
      intros. destruct Hrel. destruct rec.
      unfold complete_mmio_emulation_spec, complete_mmio_emulation_spec0 in *.
      repeat autounfold in *. simpl in *. unfold ref_accessible in *.
      hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
        repeat destruct_con; repeat destruct_dis; simpl in *; srewrite; repeat simpl_update_reg; simpl;
          repeat (repeat grewrite; simpl; simpl_htarget);
          repeat (solve_bool_range; grewrite; simpl);
          try solve[eexists; split;
                    [reflexivity|
                     constructor; repeat (repeat simpl_field; repeat swap_fields);
                     reflexivity]].
    Qed.

End Refine.

