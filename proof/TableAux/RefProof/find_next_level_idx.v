Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import TableAux.Specs.find_next_level_idx.
Require Import TableAux.LowSpecs.find_next_level_idx.
Require Import TableAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       granule_map_spec
       pgte_read_spec
       buffer_unmap_spec
       entry_is_table_spec
       null_ptr_spec
       find_granule_spec
       entry_to_phys_spec
    .

  Lemma find_next_level_idx_spec_exists:
    forall habd habd'  labd g_tbl idx res
           (Hspec: find_next_level_idx_spec g_tbl idx habd = Some (habd', res))
            (Hrel: relate_RData habd labd),
    exists labd', find_next_level_idx_spec0 g_tbl idx labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    intros. destruct Hrel. inv id_rdata. destruct g_tbl.
    unfold find_next_level_idx_spec0, find_next_level_idx_spec in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl in *.
    - extract_prop_dec; repeat destruct_con; bool_rel; simpl in *. solve_peq; simpl.
      simpl_htarget; grewrite; simpl. solve_bool_range; grewrite.
      eexists. split. reflexivity. constructor. repeat simpl_field. reflexivity.
    - extract_prop_dec; repeat destruct_con; bool_rel; simpl in *. solve_peq; simpl.
      simpl_htarget; grewrite; simpl.
      repeat destruct_if; try discriminate; repeat simpl_field; try (eexists; split; [reflexivity|constructor;reflexivity]).
  Qed.

End Refine.

