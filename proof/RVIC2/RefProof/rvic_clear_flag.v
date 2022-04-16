Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RVIC2.Specs.rvic_clear_flag.
Require Import RVIC2.LowSpecs.rvic_clear_flag.
Require Import RVIC2.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       interrupt_bitmap_dword_spec
       interrupt_bit_spec
       get_bitmap_loc_spec
       atomic_bit_clear_release_64_spec
    .

  Lemma shiftl4:
    forall n, Z.shiftl n 4 = n * 16.
  Proof.
    intros. Local Transparent Z.shiftl.
    unfold Z.shiftl; simpl. omega.
    Local Opaque Z.shiftl.
  Qed.

  Lemma rvic_clear_flag_spec_exists:
    forall habd habd'  labd intid bitmap
      (Hspec: rvic_clear_flag_spec intid bitmap habd = Some habd')
      (Hrel: relate_RData habd labd),
    exists labd', rvic_clear_flag_spec0 intid bitmap labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    intros. inv Hrel. destruct bitmap.
    unfold rvic_clear_flag_spec, rvic_clear_flag_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; simpl in * ).
    - (solve_bool_range; grewrite). (solve_bool_range; grewrite). (solve_bool_range; grewrite).
      extract_if. rewrite shiftl4. apply andb_true_iff; split; bool_rel; omega. grewrite.
      (solve_bool_range; grewrite). rewrite a_plus_16; try omega.
      repeat (simpl_htarget; grewrite; simpl in * ).
      eexists; split. reflexivity. constructor.
      rewrite a_plus_16'; try omega. reflexivity.
    - (solve_bool_range; grewrite). (solve_bool_range; grewrite). (solve_bool_range; grewrite).
      extract_if. rewrite shiftl4. apply andb_true_iff; split; bool_rel; omega. grewrite.
      (solve_bool_range; grewrite). rewrite a_plus_16; try omega.
      repeat (simpl_htarget; grewrite; simpl in * ).
      eexists; split. reflexivity. constructor.
      rewrite a_plus_16'; try omega. reflexivity.
  Qed.

End Refine.

