Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RVIC.Specs.rvic_test_flag.
Require Import RVIC.LowSpecs.rvic_test_flag.
Require Import RVIC.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       interrupt_bitmap_dword_spec
       interrupt_bit_spec
       test_bit_acquire_64_spec
       get_bitmap_loc_spec
    .

  Lemma shiftl4:
    forall n, Z.shiftl n 4 = n * 16.
  Proof.
    intros. Local Transparent Z.shiftl.
    unfold Z.shiftl; simpl. omega.
    Local Opaque Z.shiftl.
  Qed.

  Lemma rvic_test_flag_spec_exists:
    forall habd  labd intid bitmap res
           (Hspec: rvic_test_flag_spec intid bitmap habd = Some res)
            (Hrel: relate_RData habd labd),
    rvic_test_flag_spec0 intid bitmap labd = Some res.
  Proof.
    intros. inv Hrel. destruct bitmap.
    unfold rvic_test_flag_spec, rvic_test_flag_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (try simpl_htarget; grewrite; simpl in * );
        (solve_bool_range; grewrite);
        (solve_bool_range; grewrite);
        (solve_bool_range; grewrite);
        rewrite a_plus_16; try omega;
          rewrite a_plus_16'; try omega;
            repeat (try simpl_htarget; grewrite; simpl in * );
            (rewrite shiftl4; solve_bool_range; grewrite);
            (solve_bool_range; grewrite); reflexivity.
  Qed.

End Refine.

