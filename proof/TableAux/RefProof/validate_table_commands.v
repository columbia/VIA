Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import TableAux.Specs.validate_table_commands.
Require Import TableAux.LowSpecs.validate_table_commands.
Require Import TableAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       addr_is_level_aligned_spec
    .

  Lemma validate_table_commands_spec_exists:
    forall habd  labd map_addr level min_level max_level index res
           (Hspec: validate_table_commands_spec map_addr level min_level max_level index habd = Some res)
            (Hrel: relate_RData habd labd),
    validate_table_commands_spec0 map_addr level min_level max_level index labd = Some res.
  Proof.
    intros. inv Hrel.
    unfold validate_table_commands_spec, validate_table_commands_spec0 in *. autounfold in *.
    repeat simpl_hyp Hspec; inv Hspec; repeat destruct_con; bool_rel; grewrite.
    repeat destruct_if; bool_rel; try reflexivity; try omega.
    repeat destruct_dis; repeat destruct_con; bool_rel; grewrite;
      repeat destruct_if; bool_rel; try reflexivity; try omega.
  Qed.

End Refine.

