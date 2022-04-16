Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RmiAux.Specs.validate_realm_params.
Require Import RmiAux.LowSpecs.validate_realm_params.
Require Import RmiAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       get_realm_params_par_base_spec
       get_realm_params_par_size_spec
       max_ipa_size_spec
    .

  Lemma validate_realm_params_spec_exists:
    forall habd  labd  res
           (Hspec: validate_realm_params_spec  habd = Some res)
            (Hrel: relate_RData habd labd),
    validate_realm_params_spec0  labd = Some res.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. inv id_rdata.
    unfold validate_realm_params_spec, validate_realm_params_spec0, valid_realm_params in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle;
      extract_prop_dec; repeat destruct_con; bool_rel; simpl in *;
        repeat (simpl_htarget; grewrite; try solve_ptr_eq; try unfold ref_accessible in *; simpl in *).
    reflexivity.
    repeat (solve_bool_range; grewrite).
    repeat destruct_if; try reflexivity. inv C2.
  Qed.

End Refine.
