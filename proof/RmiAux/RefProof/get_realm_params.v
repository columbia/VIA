Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RmiAux.Specs.get_realm_params.
Require Import RmiAux.LowSpecs.get_realm_params.
Require Import RmiAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       find_granule_spec
       is_null_spec
       granule_map_spec
       ns_granule_map_spec
       ns_buffer_read_realm_params_spec
       ns_buffer_unmap_spec
       buffer_unmap_spec
    .

  Lemma get_realm_params_spec_exists:
    forall habd habd'  labd realm_params_addr res
           (Hspec: get_realm_params_spec realm_params_addr habd = Some (habd', res))
            (Hrel: relate_RData habd labd),
    exists labd', get_realm_params_spec0 realm_params_addr labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. inv id_rdata.
    unfold get_realm_params_spec, get_realm_params_spec0 in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle;
      extract_prop_dec; repeat destruct_con; repeat destruct_dis; bool_rel; simpl in *;
        repeat (simpl_htarget; grewrite; try solve_ptr_eq; simpl);
        repeat (solve_bool_range; grewrite);
        repeat simpl_field;
        eexists; (split; [reflexivity| constructor; reflexivity]).
  Qed.

End Refine.

