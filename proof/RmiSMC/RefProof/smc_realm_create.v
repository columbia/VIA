Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import RmiAux.Spec.
Require Import AbsAccessor.Spec.
Require Import RmiOps.Spec.
Require Import RmiSMC.Specs.smc_realm_create.
Require Import RmiSMC.LowSpecs.smc_realm_create.
Require Import RmiSMC.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       get_realm_params_spec
       validate_realm_params_spec
       get_realm_params_rtt_addr_spec
       get_realm_params_rec_list_addr_spec
       find_lock_three_delegated_granules_spec
       realm_create_ops_spec
    .

  Lemma smc_realm_create_spec_exists:
    forall habd habd'  labd rd_addr realm_params_addr res
           (Hspec: smc_realm_create_spec rd_addr realm_params_addr habd = Some (habd', res))
            (Hrel: relate_RData habd labd),
    exists labd', smc_realm_create_spec0 rd_addr realm_params_addr labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. inv id_rdata. duplicate valid_o. destruct D.
    unfold smc_realm_create_spec, smc_realm_create_spec0 in *.
    repeat autounfold in *.
    assert (1 <> 2) by omega. assert(0 <> 2) by omega. assert(0 <> 1) by omega.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; simpl in *; srewrite; simpl.
    - unfold valid_realm_params, validate_realm_params.valid_realm_params in *. grewrite. simpl.
      repeat (grewrite; try simpl_htarget; simpl).
      repeat swap_fields; repeat simpl_field; simpl in *.
      eexists; split. reflexivity. constructor; simpl; try assumption.
      repeat (try rewrite (zmap_comm _ _ Prop4);
              try rewrite (zmap_comm _ _ Prop5);
              try rewrite (zmap_comm _ _ Prop6)).
      simpl_htarget. rewrite <- Prop1; simpl_field; rewrite Prop1.
      rewrite <- Prop2; simpl_field; rewrite Prop2, <- Prop3; simpl_field. reflexivity.
    - unfold valid_realm_params, validate_realm_params.valid_realm_params in *. grewrite. simpl.
      repeat (simpl_htarget; grewrite; simpl).
      eexists; split. reflexivity. constructor; simpl; try assumption. reflexivity.
    - unfold valid_realm_params, validate_realm_params.valid_realm_params in *. grewrite. simpl.
      eexists; split. reflexivity. constructor; simpl; try assumption. reflexivity.
    - unfold valid_realm_params, validate_realm_params.valid_realm_params in *. grewrite. simpl.
      eexists; split. reflexivity. constructor; simpl; try assumption. reflexivity.
    - eexists; split. reflexivity. constructor; simpl; try assumption. reflexivity.
    - eexists; split. reflexivity. constructor; simpl; try assumption. reflexivity.
  Qed.

End Refine.

