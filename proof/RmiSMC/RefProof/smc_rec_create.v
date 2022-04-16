Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RmiOps.Spec.
Require Import RmiSMC.Specs.smc_rec_create.
Require Import RmiSMC.LowSpecs.smc_rec_create.
Require Import RmiSMC.Specs.smc_rec_destroy.
Require Import RmiSMC.LowSpecs.smc_rec_destroy.
Require Import RmiSMC.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       find_lock_unused_granule_spec
       is_null_spec
       rec_destroy_ops_spec
    .

  Lemma smc_rec_destroy_spec_exists:
    forall habd habd'  labd rec_addr res
           (Hspec: smc_rec_destroy_spec rec_addr habd = Some (habd', res))
            (Hrel: relate_RData habd labd),
    exists labd', smc_rec_destroy_spec0 rec_addr labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. inv id_rdata. duplicate valid_o. destruct D.
    unfold smc_rec_destroy_spec, smc_rec_destroy_spec0 in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; simpl in *; srewrite; simpl.
    - assert((__addr_to_gidx z) <> (g_rd (ginfo (gs s) @ (__addr_to_gidx z)))) by (bool_rel; red; intro T; rewrite <- T in *; omega).
      assert((__addr_to_gidx z) <> (g_rec_rec_list (grec (gs s) @ (__addr_to_gidx z)))) by (bool_rel; red; intro T; rewrite <- T in *; omega).
      assert((g_rd (ginfo (gs s) @ (__addr_to_gidx z))) <> (g_rec_rec_list (grec (gs s) @ (__addr_to_gidx z)))) by (bool_rel; red; intro T; rewrite <- T in *; omega).
      repeat (simpl_htarget; grewrite; simpl).
      solve_ptr_eq. simpl.
      repeat (try rewrite (zmap_comm (__addr_to_gidx z) (g_rd (ginfo (gs s) @ (__addr_to_gidx z))));
              try rewrite (zmap_comm (__addr_to_gidx z) (g_rec_rec_list (grec (gs s) @ (__addr_to_gidx z))));
              try rewrite (zmap_comm (g_rd (ginfo (gs s) @ (__addr_to_gidx z))) (g_rec_rec_list (grec (gs s) @ (__addr_to_gidx z)))));
        try assumption.
      repeat swap_fields; repeat simpl_field; simpl in *.
      eexists; split. reflexivity. constructor; simpl; try assumption.
      simpl_htarget. rewrite <- Prop4; simpl_field. reflexivity.
    - repeat (simpl_htarget; grewrite; simpl).
      repeat destruct_dis; repeat destruct_con; repeat (simpl_htarget; grewrite; simpl);
        repeat swap_fields; repeat simpl_field; simpl in *; simpl_htarget;
        (eexists; split; [reflexivity| constructor; simpl; try assumption; reflexivity]).
    - repeat (simpl_htarget; grewrite; simpl).
      repeat destruct_dis; repeat destruct_con; repeat (simpl_htarget; grewrite; simpl);
        repeat swap_fields; repeat simpl_field; simpl in *; simpl_htarget;
        (eexists; split; [reflexivity| constructor; simpl; try assumption; reflexivity]).
  Qed.

End Refine.

