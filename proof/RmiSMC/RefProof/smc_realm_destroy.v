Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RmiOps.Spec.
Require Import RmiSMC.Specs.smc_realm_destroy.
Require Import RmiSMC.LowSpecs.smc_realm_destroy.
Require Import RmiSMC.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       find_lock_unused_granule_spec
       is_null_spec
       granule_map_spec
       get_rd_g_rtt_spec
       get_rd_g_rec_list_spec
       buffer_unmap_spec
       granule_lock_spec
       get_g_rtt_refcount_spec
       granule_unlock_spec
       realm_destroy_ops_spec
    .

  Lemma smc_realm_destroy_spec_exists:
    forall habd habd'  labd rd_addr res
           (Hspec: smc_realm_destroy_spec rd_addr habd = Some (habd', res))
            (Hrel: relate_RData habd labd),
    exists labd', smc_realm_destroy_spec0 rd_addr labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. inv id_rdata. duplicate valid_o. destruct D.
    unfold smc_realm_destroy_spec, smc_realm_destroy_spec0 in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; simpl in *; srewrite; simpl.
    - assert((__addr_to_gidx z) <> (g_rtt (gnorm (gs s) @ (__addr_to_gidx z)))) by (bool_rel; red; intro T; rewrite <- T in *; omega).
      assert((__addr_to_gidx z) <> (g_rec_list (gnorm (gs s) @ (__addr_to_gidx z)))) by (bool_rel; red; intro T; rewrite <- T in *; omega).
      assert((g_rtt (gnorm (gs s) @ (__addr_to_gidx z))) <> (g_rec_list (gnorm (gs s) @ (__addr_to_gidx z)))) by (bool_rel; red; intro T; rewrite <- T in *; omega).
      match goal with
      | |- context [prop_dec (?a = ?a)] => destruct (prop_dec (a = a)); [ simpl | contra ]
      end.
      repeat (try solve_peq; try solve_ptr_eq; grewrite; simpl). repeat rewrite ZMap.gss; simpl.
      repeat match goal with
             | |- context [prop_dec (?a = ?a)] => destruct (prop_dec (a = a)); [ simpl | contra ]
             end.
      grewrite. repeat (solve_bool_range; grewrite; simpl; try rewrite ZMap.gss).
      repeat (grewrite; try solve_ptr_eq; try solve_peq; try simpl_htarget; simpl).
      simpl_ACQ; simpl.
      repeat (grewrite; try solve_ptr_eq; try solve_peq; try simpl_htarget; simpl).
      erewrite Hright_log_nil. simpl.
      repeat (grewrite; try solve_ptr_eq; try solve_peq; try simpl_htarget; simpl).
      repeat (try rewrite (zmap_comm (__addr_to_gidx z) (g_rtt (gnorm (gs s) @ (__addr_to_gidx z))));
              try rewrite (zmap_comm (__addr_to_gidx z) (g_rec_list (gnorm (gs s) @ (__addr_to_gidx z))));
              try rewrite (zmap_comm (g_rtt (gnorm (gs s) @ (__addr_to_gidx z))) (g_rec_list (gnorm (gs s) @ (__addr_to_gidx z)))));
        try assumption.
      repeat swap_fields; repeat simpl_field; simpl in *.
      eexists; split. reflexivity. constructor; simpl; try assumption.
      simpl_htarget. rewrite <- Prop1; simpl_field; rewrite Prop1.
      rewrite <- Prop6; simpl_field. reflexivity.
      econstructor. eapply ACQ_RightMover. econstructor. eapply ACQ_RightMover. econstructor.
    - match goal with
      | |- context [prop_dec (?a = ?a)] => destruct (prop_dec (a = a)); [ simpl | contra ]
      end.
      repeat (try solve_peq; try solve_ptr_eq; grewrite; simpl). repeat rewrite ZMap.gss; simpl.
      repeat match goal with
             | |- context [prop_dec (?a = ?a)] => destruct (prop_dec (a = a)); [ simpl | contra ]
             end.
      grewrite. repeat (solve_bool_range; grewrite; simpl; try rewrite ZMap.gss).
      simpl_ACQ; simpl.
      assert((__addr_to_gidx z) <> (g_rtt (gnorm (gs s) @ (__addr_to_gidx z)))) by (bool_rel; red; intro T; rewrite <- T in *; omega).
      assert((__addr_to_gidx z) <> (g_rec_list (gnorm (gs s) @ (__addr_to_gidx z)))) by (bool_rel; red; intro T; rewrite <- T in *; omega).
      assert((g_rtt (gnorm (gs s) @ (__addr_to_gidx z))) <> (g_rec_list (gnorm (gs s) @ (__addr_to_gidx z)))) by (bool_rel; red; intro T; rewrite <- T in *; omega).
      repeat (grewrite; try solve_ptr_eq; try solve_peq; try simpl_htarget; simpl).
      repeat swap_fields; repeat simpl_field; simpl in *.
      eexists; split. reflexivity. constructor; simpl; try assumption.
      repeat (try rewrite (zmap_comm (__addr_to_gidx z) (g_rtt (gnorm (gs s) @ (__addr_to_gidx z))));
              try rewrite (zmap_comm (__addr_to_gidx z) (g_rec_list (gnorm (gs s) @ (__addr_to_gidx z))));
              try rewrite (zmap_comm (g_rtt (gnorm (gs s) @ (__addr_to_gidx z))) (g_rec_list (gnorm (gs s) @ (__addr_to_gidx z)))));
        try assumption.
      simpl_htarget. rewrite <- Prop1; simpl_field; rewrite Prop1.
      rewrite <- Prop6; simpl_field. bool_rel. grewrite. rewrite <- C18, <- Prop5.
      repeat simpl_field. simpl_htarget. simpl_field. reflexivity.
    - repeat(match goal with
             | |- context [prop_dec (?a = ?a)] => destruct (prop_dec (a = a)); [ simpl | contra ]
             | _ => try solve_peq; try solve_ptr_eq; grewrite; try rewrite ZMap.gss; simpl
             end).
      repeat destruct_dis; repeat destruct_con; repeat (simpl_htarget; grewrite; simpl);
        repeat swap_fields; repeat simpl_field; simpl in *; simpl_htarget;
        (eexists; split; [reflexivity| constructor; simpl; try assumption; reflexivity]).
    - repeat(match goal with
             | |- context [prop_dec (?a = ?a)] => destruct (prop_dec (a = a)); [ simpl | contra ]
             | _ => try solve_peq; try solve_ptr_eq; grewrite; try rewrite ZMap.gss; simpl
             end).
      repeat destruct_dis; repeat destruct_con; repeat (simpl_htarget; grewrite; simpl);
        repeat swap_fields; repeat simpl_field; simpl in *; simpl_htarget;
        (eexists; split; [reflexivity| constructor; simpl; try assumption; reflexivity]).
  Qed.

End Refine.

