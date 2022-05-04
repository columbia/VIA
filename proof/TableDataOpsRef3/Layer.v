Require Import LayerDeps.
Require Import Ident.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import TableDataOpsIntro.Spec.
Require Import BaremoreHandler.Spec.
Require Import AbsAccessor.Spec.
Require Import RmiSMC.Spec.
Require Import RunSMC.Spec.
Require Import TableAux.Spec.
Require Import TableDataOpsRef3.Spec.

Local Open Scope Z_scope.

Section Layer.

  Context `{real_params: RealParams}.

  Section InvDef.

    Record high_level_invariant (adt: RData) :=
      mkInvariants { }.

    Global Instance TableDataOpsRef3_ops : CompatDataOps RData :=
      {
        empty_data := empty_adt;
        high_level_invariant := high_level_invariant;
        low_level_invariant := fun (b: block) (d: RData) => True;
        kernel_mode adt := True
      }.

  End InvDef.

  Section InvInit.

    Global Instance TableDataOpsRef3_prf : CompatData RData.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvInit.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModelX}.
  Context `{Hmwd: UseMemWithData mem}.

  Section InvProof.

    Global Instance table_create3_inv: PreservesInvariants table_create3_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance table_destroy3_inv: PreservesInvariants table_destroy3_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance table_map3_inv: PreservesInvariants table_map3_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance table_unmap3_inv: PreservesInvariants table_unmap3_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance data_create3_inv: PreservesInvariants data_create3_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance data_create_unknown3_inv: PreservesInvariants data_create_unknown3_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance data_destroy3_inv: PreservesInvariants data_destroy3_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance data_destroy_inv: PreservesInvariants data_destroy_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance table_create_inv: PreservesInvariants table_create_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance el3_sync_lel_inv: PreservesInvariants el3_sync_lel_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance buffer_unmap_inv: PreservesInvariants buffer_unmap_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance granule_unlock_inv: PreservesInvariants granule_unlock_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance enter_rmm_inv: PreservesInvariants enter_rmm_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance data_create_unknown_inv: PreservesInvariants data_create_unknown_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_granule_delegate_inv: PreservesInvariants smc_granule_delegate_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance table_unmap_inv: PreservesInvariants table_unmap_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance exit_rmm_inv: PreservesInvariants exit_rmm_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance table_destroy_inv: PreservesInvariants table_destroy_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_granule_undelegate_inv: PreservesInvariants smc_granule_undelegate_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance granule_set_state_inv: PreservesInvariants granule_set_state_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance table_map_inv: PreservesInvariants table_map_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_rec_destroy_inv: PreservesInvariants smc_rec_destroy_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_rec_create_inv: PreservesInvariants smc_rec_create_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance granule_map_inv: PreservesInvariants granule_map_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_rec_run_inv: PreservesInvariants smc_rec_run_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance data_create_inv: PreservesInvariants data_create_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance read_reg_inv: PreservesInvariants read_reg_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance find_lock_granule_inv: PreservesInvariants find_lock_granule_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance is_null_inv: PreservesInvariants is_null_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance assert_cond_inv: PreservesInvariants assert_cond_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance validate_table_commands_inv: PreservesInvariants validate_table_commands_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_rd_state_inv: PreservesInvariants get_rd_state_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance find_granule_inv: PreservesInvariants find_granule_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_realm_create_inv: PreservesInvariants smc_realm_create_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance user_step_inv: PreservesInvariants user_step_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_realm_activate_inv: PreservesInvariants smc_realm_activate_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_realm_destroy_inv: PreservesInvariants smc_realm_destroy_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvProof.

  Section LayerDef.

    Definition TableDataOpsRef3_fresh : compatlayer (cdata RData) :=
      _table_create3 ↦ gensem table_create3_spec
        ⊕ _table_destroy3 ↦ gensem table_destroy3_spec
        ⊕ _table_map3 ↦ gensem table_map3_spec
        ⊕ _table_unmap3 ↦ gensem table_unmap3_spec
        ⊕ _data_create3 ↦ gensem data_create3_spec
        ⊕ _data_create_unknown3 ↦ gensem data_create_unknown3_spec
        ⊕ _data_destroy3 ↦ gensem data_destroy3_spec
      .

    Definition TableDataOpsRef3_passthrough : compatlayer (cdata RData) :=
      _data_destroy ↦ gensem data_destroy_spec
        ⊕ _table_create ↦ gensem table_create_spec
        ⊕ _el3_sync_lel ↦ gensem el3_sync_lel_spec
        ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
        ⊕ _granule_unlock ↦ gensem granule_unlock_spec
        ⊕ _enter_rmm ↦ gensem enter_rmm_spec
        ⊕ _data_create_unknown ↦ gensem data_create_unknown_spec
        ⊕ _smc_granule_delegate ↦ gensem smc_granule_delegate_spec
        ⊕ _table_unmap ↦ gensem table_unmap_spec
        ⊕ _exit_rmm ↦ gensem exit_rmm_spec
        ⊕ _table_destroy ↦ gensem table_destroy_spec
        ⊕ _smc_granule_undelegate ↦ gensem smc_granule_undelegate_spec
        ⊕ _granule_set_state ↦ gensem granule_set_state_spec
        ⊕ _table_map ↦ gensem table_map_spec
        ⊕ _smc_rec_destroy ↦ gensem smc_rec_destroy_spec
        ⊕ _smc_rec_create ↦ gensem smc_rec_create_spec
        ⊕ _granule_map ↦ gensem granule_map_spec
        ⊕ _smc_rec_run ↦ gensem smc_rec_run_spec
        ⊕ _data_create ↦ gensem data_create_spec
        ⊕ _read_reg ↦ gensem read_reg_spec
        ⊕ _find_lock_granule ↦ gensem find_lock_granule_spec
        ⊕ _is_null ↦ gensem is_null_spec
        ⊕ _assert_cond ↦ gensem assert_cond_spec
        ⊕ _validate_table_commands ↦ gensem validate_table_commands_spec
        ⊕ _get_rd_state ↦ gensem get_rd_state_spec
        ⊕ _find_granule ↦ gensem find_granule_spec
        ⊕ _smc_realm_create ↦ gensem smc_realm_create_spec
        ⊕ _user_step ↦ gensem user_step_spec
        ⊕ _smc_realm_activate ↦ gensem smc_realm_activate_spec
        ⊕ _smc_realm_destroy ↦ gensem smc_realm_destroy_spec
      .

    Definition TableDataOpsRef3 := TableDataOpsRef3_fresh ⊕ TableDataOpsRef3_passthrough.

  End LayerDef.

End Layer.
