Require Import LayerDeps.
Require Import Ident.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import BaremoreHandler.Spec.
Require Import TableAux3.Spec.
Require Import RmiSMC.Spec.
Require Import TableAux.Spec.
Require Import RunSMC.Spec.
Require Import TableWalk.Spec.

Local Open Scope Z_scope.

Section Layer.

  Context `{real_params: RealParams}.

  Section InvDef.

    Record high_level_invariant (adt: RData) :=
      mkInvariants { }.

    Global Instance TableWalk_ops : CompatDataOps RData :=
      {
        empty_data := empty_adt;
        high_level_invariant := high_level_invariant;
        low_level_invariant := fun (b: block) (d: RData) => True;
        kernel_mode adt := True
      }.

  End InvDef.

  Section InvInit.

    Global Instance TableWalk_prf : CompatData RData.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvInit.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModelX}.
  Context `{Hmwd: UseMemWithData mem}.

  Section InvProof.

    Global Instance table_walk_lock_unlock_inv: PreservesInvariants table_walk_lock_unlock_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_mapping_inv: PreservesInvariants set_mapping_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance el3_sync_lel_inv: PreservesInvariants el3_sync_lel_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance ns_granule_map_inv: PreservesInvariants ns_granule_map_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance granule_get_inv: PreservesInvariants granule_get_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance buffer_unmap_inv: PreservesInvariants buffer_unmap_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance table_destroy_aux_inv: PreservesInvariants table_destroy_aux_spec.
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

    Global Instance smc_granule_delegate_inv: PreservesInvariants smc_granule_delegate_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance granule_put_inv: PreservesInvariants granule_put_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance exit_rmm_inv: PreservesInvariants exit_rmm_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance invalidate_page_inv: PreservesInvariants invalidate_page_spec.
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

    Global Instance entry_is_table_inv: PreservesInvariants entry_is_table_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_rec_destroy_inv: PreservesInvariants smc_rec_destroy_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_wi_g_llt_inv: PreservesInvariants get_wi_g_llt_spec.
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

    Global Instance invalidate_block_inv: PreservesInvariants invalidate_block_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance granule_memzero_inv: PreservesInvariants granule_memzero_spec.
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

    Global Instance ns_buffer_unmap_inv: PreservesInvariants ns_buffer_unmap_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance granule_memzero_mapped_inv: PreservesInvariants granule_memzero_mapped_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance pgte_read_inv: PreservesInvariants pgte_read_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance ns_buffer_read_data_inv: PreservesInvariants ns_buffer_read_data_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance table_create_aux_inv: PreservesInvariants table_create_aux_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance pgte_write_inv: PreservesInvariants pgte_write_spec.
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

    Global Instance get_wi_index_inv: PreservesInvariants get_wi_index_spec.
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

    Definition TableWalk_fresh : compatlayer (cdata RData) :=
      _table_walk_lock_unlock ↦ gensem table_walk_lock_unlock_spec
      .

    Definition TableWalk_passthrough : compatlayer (cdata RData) :=
      _set_mapping ↦ gensem set_mapping_spec
        ⊕ _el3_sync_lel ↦ gensem el3_sync_lel_spec
        ⊕ _ns_granule_map ↦ gensem ns_granule_map_spec
        ⊕ _granule_get ↦ gensem granule_get_spec
        ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
        ⊕ _table_destroy_aux ↦ gensem table_destroy_aux_spec
        ⊕ _granule_unlock ↦ gensem granule_unlock_spec
        ⊕ _enter_rmm ↦ gensem enter_rmm_spec
        ⊕ _smc_granule_delegate ↦ gensem smc_granule_delegate_spec
        ⊕ _granule_put ↦ gensem granule_put_spec
        ⊕ _exit_rmm ↦ gensem exit_rmm_spec
        ⊕ _invalidate_page ↦ gensem invalidate_page_spec
        ⊕ _smc_granule_undelegate ↦ gensem smc_granule_undelegate_spec
        ⊕ _granule_set_state ↦ gensem granule_set_state_spec
        ⊕ _entry_is_table ↦ gensem entry_is_table_spec
        ⊕ _smc_rec_destroy ↦ gensem smc_rec_destroy_spec
        ⊕ _get_wi_g_llt ↦ gensem get_wi_g_llt_spec
        ⊕ _smc_rec_create ↦ gensem smc_rec_create_spec
        ⊕ _granule_map ↦ gensem granule_map_spec
        ⊕ _smc_rec_run ↦ gensem smc_rec_run_spec
        ⊕ _invalidate_block ↦ gensem invalidate_block_spec
        ⊕ _granule_memzero ↦ gensem granule_memzero_spec
        ⊕ _read_reg ↦ gensem read_reg_spec
        ⊕ _find_lock_granule ↦ gensem find_lock_granule_spec
        ⊕ _is_null ↦ gensem is_null_spec
        ⊕ _assert_cond ↦ gensem assert_cond_spec
        ⊕ _ns_buffer_unmap ↦ gensem ns_buffer_unmap_spec
        ⊕ _granule_memzero_mapped ↦ gensem granule_memzero_mapped_spec
        ⊕ _pgte_read ↦ gensem pgte_read_spec
        ⊕ _ns_buffer_read_data ↦ gensem ns_buffer_read_data_spec
        ⊕ _table_create_aux ↦ gensem table_create_aux_spec
        ⊕ _pgte_write ↦ gensem pgte_write_spec
        ⊕ _validate_table_commands ↦ gensem validate_table_commands_spec
        ⊕ _get_rd_state ↦ gensem get_rd_state_spec
        ⊕ _find_granule ↦ gensem find_granule_spec
        ⊕ _smc_realm_create ↦ gensem smc_realm_create_spec
        ⊕ _user_step ↦ gensem user_step_spec
        ⊕ _get_wi_index ↦ gensem get_wi_index_spec
        ⊕ _smc_realm_activate ↦ gensem smc_realm_activate_spec
        ⊕ _smc_realm_destroy ↦ gensem smc_realm_destroy_spec
      .

    Definition TableWalk := TableWalk_fresh ⊕ TableWalk_passthrough.

  End LayerDef.

End Layer.
