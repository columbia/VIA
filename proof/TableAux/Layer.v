Require Import LayerDeps.
Require Import Ident.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import BaremoreHandler.Spec.
Require Import RmiSMC.Spec.
Require Import RVIC.Spec.
Require Import PendingCheck.Spec.
Require Import CtxtSwitch.Spec.
Require Import RealmExitHandler.Spec.
Require Import RunSMC.Spec.
Require Import TableAux.Spec.

Local Open Scope Z_scope.

Section Layer.

  Context `{real_params: RealParams}.

  Section InvDef.

    Record high_level_invariant (adt: RData) :=
      mkInvariants { }.

    Global Instance TableAux_ops : CompatDataOps RData :=
      {
        empty_data := empty_adt;
        high_level_invariant := high_level_invariant;
        low_level_invariant := fun (b: block) (d: RData) => True;
        kernel_mode adt := True
      }.

  End InvDef.

  Section InvInit.

    Global Instance TableAux_prf : CompatData RData.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvInit.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModelX}.
  Context `{Hmwd: UseMemWithData mem}.

  Section InvProof.

    Global Instance find_next_level_idx_inv: PreservesInvariants find_next_level_idx_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance validate_table_commands_inv: PreservesInvariants validate_table_commands_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance granule_fill_table_inv: PreservesInvariants granule_fill_table_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance table_has_destroyed_inv: PreservesInvariants table_has_destroyed_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance table_maps_block_inv: PreservesInvariants table_maps_block_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance invalidate_page_inv: PreservesInvariants invalidate_page_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance invalidate_block_inv: PreservesInvariants invalidate_block_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance invalidate_pages_in_block_inv: PreservesInvariants invalidate_pages_in_block_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance data_granule_measure_inv: PreservesInvariants data_granule_measure_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance addr_to_idx_inv: PreservesInvariants addr_to_idx_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance el3_sync_lel_inv: PreservesInvariants el3_sync_lel_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_wi_index_inv: PreservesInvariants set_wi_index_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance granule_refcount_inc_inv: PreservesInvariants granule_refcount_inc_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance ns_buffer_write_rec_run_inv: PreservesInvariants ns_buffer_write_rec_run_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance granule_unlock_inv: PreservesInvariants granule_unlock_spec.
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

    Global Instance smc_granule_undelegate_inv: PreservesInvariants smc_granule_undelegate_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance entry_is_table_inv: PreservesInvariants entry_is_table_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance atomic_granule_put_release_inv: PreservesInvariants atomic_granule_put_release_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_rec_destroy_inv: PreservesInvariants smc_rec_destroy_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_cur_rec_inv: PreservesInvariants get_cur_rec_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance clear_realm_stage2_inv: PreservesInvariants clear_realm_stage2_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_rd_g_rtt_inv: PreservesInvariants get_rd_g_rtt_spec.
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

    Global Instance granule_refcount_dec_inv: PreservesInvariants granule_refcount_dec_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance check_pending_ptimers_inv: PreservesInvariants check_pending_ptimers_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance granule_lock_inv: PreservesInvariants granule_lock_spec.
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

    Global Instance restore_ns_state_inv: PreservesInvariants restore_ns_state_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance atomic_granule_put_inv: PreservesInvariants atomic_granule_put_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_rd_state_inv: PreservesInvariants get_rd_state_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance run_realm_inv: PreservesInvariants run_realm_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance handle_realm_exit_inv: PreservesInvariants handle_realm_exit_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_g_rtt_refcount_inv: PreservesInvariants get_g_rtt_refcount_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance restore_hcr_el2_inv: PreservesInvariants restore_hcr_el2_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance check_pending_vtimers_inv: PreservesInvariants check_pending_vtimers_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_realm_activate_inv: PreservesInvariants smc_realm_activate_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_mapping_inv: PreservesInvariants set_mapping_spec.
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

    Global Instance granule_set_state_inv: PreservesInvariants granule_set_state_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance null_ptr_inv: PreservesInvariants null_ptr_spec.
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

    Global Instance get_cur_g_rec_inv: PreservesInvariants get_cur_g_rec_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance granule_map_inv: PreservesInvariants granule_map_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance realm_exit_inv: PreservesInvariants realm_exit_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_rec_run_inv: PreservesInvariants smc_rec_run_spec.
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

    Global Instance set_g_rtt_rd_inv: PreservesInvariants set_g_rtt_rd_spec.
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

    Global Instance pgte_write_inv: PreservesInvariants pgte_write_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_wi_g_llt_inv: PreservesInvariants set_wi_g_llt_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance save_realm_state_inv: PreservesInvariants save_realm_state_spec.
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

    Global Instance entry_to_phys_inv: PreservesInvariants entry_to_phys_spec.
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

    Global Instance link_table_inv: PreservesInvariants link_table_spec.
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

    Definition TableAux_fresh : compatlayer (cdata RData) :=
      _find_next_level_idx ↦ gensem find_next_level_idx_spec
        ⊕ _validate_table_commands ↦ gensem validate_table_commands_spec
        ⊕ _granule_fill_table ↦ gensem granule_fill_table_spec
        ⊕ _table_has_destroyed ↦ gensem table_has_destroyed_spec
        ⊕ _table_maps_block ↦ gensem table_maps_block_spec
        ⊕ _invalidate_page ↦ gensem invalidate_page_spec
        ⊕ _invalidate_block ↦ gensem invalidate_block_spec
        ⊕ _invalidate_pages_in_block ↦ gensem invalidate_pages_in_block_spec
        ⊕ _data_granule_measure ↦ gensem data_granule_measure_spec
      .

    Definition TableAux_passthrough : compatlayer (cdata RData) :=
      _addr_to_idx ↦ gensem addr_to_idx_spec
        ⊕ _el3_sync_lel ↦ gensem el3_sync_lel_spec
        ⊕ _set_wi_index ↦ gensem set_wi_index_spec
        ⊕ _granule_refcount_inc ↦ gensem granule_refcount_inc_spec
        ⊕ _ns_buffer_write_rec_run ↦ gensem ns_buffer_write_rec_run_spec
        ⊕ _granule_unlock ↦ gensem granule_unlock_spec
        ⊕ _granule_put ↦ gensem granule_put_spec
        ⊕ _exit_rmm ↦ gensem exit_rmm_spec
        ⊕ _smc_granule_undelegate ↦ gensem smc_granule_undelegate_spec
        ⊕ _entry_is_table ↦ gensem entry_is_table_spec
        ⊕ _atomic_granule_put_release ↦ gensem atomic_granule_put_release_spec
        ⊕ _smc_rec_destroy ↦ gensem smc_rec_destroy_spec
        ⊕ _get_cur_rec ↦ gensem get_cur_rec_spec
        ⊕ _clear_realm_stage2 ↦ gensem clear_realm_stage2_spec
        ⊕ _get_rd_g_rtt ↦ gensem get_rd_g_rtt_spec
        ⊕ _granule_memzero ↦ gensem granule_memzero_spec
        ⊕ _read_reg ↦ gensem read_reg_spec
        ⊕ _granule_refcount_dec ↦ gensem granule_refcount_dec_spec
        ⊕ _check_pending_ptimers ↦ gensem check_pending_ptimers_spec
        ⊕ _granule_lock ↦ gensem granule_lock_spec
        ⊕ _ns_buffer_unmap ↦ gensem ns_buffer_unmap_spec
        ⊕ _granule_memzero_mapped ↦ gensem granule_memzero_mapped_spec
        ⊕ _restore_ns_state ↦ gensem restore_ns_state_spec
        ⊕ _atomic_granule_put ↦ gensem atomic_granule_put_spec
        ⊕ _get_rd_state ↦ gensem get_rd_state_spec
        ⊕ _run_realm ↦ gensem run_realm_spec
        ⊕ _handle_realm_exit ↦ gensem handle_realm_exit_spec
        ⊕ _get_g_rtt_refcount ↦ gensem get_g_rtt_refcount_spec
        ⊕ _restore_hcr_el2 ↦ gensem restore_hcr_el2_spec
        ⊕ _check_pending_vtimers ↦ gensem check_pending_vtimers_spec
        ⊕ _smc_realm_activate ↦ gensem smc_realm_activate_spec
        ⊕ _set_mapping ↦ gensem set_mapping_spec
        ⊕ _ns_granule_map ↦ gensem ns_granule_map_spec
        ⊕ _granule_get ↦ gensem granule_get_spec
        ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
        ⊕ _enter_rmm ↦ gensem enter_rmm_spec
        ⊕ _smc_granule_delegate ↦ gensem smc_granule_delegate_spec
        ⊕ _granule_set_state ↦ gensem granule_set_state_spec
        ⊕ _null_ptr ↦ gensem null_ptr_spec
        ⊕ _get_wi_g_llt ↦ gensem get_wi_g_llt_spec
        ⊕ _smc_rec_create ↦ gensem smc_rec_create_spec
        ⊕ _get_cur_g_rec ↦ gensem get_cur_g_rec_spec
        ⊕ _granule_map ↦ gensem granule_map_spec
        ⊕ _realm_exit ↦ gensem realm_exit_spec
        ⊕ _smc_rec_run ↦ gensem smc_rec_run_spec
        ⊕ _find_lock_granule ↦ gensem find_lock_granule_spec
        ⊕ _is_null ↦ gensem is_null_spec
        ⊕ _assert_cond ↦ gensem assert_cond_spec
        ⊕ _set_g_rtt_rd ↦ gensem set_g_rtt_rd_spec
        ⊕ _pgte_read ↦ gensem pgte_read_spec
        ⊕ _ns_buffer_read_data ↦ gensem ns_buffer_read_data_spec
        ⊕ _pgte_write ↦ gensem pgte_write_spec
        ⊕ _set_wi_g_llt ↦ gensem set_wi_g_llt_spec
        ⊕ _save_realm_state ↦ gensem save_realm_state_spec
        ⊕ _find_granule ↦ gensem find_granule_spec
        ⊕ _smc_realm_create ↦ gensem smc_realm_create_spec
        ⊕ _entry_to_phys ↦ gensem entry_to_phys_spec
        ⊕ _user_step ↦ gensem user_step_spec
        ⊕ _get_wi_index ↦ gensem get_wi_index_spec
        ⊕ _link_table ↦ gensem link_table_spec
        ⊕ _smc_realm_destroy ↦ gensem smc_realm_destroy_spec
      .

    Definition TableAux := TableAux_fresh ⊕ TableAux_passthrough.

  End LayerDef.

End Layer.
