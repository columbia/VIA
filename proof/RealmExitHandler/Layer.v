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
Require Import CtxtSwitch.Spec.
Require Import RealmExitHandler.Spec.

Local Open Scope Z_scope.

Section Layer.

  Context `{real_params: RealParams}.

  Section InvDef.

    Record high_level_invariant (adt: RData) :=
      mkInvariants { }.

    Global Instance RealmExitHandler_ops : CompatDataOps RData :=
      {
        empty_data := empty_adt;
        high_level_invariant := high_level_invariant;
        low_level_invariant := fun (b: block) (d: RData) => True;
        kernel_mode adt := True
      }.

  End InvDef.

  Section InvInit.

    Global Instance RealmExitHandler_prf : CompatData RData.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvInit.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModelX}.
  Context `{Hmwd: UseMemWithData mem}.

  Section InvProof.

    Global Instance handle_realm_exit_inv: PreservesInvariants handle_realm_exit_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance shiftl_inv: PreservesInvariants shiftl_spec.
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

    Global Instance granule_unlock_inv: PreservesInvariants granule_unlock_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance ns_buffer_read_rec_run_inv: PreservesInvariants ns_buffer_read_rec_run_spec.
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

    Global Instance measurement_extend_data_inv: PreservesInvariants measurement_extend_data_spec.
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

    Global Instance barrier_inv: PreservesInvariants barrier_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance access_mask_inv: PreservesInvariants access_mask_spec.
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

    Global Instance configure_realm_stage2_inv: PreservesInvariants configure_realm_stage2_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_rec_run_gprs_inv: PreservesInvariants get_rec_run_gprs_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance esr_sign_extend_inv: PreservesInvariants esr_sign_extend_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_rec_dispose_pending_inv: PreservesInvariants set_rec_dispose_pending_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_rd_g_rtt_inv: PreservesInvariants get_rd_g_rtt_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_rec_last_run_info_esr_inv: PreservesInvariants set_rec_last_run_info_esr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_rec_run_is_emulated_mmio_inv: PreservesInvariants get_rec_run_is_emulated_mmio_spec.
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

    Global Instance measurement_extend_data_header_inv: PreservesInvariants measurement_extend_data_header_spec.
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

    Global Instance esr_sixty_four_inv: PreservesInvariants esr_sixty_four_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance run_realm_inv: PreservesInvariants run_realm_spec.
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

    Global Instance esr_srt_inv: PreservesInvariants esr_srt_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_realm_activate_inv: PreservesInvariants smc_realm_activate_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_rec_pc_inv: PreservesInvariants get_rec_pc_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_mapping_inv: PreservesInvariants set_mapping_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_rec_pc_inv: PreservesInvariants set_rec_pc_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance set_rec_regs_inv: PreservesInvariants set_rec_regs_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance get_rec_runnable_inv: PreservesInvariants get_rec_runnable_spec.
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

    Global Instance access_len_inv: PreservesInvariants access_len_spec.
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

    Global Instance get_rec_run_emulated_read_val_inv: PreservesInvariants get_rec_run_emulated_read_val_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance save_ns_state_inv: PreservesInvariants save_ns_state_spec.
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

    Global Instance granule_map_inv: PreservesInvariants granule_map_spec.
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

    Global Instance get_rec_last_run_info_esr_inv: PreservesInvariants get_rec_last_run_info_esr_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance find_granule_inv: PreservesInvariants find_granule_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance restore_realm_state_inv: PreservesInvariants restore_realm_state_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance esr_is_write_inv: PreservesInvariants esr_is_write_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_realm_create_inv: PreservesInvariants smc_realm_create_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance find_lock_unused_granule_inv: PreservesInvariants find_lock_unused_granule_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance entry_to_phys_inv: PreservesInvariants entry_to_phys_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance stage2_tlbi_ipa_inv: PreservesInvariants stage2_tlbi_ipa_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance atomic_granule_get_inv: PreservesInvariants atomic_granule_get_spec.
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

    Global Instance addr_is_level_aligned_inv: PreservesInvariants addr_is_level_aligned_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvProof.

  Section LayerDef.

    Definition RealmExitHandler_fresh : compatlayer (cdata RData) :=
      _handle_realm_exit ↦ gensem handle_realm_exit_spec
      .

    Definition RealmExitHandler_passthrough : compatlayer (cdata RData) :=
      _shiftl ↦ gensem shiftl_spec
        ⊕ _addr_to_idx ↦ gensem addr_to_idx_spec
        ⊕ _el3_sync_lel ↦ gensem el3_sync_lel_spec
        ⊕ _set_wi_index ↦ gensem set_wi_index_spec
        ⊕ _granule_refcount_inc ↦ gensem granule_refcount_inc_spec
        ⊕ _granule_unlock ↦ gensem granule_unlock_spec
        ⊕ _ns_buffer_read_rec_run ↦ gensem ns_buffer_read_rec_run_spec
        ⊕ _granule_put ↦ gensem granule_put_spec
        ⊕ _exit_rmm ↦ gensem exit_rmm_spec
        ⊕ _measurement_extend_data ↦ gensem measurement_extend_data_spec
        ⊕ _smc_granule_undelegate ↦ gensem smc_granule_undelegate_spec
        ⊕ _entry_is_table ↦ gensem entry_is_table_spec
        ⊕ _barrier ↦ gensem barrier_spec
        ⊕ _access_mask ↦ gensem access_mask_spec
        ⊕ _atomic_granule_put_release ↦ gensem atomic_granule_put_release_spec
        ⊕ _smc_rec_destroy ↦ gensem smc_rec_destroy_spec
        ⊕ _configure_realm_stage2 ↦ gensem configure_realm_stage2_spec
        ⊕ _get_rec_run_gprs ↦ gensem get_rec_run_gprs_spec
        ⊕ _esr_sign_extend ↦ gensem esr_sign_extend_spec
        ⊕ _set_rec_dispose_pending ↦ gensem set_rec_dispose_pending_spec
        ⊕ _get_rd_g_rtt ↦ gensem get_rd_g_rtt_spec
        ⊕ _set_rec_last_run_info_esr ↦ gensem set_rec_last_run_info_esr_spec
        ⊕ _get_rec_run_is_emulated_mmio ↦ gensem get_rec_run_is_emulated_mmio_spec
        ⊕ _granule_memzero ↦ gensem granule_memzero_spec
        ⊕ _read_reg ↦ gensem read_reg_spec
        ⊕ _granule_refcount_dec ↦ gensem granule_refcount_dec_spec
        ⊕ _measurement_extend_data_header ↦ gensem measurement_extend_data_header_spec
        ⊕ _granule_lock ↦ gensem granule_lock_spec
        ⊕ _ns_buffer_unmap ↦ gensem ns_buffer_unmap_spec
        ⊕ _granule_memzero_mapped ↦ gensem granule_memzero_mapped_spec
        ⊕ _atomic_granule_put ↦ gensem atomic_granule_put_spec
        ⊕ _get_rd_state ↦ gensem get_rd_state_spec
        ⊕ _esr_sixty_four ↦ gensem esr_sixty_four_spec
        ⊕ _run_realm ↦ gensem run_realm_spec
        ⊕ _get_g_rtt_refcount ↦ gensem get_g_rtt_refcount_spec
        ⊕ _restore_hcr_el2 ↦ gensem restore_hcr_el2_spec
        ⊕ _esr_srt ↦ gensem esr_srt_spec
        ⊕ _smc_realm_activate ↦ gensem smc_realm_activate_spec
        ⊕ _get_rec_pc ↦ gensem get_rec_pc_spec
        ⊕ _set_mapping ↦ gensem set_mapping_spec
        ⊕ _set_rec_pc ↦ gensem set_rec_pc_spec
        ⊕ _set_rec_regs ↦ gensem set_rec_regs_spec
        ⊕ _get_rec_runnable ↦ gensem get_rec_runnable_spec
        ⊕ _ns_granule_map ↦ gensem ns_granule_map_spec
        ⊕ _granule_get ↦ gensem granule_get_spec
        ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
        ⊕ _access_len ↦ gensem access_len_spec
        ⊕ _enter_rmm ↦ gensem enter_rmm_spec
        ⊕ _smc_granule_delegate ↦ gensem smc_granule_delegate_spec
        ⊕ _get_rec_run_emulated_read_val ↦ gensem get_rec_run_emulated_read_val_spec
        ⊕ _save_ns_state ↦ gensem save_ns_state_spec
        ⊕ _granule_set_state ↦ gensem granule_set_state_spec
        ⊕ _null_ptr ↦ gensem null_ptr_spec
        ⊕ _get_wi_g_llt ↦ gensem get_wi_g_llt_spec
        ⊕ _smc_rec_create ↦ gensem smc_rec_create_spec
        ⊕ _granule_map ↦ gensem granule_map_spec
        ⊕ _find_lock_granule ↦ gensem find_lock_granule_spec
        ⊕ _is_null ↦ gensem is_null_spec
        ⊕ _assert_cond ↦ gensem assert_cond_spec
        ⊕ _set_g_rtt_rd ↦ gensem set_g_rtt_rd_spec
        ⊕ _pgte_read ↦ gensem pgte_read_spec
        ⊕ _ns_buffer_read_data ↦ gensem ns_buffer_read_data_spec
        ⊕ _pgte_write ↦ gensem pgte_write_spec
        ⊕ _set_wi_g_llt ↦ gensem set_wi_g_llt_spec
        ⊕ _get_rec_last_run_info_esr ↦ gensem get_rec_last_run_info_esr_spec
        ⊕ _find_granule ↦ gensem find_granule_spec
        ⊕ _restore_realm_state ↦ gensem restore_realm_state_spec
        ⊕ _esr_is_write ↦ gensem esr_is_write_spec
        ⊕ _smc_realm_create ↦ gensem smc_realm_create_spec
        ⊕ _find_lock_unused_granule ↦ gensem find_lock_unused_granule_spec
        ⊕ _entry_to_phys ↦ gensem entry_to_phys_spec
        ⊕ _stage2_tlbi_ipa ↦ gensem stage2_tlbi_ipa_spec
        ⊕ _atomic_granule_get ↦ gensem atomic_granule_get_spec
        ⊕ _user_step ↦ gensem user_step_spec
        ⊕ _get_wi_index ↦ gensem get_wi_index_spec
        ⊕ _link_table ↦ gensem link_table_spec
        ⊕ _smc_realm_destroy ↦ gensem smc_realm_destroy_spec
        ⊕ _addr_is_level_aligned ↦ gensem addr_is_level_aligned_spec
      .

    Definition RealmExitHandler := RealmExitHandler_fresh ⊕ RealmExitHandler_passthrough.

  End LayerDef.

End Layer.
