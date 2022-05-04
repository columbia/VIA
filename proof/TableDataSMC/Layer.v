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
Require Import TableDataSMC.Spec.

Local Open Scope Z_scope.

Section Layer.

  Context `{real_params: RealParams}.

  Section InvDef.

    Record high_level_invariant (adt: RData) :=
      mkInvariants { }.

    Global Instance TableDataSMC_ops : CompatDataOps RData :=
      {
        empty_data := empty_adt;
        high_level_invariant := high_level_invariant;
        low_level_invariant := fun (b: block) (d: RData) => True;
        kernel_mode adt := True
      }.

  End InvDef.

  Section InvInit.

    Global Instance TableDataSMC_prf : CompatData RData.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvInit.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModelX}.
  Context `{Hmwd: UseMemWithData mem}.

  Section InvProof.

    Global Instance smc_rtt_create_inv: PreservesInvariants smc_rtt_create_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_rtt_destroy_inv: PreservesInvariants smc_rtt_destroy_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_rtt_map_inv: PreservesInvariants smc_rtt_map_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_rtt_unmap_inv: PreservesInvariants smc_rtt_unmap_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_data_create_inv: PreservesInvariants smc_data_create_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_data_destroy_inv: PreservesInvariants smc_data_destroy_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance smc_data_create_unknown_inv: PreservesInvariants smc_data_create_unknown_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance data_destroy_inv: PreservesInvariants data_destroy_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance el3_sync_lel_inv: PreservesInvariants el3_sync_lel_spec.
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

    Global Instance assert_cond_inv: PreservesInvariants assert_cond_spec.
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

    Definition TableDataSMC_fresh : compatlayer (cdata RData) :=
      _smc_rtt_create ↦ gensem smc_rtt_create_spec
        ⊕ _smc_rtt_destroy ↦ gensem smc_rtt_destroy_spec
        ⊕ _smc_rtt_map ↦ gensem smc_rtt_map_spec
        ⊕ _smc_rtt_unmap ↦ gensem smc_rtt_unmap_spec
        ⊕ _smc_data_create ↦ gensem smc_data_create_spec
        ⊕ _smc_data_destroy ↦ gensem smc_data_destroy_spec
        ⊕ _smc_data_create_unknown ↦ gensem smc_data_create_unknown_spec
      .

    Definition TableDataSMC_passthrough : compatlayer (cdata RData) :=
      _data_destroy ↦ gensem data_destroy_spec
        ⊕ _el3_sync_lel ↦ gensem el3_sync_lel_spec
        ⊕ _enter_rmm ↦ gensem enter_rmm_spec
        ⊕ _data_create_unknown ↦ gensem data_create_unknown_spec
        ⊕ _smc_granule_delegate ↦ gensem smc_granule_delegate_spec
        ⊕ _exit_rmm ↦ gensem exit_rmm_spec
        ⊕ _smc_granule_undelegate ↦ gensem smc_granule_undelegate_spec
        ⊕ _smc_rec_destroy ↦ gensem smc_rec_destroy_spec
        ⊕ _smc_rec_create ↦ gensem smc_rec_create_spec
        ⊕ _smc_rec_run ↦ gensem smc_rec_run_spec
        ⊕ _data_create ↦ gensem data_create_spec
        ⊕ _read_reg ↦ gensem read_reg_spec
        ⊕ _assert_cond ↦ gensem assert_cond_spec
        ⊕ _smc_realm_create ↦ gensem smc_realm_create_spec
        ⊕ _user_step ↦ gensem user_step_spec
        ⊕ _smc_realm_activate ↦ gensem smc_realm_activate_spec
        ⊕ _smc_realm_destroy ↦ gensem smc_realm_destroy_spec
      .

    Definition TableDataSMC := TableDataSMC_fresh ⊕ TableDataSMC_passthrough.

  End LayerDef.

End Layer.
