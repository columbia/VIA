Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Section RefineRel.

  Record relate_secure (hadt: RData) (ladt: RData) :=
    mkrelate_secure {
        mem_rel:
          forall rd_gidx,
            let g := (gs (share hadt)) @ rd_gidx in
            forall (is_rd: gtype g = GRANULE_STATE_RD) vaddr data_gidx,
              let ipa_gidx := __addr_to_gidx vaddr in
              forall (Hwalk: rtts (share hadt) rd_gidx ipa_gidx = (data_gidx, true))
                (Hdata: is_gidx data_gidx = true),
                let ldata := (gs (share ladt)) @ data_gidx in
                let hdata := (gs (share hadt)) @ data_gidx in
                let ofst := vaddr mod 4096 in
                match (sec_mem ((realms (share hadt)) @ rd_gidx)) @ vaddr with
                | Some val => (g_data (gnorm ldata)) @ ofst = val
                | None => (g_data (gnorm hdata)) @ ofst = (g_data (gnorm ldata)) @ ofst
                end;
        reg_not_run_rel:
          forall rd_gidx rec_gidx,
            let rd := (gs (share hadt)) @ rd_gidx in
            let rec := (gs (share hadt)) @ rec_gidx in
            let reclow := (gs (share ladt)) @ rec_gidx in
            forall (is_rd: gtype rd = GRANULE_STATE_RD)
              (is_rec: gtype rec = GRANULE_STATE_REC)
              (is_rd_rec: g_rd (ginfo rec) = rd_gidx)
              (not_run: g_running (grec rec) = None),
            forall reg,
              let realm := ((realms (share hadt)) @ rd_gidx) in
              if get_reg reg ((decl_regs realm) @ rec_gidx) =? 1 then
                get_reg reg (g_regs (grec rec)) = get_reg reg (g_regs (grec reclow))
              else
                get_reg reg ((sec_regs realm) @ rec_gidx) = get_reg reg (g_regs (grec reclow));
        reg_running_rel:
          forall rd_gidx rec_gidx,
            let rd := (gs (share hadt)) @ rd_gidx in
            let rec := (gs (share hadt)) @ rec_gidx in
            let reclow := (gs (share ladt)) @ rec_gidx in
            forall (is_rd: gtype rd = GRANULE_STATE_RD)
              (is_rec: gtype rec = GRANULE_STATE_REC)
              (is_rd_rec: g_rd (ginfo rec) = rd_gidx)
              (running: g_running (grec rec) = Some CPU_ID),
            forall reg,
              let realm := ((realms (share hadt)) @ rd_gidx) in
              if get_reg reg ((decl_regs realm) @ rec_gidx) =? 1 then
                get_reg reg (cpu_regs (priv hadt)) = get_reg reg (cpu_regs (priv ladt))
              else
                get_reg reg ((sec_regs realm) @ rec_gidx) = get_reg reg (cpu_regs (priv ladt));
        regs_eq_not_realm:
          cur_rec (priv hadt) = None ->
          cpu_regs (priv hadt) = cpu_regs (priv ladt)
      }.

  Inductive invariant (adt: RData) :=
  | INV_SHARE
      (gpt_false_ns:
         forall gidx, (gpt (share adt)) @ gidx = false -> gtype ((gs (share adt)) @ gidx) = GRANULE_STATE_NS)
      (delegate_zero:
         forall st gidx,
           let gn := (gs st) @ gidx in
           gtype gn = GRANULE_STATE_DELEGATED ->
           gnorm gn = zero_granule_data_normal /\
           grec gn = zero_granule_data_rec)
      (rec_rd:
         forall gidx,
           let gn := (gs (share adt)) @ gidx in
           gtype gn = GRANULE_STATE_REC ->
           let rd_gidx := g_rd (ginfo gn) in
           gtype ((gs (share adt)) @ rd_gidx) = GRANULE_STATE_RD)
      (table_prop:
         forall rd_gidx,
           let gn := (gs (share adt)) @ rd_gidx in
           gtype gn = GRANULE_STATE_RD ->
           forall ipa_gidx data_gidx b,
             (rtts (share adt)) rd_gidx ipa_gidx = (data_gidx, b) ->
             is_gidx data_gidx = true ->
             let gn_data := (gs (share adt)) @ data_gidx in
             gtype gn_data = GRANULE_STATE_DATA /\
             tbl_parent (gaux gn_data) = ipa_gidx /\ g_rd (ginfo gn_data) = rd_gidx)
      (tlb_prop:
         forall rd_gidx rec_gidx,
           let rd := (gs (share adt)) @ rd_gidx in
           let rec := (gs (share adt)) @ rec_gidx in
           forall (is_rd: gtype rd = GRANULE_STATE_RD)
             (is_rec: gtype rec = GRANULE_STATE_REC)
             (is_rd_rec: g_rd (ginfo rec) = rd_gidx)
             (running: g_running (grec rec) = Some CPU_ID),
           forall ipa_gidx data_gidx, (tlbs (share adt)) CPU_ID ipa_gidx = data_gidx ->
                                 is_gidx data_gidx = true ->
                                 (rtts (share adt)) rd_gidx ipa_gidx = (data_gidx, true))
      (running_not_new:
         forall rd_gidx rec_gidx,
           let rd := (gs (share adt)) @ rd_gidx in
           let rec := (gs (share adt)) @ rec_gidx in
           forall (is_rd: gtype rd = GRANULE_STATE_RD)
             (is_rec: gtype rec = GRANULE_STATE_REC)
             (is_rd_rec: g_rd (ginfo rec) = rd_gidx)
             (running: g_running (grec rec) = Some CPU_ID),
             g_realm_state (gnorm rd) = REALM_STATE_ACTIVE)
      (cur_running:
         forall rec_gidx,
           let rec := (gs (share adt)) @ rec_gidx in
           forall (is_rec: gtype rec = GRANULE_STATE_REC)
             (running: g_running (grec rec) = Some CPU_ID),
             cur_rec (priv adt) = Some rec_gidx)
      (rd_gcnt:
         forall st rd_gidx,
           let rd := (gs st) @ rd_gidx in
           gtype rd = GRANULE_STATE_RD ->
           gcnt rd = 0 ->
           ~ exists gidx, gtype ((gs st) @ gidx) = GRANULE_STATE_REC /\
                     (g_rd (ginfo (gs st) @ gidx)) = rd_gidx)
      (rd_gcnt_rtt:
         forall st rd_gidx,
           let rd := (gs st) @ rd_gidx in
           gtype rd = GRANULE_STATE_RD ->
           gcnt rd = 0 ->
           forall ipa, (rtts st rd_gidx ipa = (0, false)))
      (new_decl_mem:
         forall st rd_gidx,
           let gn := (gs st) @ rd_gidx in
           gtype gn = GRANULE_STATE_RD ->
           g_realm_state (gnorm gn) = REALM_STATE_NEW ->
           forall addr, (sec_mem ((realms st) @ rd_gidx)) @ addr = None)
      (new_decl_regs:
         forall st rd_gidx,
           let gn := (gs st) @ rd_gidx in
           gtype gn = GRANULE_STATE_RD ->
           g_realm_state (gnorm gn) = REALM_STATE_NEW ->
           forall gidx reg, get_reg reg ((decl_regs ((realms st) @ rd_gidx)) @ gidx) = 1)
      (decl_gpregs:
         forall d rd_gidx rec_gidx,
           let rd := (gs (share d)) @ rd_gidx in
           let rec := (gs (share d)) @ rec_gidx in
           forall (is_rd: gtype rd = GRANULE_STATE_RD)
             (is_rec: gtype rec = GRANULE_STATE_REC)
             (is_rd_rec: g_rd (ginfo rec) = rd_gidx)
             (running: mstage (priv d) = REALM rd_gidx rec_gidx),
           forall reg, (0 <= reg <= 30) -> get_reg reg ((decl_regs ((realms (share d)) @ rd_gidx)) @ rec_gidx) = 0)
      (new_table:
         forall st gidx,
           let gn := (gs st) @ gidx in
           gtype gn <> GRANULE_STATE_RD ->
           forall ipa, rtts st gidx ipa = (0, false))
      (decl_sysregs:
         forall d rd_gidx,
           let gn := (gs (share d)) @ rd_gidx in
           forall gidx reg, ~ (0 <= reg <= 30) -> get_reg reg ((decl_regs ((realms (share d)) @ rd_gidx)) @ gidx) = 1):
      invariant adt.

  Inductive id_granule (hg: Granule) (lg: Granule) :=
  | ID_GRANULE
      (id_glock: glock lg = glock hg)
      (id_gref: gref lg = gref hg)
      (id_gtype: gtype lg = gtype hg)
      (id_gcnt: gcnt lg = gcnt hg)
      (id_ginfo: ginfo lg = ginfo hg)
      (id_gro: gro lg = gro hg)
      (id_gaux: gaux lg = gaux hg)
      (id_not_data: forall (Htype: gtype hg <> GRANULE_STATE_DATA), g_data (gnorm hg) = g_data (gnorm lg))
      (id_not_rec: forall (Htype: gtype hg <> GRANULE_STATE_REC), g_regs (grec hg) = g_regs (grec lg))
      (id_g_realm_state: g_realm_state (gnorm lg) = g_realm_state (gnorm hg))
      (id_g_par_base: g_par_base (gnorm lg) = g_par_base (gnorm hg))
      (id_g_par_end: g_par_end (gnorm lg) = g_par_end (gnorm hg))
      (id_g_rec_list: g_rec_list (gnorm lg) = g_rec_list (gnorm hg))
      (id_g_rtt: g_rtt (gnorm lg) = g_rtt (gnorm hg))
      (id_g_measurement_algo: g_measurement_algo (gnorm lg) = g_measurement_algo (gnorm hg))
      (id_g_measurement_ctx: g_measurement_ctx (gnorm lg) = g_measurement_ctx (gnorm hg))
      (id_g_measurement: g_measurement (gnorm lg) = g_measurement (gnorm hg))
      (id_g_recs: g_recs (gnorm lg) = g_recs (gnorm hg))
      (id_g_rvic: g_rvic (gnorm lg) = g_rvic (gnorm hg))
      (id_g_runnable: g_runnable (gnorm lg) = g_runnable (gnorm hg))
      (id_g_pc: g_pc (grec lg) = g_pc (grec hg))
      (id_g_pstate: g_pstate (grec lg) = g_pstate (grec hg))
      (id_g_vtimer: g_vtimer (grec lg) = g_vtimer (grec hg))
      (id_g_ptimer: g_ptimer (grec lg) = g_ptimer (grec hg))
      (id_g_dispose_pending: g_dispose_pending (grec lg) = g_dispose_pending (grec hg))
      (id_g_dispose_addr: g_dispose_addr (grec lg) = g_dispose_addr (grec hg))
      (id_g_dispose_size: g_dispose_size (grec lg) = g_dispose_size (grec hg))
      (id_g_rec_rd: g_rec_rd (grec lg) = g_rec_rd (grec hg))
      (id_g_rec_par_base: g_rec_par_base (grec lg) = g_rec_par_base (grec hg))
      (id_g_rec_par_end: g_rec_par_end (grec lg) = g_rec_par_end (grec hg))
      (id_g_rec_rec_list: g_rec_rec_list (grec lg) = g_rec_rec_list (grec hg))
      (id_g_esr: g_esr (grec lg) = g_esr (grec hg))
      (id_g_running: g_running (grec lg) = g_running (grec hg)):
      id_granule hg lg.

  Inductive relate_share (hst: State) (lst: State):=
  | SEC_SHARE
      (id_gpt: gpt lst = gpt hst)
      (id_gpt_lk: gpt_lk lst = gpt_lk hst)
      (id_tlbs: tlbs lst = tlbs hst)
      (id_rtts: rtts lst = rtts hst)
      (id_granule: forall gidx, id_granule ((gs hst) @ gidx) ((gs lst) @ gidx)):
      relate_share hst lst.

  Inductive sysregs_eq regs1 regs2 :=
  | SYSREGS_EQ
      (lr_eq: r_lr regs1 = r_lr regs2)
      (cntp_ctl_el0_eq: r_cntp_ctl_el0 regs1 = r_cntp_ctl_el0 regs2)
      (cntp_cval_el0_eq: r_cntp_cval_el0 regs1 = r_cntp_cval_el0 regs2)
      (cntp_tval_el0_eq: r_cntp_tval_el0 regs1 = r_cntp_tval_el0 regs2)
      (cntv_ctl_el0_eq: r_cntv_ctl_el0 regs1 = r_cntv_ctl_el0 regs2)
      (cntv_cval_el0_eq: r_cntv_cval_el0 regs1 = r_cntv_cval_el0 regs2)
      (cntv_tval_el0_eq: r_cntv_tval_el0 regs1 = r_cntv_tval_el0 regs2)
      (sp_el0_eq: r_sp_el0 regs1 = r_sp_el0 regs2)
      (pmcr_el0_eq: r_pmcr_el0 regs1 = r_pmcr_el0 regs2)
      (pmuserenr_el0_eq: r_pmuserenr_el0 regs1 = r_pmuserenr_el0 regs2)
      (tpidrro_el0_eq: r_tpidrro_el0 regs1 = r_tpidrro_el0 regs2)
      (tpidr_el0_eq: r_tpidr_el0 regs1 = r_tpidr_el0 regs2)
      (sp_el1_eq: r_sp_el1 regs1 = r_sp_el1 regs2)
      (elr_el1_eq: r_elr_el1 regs1 = r_elr_el1 regs2)
      (spsr_el1_eq: r_spsr_el1 regs1 = r_spsr_el1 regs2)
      (csselr_el1_eq: r_csselr_el1 regs1 = r_csselr_el1 regs2)
      (sctlr_el1_eq: r_sctlr_el1 regs1 = r_sctlr_el1 regs2)
      (actlr_el1_eq: r_actlr_el1 regs1 = r_actlr_el1 regs2)
      (cpacr_el1_eq: r_cpacr_el1 regs1 = r_cpacr_el1 regs2)
      (zcr_el1_eq: r_zcr_el1 regs1 = r_zcr_el1 regs2)
      (ttbr0_el1_eq: r_ttbr0_el1 regs1 = r_ttbr0_el1 regs2)
      (ttbr1_el1_eq: r_ttbr1_el1 regs1 = r_ttbr1_el1 regs2)
      (tcr_el1_eq: r_tcr_el1 regs1 = r_tcr_el1 regs2)
      (esr_el1_eq: r_esr_el1 regs1 = r_esr_el1 regs2)
      (afsr0_el1_eq: r_afsr0_el1 regs1 = r_afsr0_el1 regs2)
      (afsr1_el1_eq: r_afsr1_el1 regs1 = r_afsr1_el1 regs2)
      (far_el1_eq: r_far_el1 regs1 = r_far_el1 regs2)
      (mair_el1_eq: r_mair_el1 regs1 = r_mair_el1 regs2)
      (vbar_el1_eq: r_vbar_el1 regs1 = r_vbar_el1 regs2)
      (contextidr_el1_eq: r_contextidr_el1 regs1 = r_contextidr_el1 regs2)
      (tpidr_el1_eq: r_tpidr_el1 regs1 = r_tpidr_el1 regs2)
      (amair_el1_eq: r_amair_el1 regs1 = r_amair_el1 regs2)
      (cntkctl_el1_eq: r_cntkctl_el1 regs1 = r_cntkctl_el1 regs2)
      (par_el1_eq: r_par_el1 regs1 = r_par_el1 regs2)
      (mdscr_el1_eq: r_mdscr_el1 regs1 = r_mdscr_el1 regs2)
      (mdccint_el1_eq: r_mdccint_el1 regs1 = r_mdccint_el1 regs2)
      (disr_el1_eq: r_disr_el1 regs1 = r_disr_el1 regs2)
      (mpam0_el1_eq: r_mpam0_el1 regs1 = r_mpam0_el1 regs2)
      (cnthctl_el2_eq: r_cnthctl_el2 regs1 = r_cnthctl_el2 regs2)
      (cntvoff_el2_eq: r_cntvoff_el2 regs1 = r_cntvoff_el2 regs2)
      (cntpoff_el2_eq: r_cntpoff_el2 regs1 = r_cntpoff_el2 regs2)
      (vmpidr_el2_eq: r_vmpidr_el2 regs1 = r_vmpidr_el2 regs2)
      (vttbr_el2_eq: r_vttbr_el2 regs1 = r_vttbr_el2 regs2)
      (vtcr_el2_eq: r_vtcr_el2 regs1 = r_vtcr_el2 regs2)
      (hcr_el2_eq: r_hcr_el2 regs1 = r_hcr_el2 regs2)
      (actlr_el2_eq: r_actlr_el2 regs1 = r_actlr_el2 regs2)
      (afsr0_el2_eq: r_afsr0_el2 regs1 = r_afsr0_el2 regs2)
      (afsr1_el2_eq: r_afsr1_el2 regs1 = r_afsr1_el2 regs2)
      (amair_el2_eq: r_amair_el2 regs1 = r_amair_el2 regs2)
      (cptr_el2_eq: r_cptr_el2 regs1 = r_cptr_el2 regs2)
      (elr_el2_eq: r_elr_el2 regs1 = r_elr_el2 regs2)
      (esr_el2_eq: r_esr_el2 regs1 = r_esr_el2 regs2)
      (far_el2_eq: r_far_el2 regs1 = r_far_el2 regs2)
      (hacr_el2_eq: r_hacr_el2 regs1 = r_hacr_el2 regs2)
      (hpfar_el2_eq: r_hpfar_el2 regs1 = r_hpfar_el2 regs2)
      (hstr_el2_eq: r_hstr_el2 regs1 = r_hstr_el2 regs2)
      (mair_el2_eq: r_mair_el2 regs1 = r_mair_el2 regs2)
      (mpam_el2_eq: r_mpam_el2 regs1 = r_mpam_el2 regs2)
      (mpamhcr_el2_eq: r_mpamhcr_el2 regs1 = r_mpamhcr_el2 regs2)
      (pmscr_el2_eq: r_pmscr_el2 regs1 = r_pmscr_el2 regs2)
      (sctlr_el2_eq: r_sctlr_el2 regs1 = r_sctlr_el2 regs2)
      (scxtnum_el2_eq: r_scxtnum_el2 regs1 = r_scxtnum_el2 regs2)
      (sp_el2_eq: r_sp_el2 regs1 = r_sp_el2 regs2)
      (spsr_el2_eq: r_spsr_el2 regs1 = r_spsr_el2 regs2)
      (tcr_el2_eq: r_tcr_el2 regs1 = r_tcr_el2 regs2)
      (tfsr_el2_eq: r_tfsr_el2 regs1 = r_tfsr_el2 regs2)
      (tpidr_el2_eq: r_tpidr_el2 regs1 = r_tpidr_el2 regs2)
      (trfcr_el2_eq: r_trfcr_el2 regs1 = r_trfcr_el2 regs2)
      (ttbr0_el2_eq: r_ttbr0_el2 regs1 = r_ttbr0_el2 regs2)
      (ttbr1_el2_eq: r_ttbr1_el2 regs1 = r_ttbr1_el2 regs2)
      (vbar_el2_eq: r_vbar_el2 regs1 = r_vbar_el2 regs2)
      (vdisr_el2_eq: r_vdisr_el2 regs1 = r_vdisr_el2 regs2)
      (vncr_el2_eq: r_vncr_el2 regs1 = r_vncr_el2 regs2)
      (vpidr_el2_eq: r_vpidr_el2 regs1 = r_vpidr_el2 regs2)
      (vsesr_el2_eq: r_vsesr_el2 regs1 = r_vsesr_el2 regs2)
      (vstcr_el2_eq: r_vstcr_el2 regs1 = r_vstcr_el2 regs2)
      (vsttbr_el2_eq: r_vsttbr_el2 regs1 = r_vsttbr_el2 regs2)
      (zcr_el2_eq: r_zcr_el2 regs1 = r_zcr_el2 regs2)
      (icc_sre_el2_eq: r_icc_sre_el2 regs1 = r_icc_sre_el2 regs2)
      (icc_hppir1_el1_eq: r_icc_hppir1_el1 regs1 = r_icc_hppir1_el1 regs2)
      (spsr_el3_eq: r_spsr_el3 regs1 = r_spsr_el3 regs2)
      (elr_el3_eq: r_elr_el3 regs1 = r_elr_el3 regs2)
      (esr_el3_eq: r_esr_el3 regs1 = r_esr_el3 regs2)
      (scr_el3_eq: r_scr_el3 regs1 = r_scr_el3 regs2)
      (tpidr_el3_eq: r_tpidr_el3 regs1 = r_tpidr_el3 regs2):
      sysregs_eq regs1 regs2.

  Inductive relate_priv priv1 priv2 :=
  | RELATE_PRIV
      (cpu_regs_eq: sysregs_eq (cpu_regs priv1) (cpu_regs priv2))
      (asm_regs_eq: asm_regs priv1 = asm_regs priv2)
      (id_regs_eq: id_regs priv1 = id_regs priv2)
      (buffer_eq: buffer priv1 = buffer priv2)
      (ns_regs_el2_eq: ns_regs_el2 priv1 = ns_regs_el2 priv2)
      (realm_params_eq: realm_params priv1 = realm_params priv2)
      (rec_params_eq: rec_params priv1 = rec_params priv2)
      (rec_run_eq: rec_run priv1 = rec_run priv2)
      (retval_eq: retval priv1 = retval priv2)
      (locked_g_eq: locked_g priv1 = locked_g priv2)
      (wi_last_level_eq: wi_last_level priv1 = wi_last_level priv2)
      (wi_llt_eq: wi_llt priv1 = wi_llt priv2)
      (wi_index_eq: wi_index priv1 = wi_index priv2)
      (rvic_x0_eq: rvic_x0 priv1 = rvic_x0 priv2)
      (rvic_x1_eq: rvic_x1 priv1 = rvic_x1 priv2)
      (rvic_x2_eq: rvic_x2 priv1 = rvic_x2 priv2)
      (rvic_x3_eq: rvic_x3 priv1 = rvic_x3 priv2)
      (rvic_target_eq: rvic_target priv1 = rvic_target priv2)
      (rvic_ns_notify_eq: rvic_ns_notify priv1 = rvic_ns_notify priv2)
      (psci_x0_eq: psci_x0 priv1 = psci_x0 priv2)
      (psci_x1_eq: psci_x1 priv1 = psci_x1 priv2)
      (psci_x2_eq: psci_x2 priv1 = psci_x2 priv2)
      (psci_x3_eq: psci_x3 priv1 = psci_x3 priv2)
      (psci_forward_x0_eq: psci_forward_x0 priv1 = psci_forward_x0 priv2)
      (psci_forward_x1_eq: psci_forward_x1 priv1 = psci_forward_x1 priv2)
      (psci_forward_x2_eq: psci_forward_x2 priv1 = psci_forward_x2 priv2)
      (psci_forward_x3_eq: psci_forward_x3 priv1 = psci_forward_x3 priv2)
      (psci_forward_psci_call_eq: psci_forward_psci_call priv1 = psci_forward_psci_call priv2)
      (target_rec_eq: target_rec priv1 = target_rec priv2)
      (el2_stack_eq: el2_stack priv1 = el2_stack priv2)
      (el3_stack_eq: el3_stack priv1 = el3_stack priv2)
      (ns_regs_el3_eq: ns_regs_el3 priv1 = ns_regs_el3 priv2)
      (realm_regs_el3_eq: realm_regs_el3 priv1 = realm_regs_el3 priv2)
      (cur_rec_eq: cur_rec priv1 = cur_rec priv2)
      (mstage_eq: mstage priv1 = mstage priv2)
      (trap_reason_eq: trap_reason priv1 = trap_reason priv2)
      (trap_type_eq: trap_type priv1 = trap_type priv2):
      relate_priv priv1 priv2.

  Record relate_adt (hadt: RData) (ladt: RData) :=
    mkrelate_adt {
        id_share: relate_share (share hadt) (share ladt);
        id_priv: relate_priv (priv hadt) (priv ladt);
        invs: invariant hadt;
        rel_secure: relate_secure hadt ladt
      }.

End RefineRel.

Hypothesis query_oracle_security:
  forall habd habd' labd
    (Hspec: query_oracle habd = Some habd')
    (Hrel: relate_share (share habd) (share labd))
    (Hinv: invariant habd)
    (Hsec: relate_secure habd labd),
  exists labd', query_oracle labd = Some labd' /\
            relate_share (share habd') (share labd') /\ invariant habd' /\ relate_secure habd' labd'.

Ltac exploit_query_oracle H :=
  match goal with
  | [ |- context[query_oracle ?ld]] =>
    match type of H with
    | query_oracle ?hd = Some ?hd' =>
      exploit (query_oracle_security hd hd' ld H)
    end
  end; simpl.

Lemma set_gpregs_sys_eq_l:
  forall regs1 regs2 reg (Hreg: 0 <= reg <= 30) val,
    sysregs_eq regs1 regs2 -> sysregs_eq (set_reg reg val regs1) regs2.
Proof.
  intros. assert(0 <= reg < 31) by omega.
  destruct_case H0; grewrite; simpl_update_reg; inv H; constructor; simpl; assumption.
Qed.

Lemma set_gpregs_sys_eq_r:
  forall regs1 regs2 reg (Hreg: 0 <= reg <= 30) val,
    sysregs_eq regs1 regs2 -> sysregs_eq regs1 (set_reg reg val regs2).
Proof.
  intros. assert(0 <= reg < 31) by omega.
  destruct_case H0; grewrite; simpl_update_reg; inv H; constructor; simpl; assumption.
Qed.

Lemma relate_share_gpt:
  forall sa sb (Hrelate: relate_share sa sb), gpt sb = gpt sa.
Proof. intros. inv Hrelate. assumption. Qed.
Lemma relate_share_gpt_lk:
  forall sa sb (Hrelate: relate_share sa sb), gpt_lk sb = gpt_lk sa.
Proof. intros. inv Hrelate. assumption. Qed.
Lemma relate_share_tlbs:
  forall sa sb (Hrelate: relate_share sa sb), tlbs sb = tlbs sa.
Proof. intros. inv Hrelate. assumption. Qed.
Lemma relate_share_rtts:
  forall sa sb (Hrelate: relate_share sa sb), rtts sb = rtts sa.
Proof. intros. inv Hrelate. assumption. Qed.
Lemma relate_share_glock:
  forall sa sb (Hrelate: relate_share sa sb) gidx, glock ((gs sb) @ gidx) = glock ((gs sa) @ gidx).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_gref:
  forall sa sb (Hrelate: relate_share sa sb) gidx, gref ((gs sb) @ gidx) = gref ((gs sa) @ gidx).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_gtype:
  forall sa sb (Hrelate: relate_share sa sb) gidx, gtype ((gs sb) @ gidx) = gtype ((gs sa) @ gidx).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_gcnt:
  forall sa sb (Hrelate: relate_share sa sb) gidx, gcnt ((gs sb) @ gidx) = gcnt ((gs sa) @ gidx).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_ginfo:
  forall sa sb (Hrelate: relate_share sa sb) gidx, ginfo ((gs sb) @ gidx) = ginfo ((gs sa) @ gidx).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_gro:
  forall sa sb (Hrelate: relate_share sa sb) gidx, gro ((gs sb) @ gidx) = gro ((gs sa) @ gidx).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_gaux:
  forall sa sb (Hrelate: relate_share sa sb) gidx, gaux ((gs sb) @ gidx) = gaux ((gs sa) @ gidx).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_realm_state:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_realm_state (gnorm ((gs sb) @ gidx)) = g_realm_state (gnorm ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_par_base:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_par_base (gnorm ((gs sb) @ gidx)) = g_par_base (gnorm ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_par_end:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_par_end (gnorm ((gs sb) @ gidx)) = g_par_end (gnorm ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_rec_list:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_rec_list (gnorm ((gs sb) @ gidx)) = g_rec_list (gnorm ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_rtt:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_rtt (gnorm ((gs sb) @ gidx)) = g_rtt (gnorm ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_measurement_algo:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_measurement_algo (gnorm ((gs sb) @ gidx)) = g_measurement_algo (gnorm ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_measurement_ctx:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_measurement_ctx (gnorm ((gs sb) @ gidx)) = g_measurement_ctx (gnorm ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_measurement:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_measurement (gnorm ((gs sb) @ gidx)) = g_measurement (gnorm ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_recs:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_recs (gnorm ((gs sb) @ gidx)) = g_recs (gnorm ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_rvic:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_rvic (gnorm ((gs sb) @ gidx)) = g_rvic (gnorm ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_runnable:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_runnable (gnorm ((gs sb) @ gidx)) = g_runnable (gnorm ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_pc:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_pc (grec ((gs sb) @ gidx)) = g_pc (grec ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_pstate:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_pstate (grec ((gs sb) @ gidx)) = g_pstate (grec ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_vtimer:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_vtimer (grec ((gs sb) @ gidx)) = g_vtimer (grec ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_ptimer:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_ptimer (grec ((gs sb) @ gidx)) = g_ptimer (grec ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_dispose_pending:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_dispose_pending (grec ((gs sb) @ gidx)) = g_dispose_pending (grec ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_dispose_addr:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_dispose_addr (grec ((gs sb) @ gidx)) = g_dispose_addr (grec ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_dispose_size:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_dispose_size (grec ((gs sb) @ gidx)) = g_dispose_size (grec ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_rec_rd:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_rec_rd (grec ((gs sb) @ gidx)) = g_rec_rd (grec ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_rec_par_base:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_rec_par_base (grec ((gs sb) @ gidx)) = g_rec_par_base (grec ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_rec_par_end:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_rec_par_end (grec ((gs sb) @ gidx)) = g_rec_par_end (grec ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_rec_rec_list:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_rec_rec_list (grec ((gs sb) @ gidx)) = g_rec_rec_list (grec ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_esr:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_esr (grec ((gs sb) @ gidx)) = g_esr (grec ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_g_running:
  forall sa sb (Hrelate: relate_share sa sb) gidx, g_running (grec ((gs sb) @ gidx)) = g_running (grec ((gs sa) @ gidx)).
Proof. intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T. assumption. Qed.
Lemma relate_share_ref_accessible:
  forall sa sb (Hrelate: relate_share sa sb) gidx c,
    ref_accessible ((gs sb) @ gidx) c = ref_accessible ((gs sa) @ gidx) c.
Proof.
  intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T.
  unfold ref_accessible. grewrite. reflexivity.
Qed.

Lemma relate_share_g_data:
  forall sa sb (Hrelate: relate_share sa sb) gidx (Htype: gtype ((gs sa) @ gidx) <> GRANULE_STATE_DATA),
    g_data (gnorm ((gs sb) @ gidx)) = g_data (gnorm ((gs sa) @ gidx)).
Proof.
  intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T.
  rewrite id_not_data. reflexivity. assumption.
Qed.

Lemma relate_share_g_regs:
  forall sa sb (Hrelate: relate_share sa sb) gidx (Htype: gtype ((gs sa) @ gidx) <> GRANULE_STATE_REC),
    g_regs (grec ((gs sb) @ gidx)) = g_regs (grec ((gs sa) @ gidx)).
Proof.
  intros. inv Hrelate. pose proof (id_granule0 gidx) as T. inversion T.
  rewrite id_not_rec. reflexivity. assumption.
Qed.
Lemma relate_priv_asm_regs:
  forall pa pb (Hrelate: relate_priv pa pb), asm_regs pb = asm_regs pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_id_regs:
  forall pa pb (Hrelate: relate_priv pa pb), id_regs pb = id_regs pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_buffer:
  forall pa pb (Hrelate: relate_priv pa pb), buffer pb = buffer pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_ns_regs_el2:
  forall pa pb (Hrelate: relate_priv pa pb), ns_regs_el2 pb = ns_regs_el2 pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_realm_params:
  forall pa pb (Hrelate: relate_priv pa pb), realm_params pb = realm_params pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_rec_params:
  forall pa pb (Hrelate: relate_priv pa pb), rec_params pb = rec_params pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_rec_run:
  forall pa pb (Hrelate: relate_priv pa pb), rec_run pb = rec_run pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_retval:
  forall pa pb (Hrelate: relate_priv pa pb), retval pb = retval pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_locked_g:
  forall pa pb (Hrelate: relate_priv pa pb), locked_g pb = locked_g pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_wi_last_level:
  forall pa pb (Hrelate: relate_priv pa pb), wi_last_level pb = wi_last_level pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_wi_llt:
  forall pa pb (Hrelate: relate_priv pa pb), wi_llt pb = wi_llt pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_wi_index:
  forall pa pb (Hrelate: relate_priv pa pb), wi_index pb = wi_index pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_rvic_x0:
  forall pa pb (Hrelate: relate_priv pa pb), rvic_x0 pb = rvic_x0 pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_rvic_x1:
  forall pa pb (Hrelate: relate_priv pa pb), rvic_x1 pb = rvic_x1 pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_rvic_x2:
  forall pa pb (Hrelate: relate_priv pa pb), rvic_x2 pb = rvic_x2 pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_rvic_x3:
  forall pa pb (Hrelate: relate_priv pa pb), rvic_x3 pb = rvic_x3 pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_rvic_target:
  forall pa pb (Hrelate: relate_priv pa pb), rvic_target pb = rvic_target pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_rvic_ns_notify:
  forall pa pb (Hrelate: relate_priv pa pb), rvic_ns_notify pb = rvic_ns_notify pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_psci_x0:
  forall pa pb (Hrelate: relate_priv pa pb), psci_x0 pb = psci_x0 pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_psci_x1:
  forall pa pb (Hrelate: relate_priv pa pb), psci_x1 pb = psci_x1 pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_psci_x2:
  forall pa pb (Hrelate: relate_priv pa pb), psci_x2 pb = psci_x2 pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_psci_x3:
  forall pa pb (Hrelate: relate_priv pa pb), psci_x3 pb = psci_x3 pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_psci_forward_x0:
  forall pa pb (Hrelate: relate_priv pa pb), psci_forward_x0 pb = psci_forward_x0 pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_psci_forward_x1:
  forall pa pb (Hrelate: relate_priv pa pb), psci_forward_x1 pb = psci_forward_x1 pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_psci_forward_x2:
  forall pa pb (Hrelate: relate_priv pa pb), psci_forward_x2 pb = psci_forward_x2 pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_psci_forward_x3:
  forall pa pb (Hrelate: relate_priv pa pb), psci_forward_x3 pb = psci_forward_x3 pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_psci_forward_psci_call:
  forall pa pb (Hrelate: relate_priv pa pb), psci_forward_psci_call pb = psci_forward_psci_call pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_target_rec:
  forall pa pb (Hrelate: relate_priv pa pb), target_rec pb = target_rec pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_el2_stack:
  forall pa pb (Hrelate: relate_priv pa pb), el2_stack pb = el2_stack pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_el3_stack:
  forall pa pb (Hrelate: relate_priv pa pb), el3_stack pb = el3_stack pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_ns_regs_el3:
  forall pa pb (Hrelate: relate_priv pa pb), ns_regs_el3 pb = ns_regs_el3 pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_realm_regs_el3:
  forall pa pb (Hrelate: relate_priv pa pb), realm_regs_el3 pb = realm_regs_el3 pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_cur_rec:
  forall pa pb (Hrelate: relate_priv pa pb), cur_rec pb = cur_rec pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_mstage:
  forall pa pb (Hrelate: relate_priv pa pb), mstage pb = mstage pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_trap_reason:
  forall pa pb (Hrelate: relate_priv pa pb), trap_reason pb = trap_reason pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_trap_type:
  forall pa pb (Hrelate: relate_priv pa pb), trap_type pb = trap_type pa.
Proof. intros; inv Hrelate. grewrite; reflexivity. Qed.
Lemma relate_priv_r_lr:
  forall pa pb (Hrelate: relate_priv pa pb), r_lr (cpu_regs pb) = r_lr (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq. grewrite. reflexivity. Qed.
Lemma relate_priv_r_cntp_ctl_el0:
  forall pa pb (Hrelate: relate_priv pa pb), r_cntp_ctl_el0 (cpu_regs pb) = r_cntp_ctl_el0 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_cntp_cval_el0:
  forall pa pb (Hrelate: relate_priv pa pb), r_cntp_cval_el0 (cpu_regs pb) = r_cntp_cval_el0 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_cntp_tval_el0:
  forall pa pb (Hrelate: relate_priv pa pb), r_cntp_tval_el0 (cpu_regs pb) = r_cntp_tval_el0 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_cntv_ctl_el0:
  forall pa pb (Hrelate: relate_priv pa pb), r_cntv_ctl_el0 (cpu_regs pb) = r_cntv_ctl_el0 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_cntv_cval_el0:
  forall pa pb (Hrelate: relate_priv pa pb), r_cntv_cval_el0 (cpu_regs pb) = r_cntv_cval_el0 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_cntv_tval_el0:
  forall pa pb (Hrelate: relate_priv pa pb), r_cntv_tval_el0 (cpu_regs pb) = r_cntv_tval_el0 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_sp_el0:
  forall pa pb (Hrelate: relate_priv pa pb), r_sp_el0 (cpu_regs pb) = r_sp_el0 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_pmcr_el0:
  forall pa pb (Hrelate: relate_priv pa pb), r_pmcr_el0 (cpu_regs pb) = r_pmcr_el0 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_pmuserenr_el0:
  forall pa pb (Hrelate: relate_priv pa pb), r_pmuserenr_el0 (cpu_regs pb) = r_pmuserenr_el0 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_tpidrro_el0:
  forall pa pb (Hrelate: relate_priv pa pb), r_tpidrro_el0 (cpu_regs pb) = r_tpidrro_el0 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_tpidr_el0:
  forall pa pb (Hrelate: relate_priv pa pb), r_tpidr_el0 (cpu_regs pb) = r_tpidr_el0 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_sp_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_sp_el1 (cpu_regs pb) = r_sp_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_elr_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_elr_el1 (cpu_regs pb) = r_elr_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_spsr_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_spsr_el1 (cpu_regs pb) = r_spsr_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_csselr_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_csselr_el1 (cpu_regs pb) = r_csselr_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_sctlr_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_sctlr_el1 (cpu_regs pb) = r_sctlr_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_actlr_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_actlr_el1 (cpu_regs pb) = r_actlr_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_cpacr_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_cpacr_el1 (cpu_regs pb) = r_cpacr_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_zcr_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_zcr_el1 (cpu_regs pb) = r_zcr_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_ttbr0_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_ttbr0_el1 (cpu_regs pb) = r_ttbr0_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_ttbr1_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_ttbr1_el1 (cpu_regs pb) = r_ttbr1_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_tcr_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_tcr_el1 (cpu_regs pb) = r_tcr_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_esr_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_esr_el1 (cpu_regs pb) = r_esr_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_afsr0_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_afsr0_el1 (cpu_regs pb) = r_afsr0_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_afsr1_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_afsr1_el1 (cpu_regs pb) = r_afsr1_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_far_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_far_el1 (cpu_regs pb) = r_far_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_mair_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_mair_el1 (cpu_regs pb) = r_mair_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_vbar_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_vbar_el1 (cpu_regs pb) = r_vbar_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_contextidr_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_contextidr_el1 (cpu_regs pb) = r_contextidr_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_tpidr_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_tpidr_el1 (cpu_regs pb) = r_tpidr_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_amair_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_amair_el1 (cpu_regs pb) = r_amair_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_cntkctl_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_cntkctl_el1 (cpu_regs pb) = r_cntkctl_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_par_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_par_el1 (cpu_regs pb) = r_par_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_mdscr_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_mdscr_el1 (cpu_regs pb) = r_mdscr_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_mdccint_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_mdccint_el1 (cpu_regs pb) = r_mdccint_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_disr_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_disr_el1 (cpu_regs pb) = r_disr_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_mpam0_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_mpam0_el1 (cpu_regs pb) = r_mpam0_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_cnthctl_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_cnthctl_el2 (cpu_regs pb) = r_cnthctl_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_cntvoff_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_cntvoff_el2 (cpu_regs pb) = r_cntvoff_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_cntpoff_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_cntpoff_el2 (cpu_regs pb) = r_cntpoff_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_vmpidr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_vmpidr_el2 (cpu_regs pb) = r_vmpidr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_vttbr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_vttbr_el2 (cpu_regs pb) = r_vttbr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_vtcr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_vtcr_el2 (cpu_regs pb) = r_vtcr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_hcr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_hcr_el2 (cpu_regs pb) = r_hcr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_actlr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_actlr_el2 (cpu_regs pb) = r_actlr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_afsr0_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_afsr0_el2 (cpu_regs pb) = r_afsr0_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_afsr1_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_afsr1_el2 (cpu_regs pb) = r_afsr1_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_amair_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_amair_el2 (cpu_regs pb) = r_amair_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_cptr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_cptr_el2 (cpu_regs pb) = r_cptr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_elr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_elr_el2 (cpu_regs pb) = r_elr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_esr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_esr_el2 (cpu_regs pb) = r_esr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_far_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_far_el2 (cpu_regs pb) = r_far_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_hacr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_hacr_el2 (cpu_regs pb) = r_hacr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_hpfar_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_hpfar_el2 (cpu_regs pb) = r_hpfar_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_hstr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_hstr_el2 (cpu_regs pb) = r_hstr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_mair_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_mair_el2 (cpu_regs pb) = r_mair_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_mpam_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_mpam_el2 (cpu_regs pb) = r_mpam_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_mpamhcr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_mpamhcr_el2 (cpu_regs pb) = r_mpamhcr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_pmscr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_pmscr_el2 (cpu_regs pb) = r_pmscr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_sctlr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_sctlr_el2 (cpu_regs pb) = r_sctlr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_scxtnum_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_scxtnum_el2 (cpu_regs pb) = r_scxtnum_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_sp_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_sp_el2 (cpu_regs pb) = r_sp_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_spsr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_spsr_el2 (cpu_regs pb) = r_spsr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_tcr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_tcr_el2 (cpu_regs pb) = r_tcr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_tfsr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_tfsr_el2 (cpu_regs pb) = r_tfsr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_tpidr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_tpidr_el2 (cpu_regs pb) = r_tpidr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_trfcr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_trfcr_el2 (cpu_regs pb) = r_trfcr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_ttbr0_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_ttbr0_el2 (cpu_regs pb) = r_ttbr0_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_ttbr1_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_ttbr1_el2 (cpu_regs pb) = r_ttbr1_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_vbar_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_vbar_el2 (cpu_regs pb) = r_vbar_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_vdisr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_vdisr_el2 (cpu_regs pb) = r_vdisr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_vncr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_vncr_el2 (cpu_regs pb) = r_vncr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_vpidr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_vpidr_el2 (cpu_regs pb) = r_vpidr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_vsesr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_vsesr_el2 (cpu_regs pb) = r_vsesr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_vstcr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_vstcr_el2 (cpu_regs pb) = r_vstcr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_vsttbr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_vsttbr_el2 (cpu_regs pb) = r_vsttbr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_zcr_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_zcr_el2 (cpu_regs pb) = r_zcr_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_icc_sre_el2:
  forall pa pb (Hrelate: relate_priv pa pb), r_icc_sre_el2 (cpu_regs pb) = r_icc_sre_el2 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_icc_hppir1_el1:
  forall pa pb (Hrelate: relate_priv pa pb), r_icc_hppir1_el1 (cpu_regs pb) = r_icc_hppir1_el1 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_spsr_el3:
  forall pa pb (Hrelate: relate_priv pa pb), r_spsr_el3 (cpu_regs pb) = r_spsr_el3 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_elr_el3:
  forall pa pb (Hrelate: relate_priv pa pb), r_elr_el3 (cpu_regs pb) = r_elr_el3 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_esr_el3:
  forall pa pb (Hrelate: relate_priv pa pb), r_esr_el3 (cpu_regs pb) = r_esr_el3 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_scr_el3:
  forall pa pb (Hrelate: relate_priv pa pb), r_scr_el3 (cpu_regs pb) = r_scr_el3 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.
Lemma relate_priv_r_tpidr_el3:
  forall pa pb (Hrelate: relate_priv pa pb), r_tpidr_el3 (cpu_regs pb) = r_tpidr_el3 (cpu_regs pa).
Proof. intros; inv Hrelate. inv cpu_regs_eq; grewrite; reflexivity. Qed.

Ltac rewrite_sec_rel :=
  repeat
    match goal with
    | [H: relate_priv ?a ?b |- context[asm_regs ?b]] =>
      rewrite (relate_priv_asm_regs a b H)
    | [H: relate_priv ?a ?b |- context[id_regs ?b]] =>
      rewrite (relate_priv_id_regs a b H)
    | [H: relate_priv ?a ?b |- context[buffer ?b]] =>
      rewrite (relate_priv_buffer a b H)
    | [H: relate_priv ?a ?b |- context[ns_regs_el2 ?b]] =>
      rewrite (relate_priv_ns_regs_el2 a b H)
    | [H: relate_priv ?a ?b |- context[realm_params ?b]] =>
      rewrite (relate_priv_realm_params a b H)
    | [H: relate_priv ?a ?b |- context[rec_params ?b]] =>
      rewrite (relate_priv_rec_params a b H)
    | [H: relate_priv ?a ?b |- context[rec_run ?b]] =>
      rewrite (relate_priv_rec_run a b H)
    | [H: relate_priv ?a ?b |- context[retval ?b]] =>
      rewrite (relate_priv_retval a b H)
    | [H: relate_priv ?a ?b |- context[locked_g ?b]] =>
      rewrite (relate_priv_locked_g a b H)
    | [H: relate_priv ?a ?b |- context[wi_last_level ?b]] =>
      rewrite (relate_priv_wi_last_level a b H)
    | [H: relate_priv ?a ?b |- context[wi_llt ?b]] =>
      rewrite (relate_priv_wi_llt a b H)
    | [H: relate_priv ?a ?b |- context[wi_index ?b]] =>
      rewrite (relate_priv_wi_index a b H)
    | [H: relate_priv ?a ?b |- context[rvic_x0 ?b]] =>
      rewrite (relate_priv_rvic_x0 a b H)
    | [H: relate_priv ?a ?b |- context[rvic_x1 ?b]] =>
      rewrite (relate_priv_rvic_x1 a b H)
    | [H: relate_priv ?a ?b |- context[rvic_x2 ?b]] =>
      rewrite (relate_priv_rvic_x2 a b H)
    | [H: relate_priv ?a ?b |- context[rvic_x3 ?b]] =>
      rewrite (relate_priv_rvic_x3 a b H)
    | [H: relate_priv ?a ?b |- context[rvic_target ?b]] =>
      rewrite (relate_priv_rvic_target a b H)
    | [H: relate_priv ?a ?b |- context[rvic_ns_notify ?b]] =>
      rewrite (relate_priv_rvic_ns_notify a b H)
    | [H: relate_priv ?a ?b |- context[psci_x0 ?b]] =>
      rewrite (relate_priv_psci_x0 a b H)
    | [H: relate_priv ?a ?b |- context[psci_x1 ?b]] =>
      rewrite (relate_priv_psci_x1 a b H)
    | [H: relate_priv ?a ?b |- context[psci_x2 ?b]] =>
      rewrite (relate_priv_psci_x2 a b H)
    | [H: relate_priv ?a ?b |- context[psci_x3 ?b]] =>
      rewrite (relate_priv_psci_x3 a b H)
    | [H: relate_priv ?a ?b |- context[psci_forward_x0 ?b]] =>
      rewrite (relate_priv_psci_forward_x0 a b H)
    | [H: relate_priv ?a ?b |- context[psci_forward_x1 ?b]] =>
      rewrite (relate_priv_psci_forward_x1 a b H)
    | [H: relate_priv ?a ?b |- context[psci_forward_x2 ?b]] =>
      rewrite (relate_priv_psci_forward_x2 a b H)
    | [H: relate_priv ?a ?b |- context[psci_forward_x3 ?b]] =>
      rewrite (relate_priv_psci_forward_x3 a b H)
    | [H: relate_priv ?a ?b |- context[psci_forward_psci_call ?b]] =>
      rewrite (relate_priv_psci_forward_psci_call a b H)
    | [H: relate_priv ?a ?b |- context[target_rec ?b]] =>
      rewrite (relate_priv_target_rec a b H)
    | [H: relate_priv ?a ?b |- context[el2_stack ?b]] =>
      rewrite (relate_priv_el2_stack a b H)
    | [H: relate_priv ?a ?b |- context[el3_stack ?b]] =>
      rewrite (relate_priv_el3_stack a b H)
    | [H: relate_priv ?a ?b |- context[ns_regs_el3 ?b]] =>
      rewrite (relate_priv_ns_regs_el3 a b H)
    | [H: relate_priv ?a ?b |- context[realm_regs_el3 ?b]] =>
      rewrite (relate_priv_realm_regs_el3 a b H)
    | [H: relate_priv ?a ?b |- context[cur_rec ?b]] =>
      rewrite (relate_priv_cur_rec a b H)
    | [H: relate_priv ?a ?b |- context[mstage ?b]] =>
      rewrite (relate_priv_mstage a b H)
    | [H: relate_priv ?a ?b |- context[trap_reason ?b]] =>
      rewrite (relate_priv_trap_reason a b H)
    | [H: relate_priv ?a ?b |- context[trap_type ?b]] =>
      rewrite (relate_priv_trap_type a b H)
    | [H: relate_priv ?a ?b |- context[r_lr (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_lr a b H)
    | [H: relate_priv ?a ?b |- context[r_cntp_ctl_el0 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_cntp_ctl_el0 a b H)
    | [H: relate_priv ?a ?b |- context[r_cntp_cval_el0 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_cntp_cval_el0 a b H)
    | [H: relate_priv ?a ?b |- context[r_cntp_tval_el0 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_cntp_tval_el0 a b H)
    | [H: relate_priv ?a ?b |- context[r_cntv_ctl_el0 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_cntv_ctl_el0 a b H)
    | [H: relate_priv ?a ?b |- context[r_cntv_cval_el0 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_cntv_cval_el0 a b H)
    | [H: relate_priv ?a ?b |- context[r_cntv_tval_el0 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_cntv_tval_el0 a b H)
    | [H: relate_priv ?a ?b |- context[r_sp_el0 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_sp_el0 a b H)
    | [H: relate_priv ?a ?b |- context[r_pmcr_el0 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_pmcr_el0 a b H)
    | [H: relate_priv ?a ?b |- context[r_pmuserenr_el0 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_pmuserenr_el0 a b H)
    | [H: relate_priv ?a ?b |- context[r_tpidrro_el0 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_tpidrro_el0 a b H)
    | [H: relate_priv ?a ?b |- context[r_tpidr_el0 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_tpidr_el0 a b H)
    | [H: relate_priv ?a ?b |- context[r_sp_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_sp_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_elr_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_elr_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_spsr_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_spsr_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_csselr_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_csselr_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_sctlr_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_sctlr_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_actlr_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_actlr_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_cpacr_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_cpacr_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_zcr_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_zcr_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_ttbr0_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_ttbr0_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_ttbr1_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_ttbr1_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_tcr_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_tcr_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_esr_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_esr_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_afsr0_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_afsr0_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_afsr1_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_afsr1_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_far_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_far_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_mair_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_mair_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_vbar_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_vbar_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_contextidr_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_contextidr_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_tpidr_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_tpidr_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_amair_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_amair_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_cntkctl_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_cntkctl_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_par_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_par_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_mdscr_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_mdscr_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_mdccint_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_mdccint_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_disr_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_disr_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_mpam0_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_mpam0_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_cnthctl_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_cnthctl_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_cntvoff_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_cntvoff_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_cntpoff_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_cntpoff_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_vmpidr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_vmpidr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_vttbr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_vttbr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_vtcr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_vtcr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_hcr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_hcr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_actlr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_actlr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_afsr0_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_afsr0_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_afsr1_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_afsr1_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_amair_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_amair_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_cptr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_cptr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_elr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_elr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_esr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_esr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_far_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_far_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_hacr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_hacr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_hpfar_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_hpfar_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_hstr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_hstr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_mair_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_mair_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_mpam_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_mpam_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_mpamhcr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_mpamhcr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_pmscr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_pmscr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_sctlr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_sctlr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_scxtnum_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_scxtnum_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_sp_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_sp_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_spsr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_spsr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_tcr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_tcr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_tfsr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_tfsr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_tpidr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_tpidr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_trfcr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_trfcr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_ttbr0_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_ttbr0_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_ttbr1_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_ttbr1_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_vbar_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_vbar_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_vdisr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_vdisr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_vncr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_vncr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_vpidr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_vpidr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_vsesr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_vsesr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_vstcr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_vstcr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_vsttbr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_vsttbr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_zcr_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_zcr_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_icc_sre_el2 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_icc_sre_el2 a b H)
    | [H: relate_priv ?a ?b |- context[r_icc_hppir1_el1 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_icc_hppir1_el1 a b H)
    | [H: relate_priv ?a ?b |- context[r_spsr_el3 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_spsr_el3 a b H)
    | [H: relate_priv ?a ?b |- context[r_elr_el3 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_elr_el3 a b H)
    | [H: relate_priv ?a ?b |- context[r_esr_el3 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_esr_el3 a b H)
    | [H: relate_priv ?a ?b |- context[r_scr_el3 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_scr_el3 a b H)
    | [H: relate_priv ?a ?b |- context[r_tpidr_el3 (cpu_regs ?b)]] =>
      rewrite (relate_priv_r_tpidr_el3 a b H)
    | [H: relate_share ?a ?b |- context[gpt ?b]] =>
      rewrite (relate_share_gpt a b H)
    | [H: relate_share ?a ?b |- context[gpt_lk ?b]] =>
      rewrite (relate_share_gpt_lk a b H)
    | [H: relate_share ?a ?b |- context[tlbs ?b]] =>
      rewrite (relate_share_tlbs a b H)
    | [H: relate_share ?a ?b |- context[rtts ?b]] =>
      rewrite (relate_share_rtts a b H)
    | [H: relate_share ?a ?b |- context[glock ((gs ?b) @ ?gidx)]] =>
      rewrite (relate_share_glock a b H gidx)
    | [H: relate_share ?a ?b |- context[gref ((gs ?b) @ ?gidx)]] =>
      rewrite (relate_share_gref a b H gidx)
    | [H: relate_share ?a ?b |- context[gtype ((gs ?b) @ ?gidx)]] =>
      rewrite (relate_share_gtype a b H gidx)
    | [H: relate_share ?a ?b |- context[gcnt ((gs ?b) @ ?gidx)]] =>
      rewrite (relate_share_gcnt a b H gidx)
    | [H: relate_share ?a ?b |- context[ginfo ((gs ?b) @ ?gidx)]] =>
      rewrite (relate_share_ginfo a b H gidx)
    | [H: relate_share ?a ?b |- context[gro ((gs ?b) @ ?gidx)]] =>
      rewrite (relate_share_gro a b H gidx)
    | [H: relate_share ?a ?b |- context[gaux ((gs ?b) @ ?gidx)]] =>
      rewrite (relate_share_gaux a b H gidx)
    | [H: relate_share ?a ?b |- context[g_realm_state (gnorm ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_realm_state a b H gidx)
    | [H: relate_share ?a ?b |- context[g_par_base (gnorm ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_par_base a b H gidx)
    | [H: relate_share ?a ?b |- context[g_par_end (gnorm ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_par_end a b H gidx)
    | [H: relate_share ?a ?b |- context[g_rec_list (gnorm ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_rec_list a b H gidx)
    | [H: relate_share ?a ?b |- context[g_rtt (gnorm ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_rtt a b H gidx)
    | [H: relate_share ?a ?b |- context[g_measurement_algo (gnorm ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_measurement_algo a b H gidx)
    | [H: relate_share ?a ?b |- context[g_measurement_ctx (gnorm ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_measurement_ctx a b H gidx)
    | [H: relate_share ?a ?b |- context[g_measurement (gnorm ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_measurement a b H gidx)
    | [H: relate_share ?a ?b |- context[g_recs (gnorm ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_recs a b H gidx)
    | [H: relate_share ?a ?b |- context[g_rvic (gnorm ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_rvic a b H gidx)
    | [H: relate_share ?a ?b |- context[g_runnable (gnorm ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_runnable a b H gidx)
    | [H: relate_share ?a ?b |- context[g_pc (grec ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_pc a b H gidx)
    | [H: relate_share ?a ?b |- context[g_pstate (grec ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_pstate a b H gidx)
    | [H: relate_share ?a ?b |- context[g_vtimer (grec ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_vtimer a b H gidx)
    | [H: relate_share ?a ?b |- context[g_ptimer (grec ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_ptimer a b H gidx)
    | [H: relate_share ?a ?b |- context[g_dispose_pending (grec ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_dispose_pending a b H gidx)
    | [H: relate_share ?a ?b |- context[g_dispose_addr (grec ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_dispose_addr a b H gidx)
    | [H: relate_share ?a ?b |- context[g_dispose_size (grec ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_dispose_size a b H gidx)
    | [H: relate_share ?a ?b |- context[g_rec_rd (grec ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_rec_rd a b H gidx)
    | [H: relate_share ?a ?b |- context[g_rec_par_base (grec ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_rec_par_base a b H gidx)
    | [H: relate_share ?a ?b |- context[g_rec_par_end (grec ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_rec_par_end a b H gidx)
    | [H: relate_share ?a ?b |- context[g_rec_rec_list (grec ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_rec_rec_list a b H gidx)
    | [H: relate_share ?a ?b |- context[g_esr (grec ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_esr a b H gidx)
    | [H: relate_share ?a ?b |- context[g_running (grec ((gs ?b) @ ?gidx))]] =>
      rewrite (relate_share_g_running a b H gidx)
    | [H: relate_share ?a ?b |- context[ref_accessible (((gs ?b) @ ?gidx)) ?c]] =>
      rewrite (relate_share_ref_accessible a b H gidx c)
    end.
