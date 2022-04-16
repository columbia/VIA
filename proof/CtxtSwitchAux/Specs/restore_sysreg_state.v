Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition restore_sysreg_state_spec (rec: Pointer) (adt: RData) : option RData :=
    rely (peq (base rec) buffer_loc);
    when gidx == (buffer (priv adt)) @ (offset rec);
    let gn := (gs (share adt)) @ gidx in
    rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
    rely (ref_accessible gn CPU_ID);
    let sysregs := g_regs (grec gn) in
    rely regs_is_int64_dec sysregs;
    Some adt {priv: (priv adt)
                      {cpu_regs: (cpu_regs (priv adt))
                                   {r_sp_el0: (r_sp_el0 sysregs)}
                                   {r_sp_el1: (r_sp_el1 sysregs)}
                                   {r_elr_el1: (r_elr_el1 sysregs)}
                                   {r_spsr_el1: (r_spsr_el1 sysregs)}
                                   {r_pmcr_el0: (r_pmcr_el0 sysregs)}
                                   {r_pmuserenr_el0: (r_pmuserenr_el0 sysregs)}
                                   {r_tpidrro_el0: (r_tpidrro_el0 sysregs)}
                                   {r_tpidr_el0: (r_tpidr_el0 sysregs)}
                                   {r_csselr_el1: (r_csselr_el1 sysregs)}
                                   {r_sctlr_el1: (r_sctlr_el1 sysregs)}
                                   {r_actlr_el1: (r_actlr_el1 sysregs)}
                                   {r_cpacr_el1: (r_cpacr_el1 sysregs)}
                                   {r_zcr_el1: (r_zcr_el1 sysregs)}
                                   {r_ttbr0_el1: (r_ttbr0_el1 sysregs)}
                                   {r_ttbr1_el1: (r_ttbr1_el1 sysregs)}
                                   {r_tcr_el1: (r_tcr_el1 sysregs)}
                                   {r_esr_el1: (r_esr_el1 sysregs)}
                                   {r_afsr0_el1: (r_afsr0_el1 sysregs)}
                                   {r_afsr1_el1: (r_afsr1_el1 sysregs)}
                                   {r_far_el1: (r_far_el1 sysregs)}
                                   {r_mair_el1: (r_mair_el1 sysregs)}
                                   {r_vbar_el1: (r_vbar_el1 sysregs)}
                                   {r_contextidr_el1: (r_contextidr_el1 sysregs)}
                                   {r_tpidr_el1: (r_tpidr_el1 sysregs)}
                                   {r_amair_el1: (r_amair_el1 sysregs)}
                                   {r_cntkctl_el1: (r_cntkctl_el1 sysregs)}
                                   {r_par_el1: (r_par_el1 sysregs)}
                                   {r_mdscr_el1: (r_mdscr_el1 sysregs)}
                                   {r_mdccint_el1: (r_mdccint_el1 sysregs)}
                                   {r_disr_el1: (r_disr_el1 sysregs)}
                                   {r_mpam0_el1: (r_mpam0_el1 sysregs)}
                                   {r_vmpidr_el2: (r_vmpidr_el2 sysregs)}
                                   {r_cnthctl_el2: (r_cnthctl_el2 sysregs)}
                                   {r_cntvoff_el2: (r_cntvoff_el2 sysregs)}
                                   {r_cntp_ctl_el0: (r_cntp_ctl_el0 sysregs)}
                                   {r_cntp_cval_el0: (r_cntp_cval_el0 sysregs)}
                                   {r_cntv_ctl_el0: (r_cntv_ctl_el0 sysregs)}
                                   {r_cntv_cval_el0: (r_cntv_cval_el0 sysregs)}}}.

End Spec.

