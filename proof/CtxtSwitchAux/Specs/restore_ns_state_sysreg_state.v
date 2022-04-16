Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition restore_ns_state_sysreg_state_spec  (adt: RData) : option RData :=
      rely regs_is_int64_dec (ns_regs_el2 (priv adt));
      Some adt {priv: (priv adt)
                        {cpu_regs: (cpu_regs (priv adt))
                                     {r_sp_el0: (r_sp_el0 (ns_regs_el2 (priv adt)))}
                                     {r_sp_el1: (r_sp_el1 (ns_regs_el2 (priv adt)))}
                                     {r_elr_el1: (r_elr_el1 (ns_regs_el2 (priv adt)))}
                                     {r_spsr_el1: (r_spsr_el1 (ns_regs_el2 (priv adt)))}
                                     {r_pmcr_el0: (r_pmcr_el0 (ns_regs_el2 (priv adt)))}
                                     {r_pmuserenr_el0: (r_pmuserenr_el0 (ns_regs_el2 (priv adt)))}
                                     {r_tpidrro_el0: (r_tpidrro_el0 (ns_regs_el2 (priv adt)))}
                                     {r_tpidr_el0: (r_tpidr_el0 (ns_regs_el2 (priv adt)))}
                                     {r_csselr_el1: (r_csselr_el1 (ns_regs_el2 (priv adt)))}
                                     {r_sctlr_el1: (r_sctlr_el1 (ns_regs_el2 (priv adt)))}
                                     {r_actlr_el1: (r_actlr_el1 (ns_regs_el2 (priv adt)))}
                                     {r_cpacr_el1: (r_cpacr_el1 (ns_regs_el2 (priv adt)))}
                                     {r_zcr_el1: (r_zcr_el1 (ns_regs_el2 (priv adt)))}
                                     {r_ttbr0_el1: (r_ttbr0_el1 (ns_regs_el2 (priv adt)))}
                                     {r_ttbr1_el1: (r_ttbr1_el1 (ns_regs_el2 (priv adt)))}
                                     {r_tcr_el1: (r_tcr_el1 (ns_regs_el2 (priv adt)))}
                                     {r_esr_el1: (r_esr_el1 (ns_regs_el2 (priv adt)))}
                                     {r_afsr0_el1: (r_afsr0_el1 (ns_regs_el2 (priv adt)))}
                                     {r_afsr1_el1: (r_afsr1_el1 (ns_regs_el2 (priv adt)))}
                                     {r_far_el1: (r_far_el1 (ns_regs_el2 (priv adt)))}
                                     {r_mair_el1: (r_mair_el1 (ns_regs_el2 (priv adt)))}
                                     {r_vbar_el1: (r_vbar_el1 (ns_regs_el2 (priv adt)))}

                                     {r_contextidr_el1: (r_contextidr_el1 (ns_regs_el2 (priv adt)))}
                                     {r_tpidr_el1: (r_tpidr_el1 (ns_regs_el2 (priv adt)))}
                                     {r_amair_el1: (r_amair_el1 (ns_regs_el2 (priv adt)))}
                                     {r_cntkctl_el1: (r_cntkctl_el1 (ns_regs_el2 (priv adt)))}
                                     {r_par_el1: (r_par_el1 (ns_regs_el2 (priv adt)))}
                                     {r_mdscr_el1: (r_mdscr_el1 (ns_regs_el2 (priv adt)))}
                                     {r_mdccint_el1: (r_mdccint_el1 (ns_regs_el2 (priv adt)))}
                                     {r_disr_el1: (r_disr_el1 (ns_regs_el2 (priv adt)))}
                                     {r_mpam0_el1: (r_mpam0_el1 (ns_regs_el2 (priv adt)))}
                                     {r_vmpidr_el2: (r_vmpidr_el2 (ns_regs_el2 (priv adt)))}

                                     {r_cnthctl_el2: (r_cnthctl_el2 (ns_regs_el2 (priv adt)))}
                                     {r_cntvoff_el2: (r_cntvoff_el2 (ns_regs_el2 (priv adt)))}
                                     {r_cntp_ctl_el0: (r_cntp_ctl_el0 (ns_regs_el2 (priv adt)))}
                                     {r_cntp_cval_el0: (r_cntp_cval_el0 (ns_regs_el2 (priv adt)))}
                                     {r_cntv_ctl_el0: (r_cntv_ctl_el0 (ns_regs_el2 (priv adt)))}
                                     {r_cntv_cval_el0: (r_cntv_cval_el0 (ns_regs_el2 (priv adt)))}}}.

End Spec.

