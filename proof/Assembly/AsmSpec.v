Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Smallstep.
Require Import Events.
Require Import Globalenvs.
Require Import Memory.
Require Import Values.
Require Import Constants.
Require Import RData.
Require Import Assembly.Asm.
Require Import AsmCode.
Require Import CommonLib.

Variable ge: genv.

Definition el3_sync_lel_spec (adt: RData) :=
  rely prop_dec (get_pc adt = (el3_sync_lel, 0));
  rely (a_EL3 (asm_regs (priv adt)));
  let cregs := cpu_regs (priv adt) in
  rely (r_tpidr_el3 cregs =? percpu_data_start);
  match (r_x0 cregs),  (r_x1 cregs),  (r_x2 cregs),  (r_x3 cregs),  (r_x4 cregs),  (r_lr cregs), (r_esr_el3 cregs), (r_scr_el3 cregs) with
  | x0', x1', x2', x3', x4', lr', esr', scr' =>
    rely is_int64 x1';
    let stack0 := el3_stack (priv adt) in
    let stack' := lr' :: x4' :: x3' :: x2' :: x1' :: x0' :: stack0 in
    if (Z.land esr' ESR_EC) =? ESR_EC_SMC then
      if Z.land esr' ESR_EC_SMC_IMM16 =? 0 then
        if Z.land scr' SCR_WORLD_MASK =? SCR_REALM_WORLD then
        (* realm_smc_handler *)
          if Z.land x0' NOT_SMC_STD_CALL_MASK =? SMC_STD_CALL_BASE then
            Some adt
          else
            (* baremore_to_ns *)
            let cregs := cpu_regs (priv adt) in
            let realm_regs_el3' :=
                (realm_regs_el3 (priv adt)) {r_spsr_el3: (r_spsr_el3 cregs)} {r_elr_el3: (r_elr_el3 cregs)} {r_actlr_el2: (r_actlr_el2 cregs)}
                                      {r_afsr0_el2: (r_afsr0_el2 cregs)} {r_afsr1_el2: (r_afsr1_el2 cregs)} {r_amair_el2: (r_amair_el2 cregs)}
                                      {r_cnthctl_el2: (r_cnthctl_el2 cregs)} {r_cntvoff_el2: (r_cntvoff_el2 cregs)}
                                      {r_cptr_el2: (r_cptr_el2 cregs)} {r_elr_el2: (r_elr_el2 cregs)} {r_esr_el2: (r_esr_el2 cregs)}
                                      {r_far_el2: (r_far_el2 cregs)} {r_hacr_el2: (r_hacr_el2 cregs)} {r_hcr_el2: (r_hcr_el2 cregs)}
                                      {r_hpfar_el2: (r_hpfar_el2 cregs)} {r_hstr_el2: (r_hstr_el2 cregs)} {r_mair_el2: (r_mair_el2 cregs)}
                                      {r_mpam_el2: (r_mpam_el2 cregs)} {r_mpamhcr_el2: (r_mpamhcr_el2 cregs)} {r_pmscr_el2: (r_pmscr_el2 cregs)}
                                      {r_sctlr_el2: (r_sctlr_el2 cregs)} {r_scxtnum_el2: (r_scxtnum_el2 cregs)} {r_sp_el2: (r_sp_el2 cregs)}
                                      {r_spsr_el2: (r_spsr_el2 cregs)} {r_tcr_el2: (r_tcr_el2 cregs)} {r_tfsr_el2: (r_tfsr_el2 cregs)}
                                      {r_tpidr_el2: (r_tpidr_el2 cregs)} {r_trfcr_el2: (r_trfcr_el2 cregs)} {r_ttbr0_el2: (r_ttbr0_el2 cregs)}
                                      {r_ttbr1_el2: (r_ttbr1_el2 cregs)} {r_vbar_el2: (r_vbar_el2 cregs)} {r_vdisr_el2: (r_vdisr_el2 cregs)}
                                      {r_vmpidr_el2: (r_vmpidr_el2 cregs)} {r_vncr_el2: (r_vncr_el2 cregs)} {r_vpidr_el2: (r_vpidr_el2 cregs)}
                                      {r_vsesr_el2: (r_vsesr_el2 cregs)} {r_vstcr_el2: (r_vstcr_el2 cregs)} {r_vsttbr_el2: (r_vsttbr_el2 cregs)}
                                      {r_vtcr_el2: (r_vtcr_el2 cregs)} {r_vttbr_el2: (r_vttbr_el2 cregs)} {r_zcr_el2: (r_zcr_el2 cregs)} in
            let nregs := (ns_regs_el3 (priv adt)) in
            let cregs' :=
                (cpu_regs (priv adt)) {r_spsr_el3: (r_spsr_el3 nregs)} {r_elr_el3: (r_elr_el3 nregs)} {r_actlr_el2: (r_actlr_el2 nregs)}
                                {r_afsr0_el2: (r_afsr0_el2 nregs)} {r_afsr1_el2: (r_afsr1_el2 nregs)} {r_amair_el2: (r_amair_el2 nregs)}
                                {r_cnthctl_el2: (r_cnthctl_el2 nregs)} {r_cntvoff_el2: (r_cntvoff_el2 nregs)}
                                {r_cptr_el2: (r_cptr_el2 nregs)} {r_elr_el2: (r_elr_el2 nregs)} {r_esr_el2: (r_esr_el2 nregs)}
                                {r_far_el2: (r_far_el2 nregs)} {r_hacr_el2: (r_hacr_el2 nregs)} {r_hcr_el2: (r_hcr_el2 nregs)}
                                {r_hpfar_el2: (r_hpfar_el2 nregs)} {r_hstr_el2: (r_hstr_el2 nregs)} {r_mair_el2: (r_mair_el2 nregs)}
                                {r_mpam_el2: (r_mpam_el2 nregs)} {r_mpamhcr_el2: (r_mpamhcr_el2 nregs)} {r_pmscr_el2: (r_pmscr_el2 nregs)}
                                {r_sctlr_el2: (r_sctlr_el2 nregs)} {r_scxtnum_el2: (r_scxtnum_el2 nregs)} {r_sp_el2: (r_sp_el2 nregs)}
                                {r_spsr_el2: (r_spsr_el2 nregs)} {r_tcr_el2: (r_tcr_el2 nregs)} {r_tfsr_el2: (r_tfsr_el2 nregs)}
                                {r_tpidr_el2: (r_tpidr_el2 nregs)} {r_trfcr_el2: (r_trfcr_el2 nregs)} {r_ttbr0_el2: (r_ttbr0_el2 nregs)}
                                {r_ttbr1_el2: (r_ttbr1_el2 nregs)} {r_vbar_el2: (r_vbar_el2 nregs)} {r_vdisr_el2: (r_vdisr_el2 nregs)}
                                {r_vmpidr_el2: (r_vmpidr_el2 nregs)} {r_vncr_el2: (r_vncr_el2 nregs)} {r_vpidr_el2: (r_vpidr_el2 nregs)}
                                {r_vsesr_el2: (r_vsesr_el2 nregs)} {r_vstcr_el2: (r_vstcr_el2 nregs)} {r_vsttbr_el2: (r_vsttbr_el2 nregs)}
                                {r_vtcr_el2: (r_vtcr_el2 nregs)} {r_vttbr_el2: (r_vttbr_el2 nregs)} {r_zcr_el2: (r_zcr_el2 nregs)}
                                {r_scr_el3: SCR_EL3_NS} in
            Some adt {priv: (priv adt) {cpu_regs: cregs'} {realm_regs_el3: realm_regs_el3'}}
        else
          if Z.land x0' NOT_SMC_ARM_ARCH_CALL_MASK =? SMC_ARM_ARCH_CALL_BASE then
            (* baremore_to_rmm *)
            let cregs := cpu_regs (priv adt) in
            let ns_regs_el3' :=
                (ns_regs_el3 (priv adt)) {r_spsr_el3: (r_spsr_el3 cregs)} {r_elr_el3: (r_elr_el3 cregs)} {r_actlr_el2: (r_actlr_el2 cregs)}
                                    {r_afsr0_el2: (r_afsr0_el2 cregs)} {r_afsr1_el2: (r_afsr1_el2 cregs)} {r_amair_el2: (r_amair_el2 cregs)}
                                    {r_cnthctl_el2: (r_cnthctl_el2 cregs)} {r_cntvoff_el2: (r_cntvoff_el2 cregs)}
                                    {r_cptr_el2: (r_cptr_el2 cregs)} {r_elr_el2: (r_elr_el2 cregs)} {r_esr_el2: (r_esr_el2 cregs)}
                                    {r_far_el2: (r_far_el2 cregs)} {r_hacr_el2: (r_hacr_el2 cregs)} {r_hcr_el2: (r_hcr_el2 cregs)}
                                    {r_hpfar_el2: (r_hpfar_el2 cregs)} {r_hstr_el2: (r_hstr_el2 cregs)} {r_mair_el2: (r_mair_el2 cregs)}
                                    {r_mpam_el2: (r_mpam_el2 cregs)} {r_mpamhcr_el2: (r_mpamhcr_el2 cregs)} {r_pmscr_el2: (r_pmscr_el2 cregs)}
                                    {r_sctlr_el2: (r_sctlr_el2 cregs)} {r_scxtnum_el2: (r_scxtnum_el2 cregs)} {r_sp_el2: (r_sp_el2 cregs)}
                                    {r_spsr_el2: (r_spsr_el2 cregs)} {r_tcr_el2: (r_tcr_el2 cregs)} {r_tfsr_el2: (r_tfsr_el2 cregs)}
                                    {r_tpidr_el2: (r_tpidr_el2 cregs)} {r_trfcr_el2: (r_trfcr_el2 cregs)} {r_ttbr0_el2: (r_ttbr0_el2 cregs)}
                                    {r_ttbr1_el2: (r_ttbr1_el2 cregs)} {r_vbar_el2: (r_vbar_el2 cregs)} {r_vdisr_el2: (r_vdisr_el2 cregs)}
                                    {r_vmpidr_el2: (r_vmpidr_el2 cregs)} {r_vncr_el2: (r_vncr_el2 cregs)} {r_vpidr_el2: (r_vpidr_el2 cregs)}
                                    {r_vsesr_el2: (r_vsesr_el2 cregs)} {r_vstcr_el2: (r_vstcr_el2 cregs)} {r_vsttbr_el2: (r_vsttbr_el2 cregs)}
                                    {r_vtcr_el2: (r_vtcr_el2 cregs)} {r_vttbr_el2: (r_vttbr_el2 cregs)} {r_zcr_el2: (r_zcr_el2 cregs)}
            in
            let rregs := (realm_regs_el3 (priv adt)) in
            let cregs' :=
                (cpu_regs (priv adt)) {r_spsr_el3: (r_spsr_el3 rregs)} {r_elr_el3: rmm_handler} {r_actlr_el2: (r_actlr_el2 rregs)}
                                {r_afsr0_el2: (r_afsr0_el2 rregs)} {r_afsr1_el2: (r_afsr1_el2 rregs)} {r_amair_el2: (r_amair_el2 rregs)}
                                {r_cnthctl_el2: (r_cnthctl_el2 rregs)} {r_cntvoff_el2: (r_cntvoff_el2 rregs)}
                                {r_cptr_el2: (r_cptr_el2 rregs)} {r_elr_el2: (r_elr_el2 rregs)} {r_esr_el2: (r_esr_el2 rregs)}
                                {r_far_el2: (r_far_el2 rregs)} {r_hacr_el2: (r_hacr_el2 rregs)} {r_hcr_el2: (r_hcr_el2 rregs)}
                                {r_hpfar_el2: (r_hpfar_el2 rregs)} {r_hstr_el2: (r_hstr_el2 rregs)} {r_mair_el2: (r_mair_el2 rregs)}
                                {r_mpam_el2: (r_mpam_el2 rregs)} {r_mpamhcr_el2: (r_mpamhcr_el2 rregs)} {r_pmscr_el2: (r_pmscr_el2 rregs)}
                                {r_sctlr_el2: (r_sctlr_el2 rregs)} {r_scxtnum_el2: (r_scxtnum_el2 rregs)} {r_sp_el2: (r_sp_el2 rregs)}
                                {r_spsr_el2: (r_spsr_el2 rregs)} {r_tcr_el2: (r_tcr_el2 rregs)} {r_tfsr_el2: (r_tfsr_el2 rregs)}
                                {r_tpidr_el2: (r_tpidr_el2 rregs)} {r_trfcr_el2: (r_trfcr_el2 rregs)} {r_ttbr0_el2: (r_ttbr0_el2 rregs)}
                                {r_ttbr1_el2: (r_ttbr1_el2 rregs)} {r_vbar_el2: (r_vbar_el2 rregs)} {r_vdisr_el2: (r_vdisr_el2 rregs)}
                                {r_vmpidr_el2: (r_vmpidr_el2 rregs)} {r_vncr_el2: (r_vncr_el2 rregs)} {r_vpidr_el2: (r_vpidr_el2 rregs)}
                                {r_vsesr_el2: (r_vsesr_el2 rregs)} {r_vstcr_el2: (r_vstcr_el2 rregs)} {r_vsttbr_el2: (r_vsttbr_el2 rregs)}
                                {r_vtcr_el2: (r_vtcr_el2 rregs)} {r_vttbr_el2: (r_vttbr_el2 rregs)} {r_zcr_el2: (r_zcr_el2 rregs)}
                                {r_scr_el3: SCR_EL3_REALM} in
            Some adt {priv: (priv adt) {cpu_regs: cregs'} {ns_regs_el3: ns_regs_el3'}}
          else None
      else None
    else None
  end.
