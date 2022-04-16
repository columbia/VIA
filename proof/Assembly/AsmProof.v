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
Require Import Asm.
Require Import AsmCode.
Require Import CommonLib.
Require Import RefTactics.
Require Import Assembly.Asm.
Require Import Assembly.AsmCode.
Require Import Assembly.AsmSpec.
Require Import RefTactics.

Variable ge: genv.

Inductive StarStep: RData -> RData -> Prop :=
| NoStep: forall d, StarStep d d
| OneStep:
    forall d d' d'',
      step ge d d' -> StarStep d' d'' -> StarStep d d''.

Ltac asm_one_internal_step Hf :=
  eapply OneStep; [
    eapply exec_step_internal; repeat autounfold;
    [simpl; grewrite; reflexivity | eapply Hf | reflexivity |
     simpl; repeat (autounfold; simpl; repeat grewrite; simpl);
     repeat (simpl_update_reg; simpl; repeat grewrite; simpl);
     repeat simpl_field; repeat swap_fields; repeat simpl_field; simpl_htarget; try reflexivity]
  | idtac ].

Ltac asm_prep_one_internal_step Hf :=
  eapply OneStep; [
    eapply exec_step_internal; repeat autounfold;
    [simpl; grewrite; reflexivity | eapply Hf | reflexivity |]|].


Definition el3_sync_lel_func : function :=
  {| fn_sig := null_signature;
     fn_code := el3_sync_lel_insn |}.

Definition save_el2_state_func : function :=
  {| fn_sig := null_signature;
     fn_code := save_el2_state_insn |}.

Definition restore_el2_state_func : function :=
  {| fn_sig := null_signature;
     fn_code := restore_el2_state_insn |}.

Hypothesis el3_sync_lel_function:
   Genv.find_funct_ptr ge (Z.to_pos el3_sync_lel) = Some (Internal el3_sync_lel_func).
Hypothesis save_el2_state_function:
   Genv.find_funct_ptr ge (Z.to_pos save_el2_state) = Some (Internal save_el2_state_func).
Hypothesis restore_el2_state_function:
   Genv.find_funct_ptr ge (Z.to_pos restore_el2_state) = Some (Internal restore_el2_state_func).

Variable f_handle_std_service: external_function.
Hypothesis handle_std_service_function:
   Genv.find_funct_ptr ge (Z.to_pos handle_std_service) = Some (External f_handle_std_service).

Hint Unfold
     get_creg set_creg get_pc set_pc get_sp set_sp extend_stack shrink_stack
     nextinstr compare_long eval_testcond eval_testbit eval_testzero
     mem_load mem_store get_stack set_stack goto_label RA get_el3_regs set_el3_regs.

Lemma realm_save_el2_state:
  forall d lb ofs d'
    (Hpc: get_pc d = (save_el2_state, 0))
    (Hlabel: get_creg RA d / 10000 = lb)
    (Hoffset: get_creg RA d mod 10000 = ofs)
    (Harg: get_creg x0 d = percpu_data_start + CPUSTATE_REALM_OFFSET),
    let cregs := cpu_regs (priv d) in
    let realm_regs' :=
        (realm_regs_el3 (priv d)) {r_spsr_el3: (r_spsr_el3 cregs)} {r_elr_el3: (r_elr_el3 cregs)} {r_actlr_el2: (r_actlr_el2 cregs)}
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
    let d0 := d {priv: (priv d) {realm_regs_el3: realm_regs'}
                                {cpu_regs: (cpu_regs (priv d)) {r_x1: r_zcr_el2 (cpu_regs (priv d))}
                                                               {r_x2: r_vttbr_el2 (cpu_regs (priv d))}
                                                               {r_x30: -1}}
                                {asm_regs : ((asm_regs (priv d)) {a_CZ : None} {a_PC: (lb, ofs)})}} in
    StarStep d0 d' -> StarStep d d'.
Proof.
  intros until d'.
  repeat autounfold. repeat simpl_update_reg. repeat simpl_field. repeat swap_fields. simpl. intros.
  assert(r_x0 (cpu_regs (priv d)) =? percpu_data_start + 4096 = false).
  grewrite. bool_rel. omega.
  assert(r_x0 (cpu_regs (priv d)) =? percpu_data_start + 0 = true).
  grewrite. bool_rel. omega.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  apply H.
Qed.

Lemma ns_save_el2_state:
  forall d lb ofs d'
    (Hpc: get_pc d = (save_el2_state, 0))
    (Hlabel: get_creg RA d / 10000 = lb)
    (Hoffset: get_creg RA d mod 10000 = ofs)
    (Harg: get_creg x0 d = percpu_data_start + CPUSTATE_NS_OFFSET),
    let cregs := cpu_regs (priv d) in
    let ns_regs' :=
        (ns_regs_el3 (priv d)) {r_spsr_el3: (r_spsr_el3 cregs)} {r_elr_el3: (r_elr_el3 cregs)} {r_actlr_el2: (r_actlr_el2 cregs)}
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
    let d0 := d {priv: (priv d) {ns_regs_el3: ns_regs'}
                                {cpu_regs: (cpu_regs (priv d)) {r_x1: r_zcr_el2 (cpu_regs (priv d))}
                                                               {r_x2: r_vttbr_el2 (cpu_regs (priv d))}
                                                               {r_x30: -1}}
                                {asm_regs : ((asm_regs (priv d)) {a_CZ : None} {a_PC: (lb, ofs)})}} in
    StarStep d0 d' -> StarStep d d'.
Proof.
  intros until d'.
  repeat autounfold. repeat simpl_update_reg. repeat simpl_field. repeat swap_fields. simpl. intros.
  assert(r_x0 (cpu_regs (priv d)) =? percpu_data_start + 4096 = true).
  grewrite. bool_rel. omega.
  assert(r_x0 (cpu_regs (priv d)) =? percpu_data_start + 0 = false).
  grewrite. bool_rel. omega.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  asm_one_internal_step save_el2_state_function.
  apply H.
Qed.


Lemma ns_restore_el2_state:
  forall d lb ofs d'
    (Hpc: get_pc d = (restore_el2_state, 0))
    (Hlabel: get_creg RA d / 10000 = lb)
    (Hoffset: get_creg RA d mod 10000 = ofs)
    (Harg: get_creg x0 d = percpu_data_start + CPUSTATE_NS_OFFSET),
    let cregs := ns_regs_el3 (priv d) in
    let ns_regs' :=
        (cpu_regs (priv d)) {r_spsr_el3: (r_spsr_el3 cregs)} {r_elr_el3: (r_elr_el3 cregs)} {r_actlr_el2: (r_actlr_el2 cregs)}
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
    let d0 := d {priv: (priv d)
                         {cpu_regs: ns_regs' {r_x1: r_zcr_el2 (ns_regs_el3 (priv d))}
                                             {r_x2: r_vttbr_el2 (ns_regs_el3 (priv d))}
                                             {r_x30: -1}}
                                {asm_regs : ((asm_regs (priv d)) {a_CZ : None} {a_PC: (lb, ofs)})}} in
    StarStep d0 d' -> StarStep d d'.
Proof.
  intros until d'.
  repeat autounfold. repeat simpl_update_reg. repeat simpl_field. repeat swap_fields. simpl. intros.
  assert(r_x0 (cpu_regs (priv d)) =? percpu_data_start + 4096 = true).
  grewrite. bool_rel. omega.
  assert(r_x0 (cpu_regs (priv d)) =? percpu_data_start + 0 = false).
  grewrite. bool_rel. omega.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  apply H.
Qed.

Lemma realm_restore_el2_state:
  forall d lb ofs d'
    (Hpc: get_pc d = (restore_el2_state, 0))
    (Hlabel: get_creg RA d / 10000 = lb)
    (Hoffset: get_creg RA d mod 10000 = ofs)
    (Harg: get_creg x0 d = percpu_data_start + CPUSTATE_REALM_OFFSET),
    let cregs := realm_regs_el3 (priv d) in
    let realm_regs' :=
        (cpu_regs (priv d)) {r_spsr_el3: (r_spsr_el3 cregs)} {r_elr_el3: (r_elr_el3 cregs)} {r_actlr_el2: (r_actlr_el2 cregs)}
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
    let d0 := d {priv: (priv d)
                         {cpu_regs: realm_regs' {r_x1: r_zcr_el2 (realm_regs_el3 (priv d))}
                                             {r_x2: r_vttbr_el2 (realm_regs_el3 (priv d))}
                                             {r_x30: -1}}
                                {asm_regs : ((asm_regs (priv d)) {a_CZ : None} {a_PC: (lb, ofs)})}} in
    StarStep d0 d' -> StarStep d d'.
Proof.
  intros until d'.
  repeat autounfold. repeat simpl_update_reg. repeat simpl_field. repeat swap_fields. simpl. intros.
  assert(r_x0 (cpu_regs (priv d)) =? percpu_data_start + 4096 = false).
  grewrite. bool_rel. omega.
  assert(r_x0 (cpu_regs (priv d)) =? percpu_data_start + 0 = true).
  grewrite. bool_rel. omega.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  asm_one_internal_step restore_el2_state_function.
  apply H.
Qed.
