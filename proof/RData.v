Require Import Coqlib.
Require Import Maps.
Require Import GenSem.

Require Import Constants.
Require Import CommonLib.

Open Local Scope Z_scope.

Section DataType.

  Definition null_loc := 1%positive.
  Definition error_loc := 2%positive.
  Definition ginfo_loc := 3%positive.
  Definition buffer_loc := 4%positive.
  Definition pg_loc := 5%positive.
  Definition vtimer_loc := 6%positive.
  Definition ptimer_loc := 7%positive.
  Definition rvic_loc := 8%positive.
  Definition bitmap_loc := 9%positive.
  Definition rvic_pending_loc := 10%positive.
  Definition rvic_mask_loc := 11%positive.
  Definition spinlock_loc := 12%positive.

  Definition base (p: Pointer) := fst p.
  Definition offset (p: Pointer) := snd p.

  Definition NULL := (null_loc, 0).

  Record RegState :=
    mkRegState {
        r_x0: Z;
        r_x1: Z;
        r_x2: Z;
        r_x3: Z;
        r_x4: Z;
        r_x5: Z;
        r_x6: Z;
        r_x7: Z;
        r_x8: Z;
        r_x9: Z;
        r_x10: Z;
        r_x11: Z;
        r_x12: Z;
        r_x13: Z;
        r_x14: Z;
        r_x15: Z;
        r_x16: Z;
        r_x17: Z;
        r_x18: Z;
        r_x19: Z;
        r_x20: Z;
        r_x21: Z;
        r_x22: Z;
        r_x23: Z;
        r_x24: Z;
        r_x25: Z;
        r_x26: Z;
        r_x27: Z;
        r_x28: Z;
        r_x29: Z;
        r_x30: Z;
        r_lr: Z;
        r_cntp_ctl_el0: Z;
        r_cntp_cval_el0: Z;
        r_cntp_tval_el0: Z;
        r_cntv_ctl_el0: Z;
        r_cntv_cval_el0: Z;
        r_cntv_tval_el0: Z;
        r_sp_el0: Z;
        r_pmcr_el0: Z;
        r_pmuserenr_el0: Z;
        r_tpidrro_el0: Z;
        r_tpidr_el0: Z;
        r_sp_el1: Z;
        r_elr_el1: Z;
        r_spsr_el1: Z;
        r_csselr_el1: Z;
        r_sctlr_el1: Z;
        r_actlr_el1: Z;
        r_cpacr_el1: Z;
        r_zcr_el1: Z;
        r_ttbr0_el1: Z;
        r_ttbr1_el1: Z;
        r_tcr_el1: Z;
        r_esr_el1: Z;
        r_afsr0_el1: Z;
        r_afsr1_el1: Z;
        r_far_el1: Z;
        r_mair_el1: Z;
        r_vbar_el1: Z;
        r_contextidr_el1: Z;
        r_tpidr_el1: Z;
        r_amair_el1: Z;
        r_cntkctl_el1: Z;
        r_par_el1: Z;
        r_mdscr_el1: Z;
        r_mdccint_el1: Z;
        r_disr_el1: Z;
        r_mpam0_el1: Z;
        r_cnthctl_el2: Z;
        r_cntvoff_el2: Z;
        r_cntpoff_el2: Z;
        r_vmpidr_el2: Z;
        r_vttbr_el2: Z;
        r_vtcr_el2: Z;
        r_hcr_el2: Z;
        r_actlr_el2: Z;
        r_afsr0_el2: Z;
        r_afsr1_el2: Z;
        r_amair_el2: Z;
        r_cptr_el2: Z;
        r_elr_el2: Z;
        r_esr_el2: Z;
        r_far_el2: Z;
        r_hacr_el2: Z;
        r_hpfar_el2: Z;
        r_hstr_el2: Z;
        r_mair_el2: Z;
        r_mpam_el2: Z;
        r_mpamhcr_el2: Z;
        r_pmscr_el2: Z;
        r_sctlr_el2: Z;
        r_scxtnum_el2: Z;
        r_sp_el2: Z;
        r_spsr_el2: Z;
        r_tcr_el2: Z;
        r_tfsr_el2: Z;
        r_tpidr_el2: Z;
        r_trfcr_el2: Z;
        r_ttbr0_el2: Z;
        r_ttbr1_el2: Z;
        r_vbar_el2: Z;
        r_vdisr_el2: Z;
        r_vncr_el2: Z;
        r_vpidr_el2: Z;
        r_vsesr_el2: Z;
        r_vstcr_el2: Z;
        r_vsttbr_el2: Z;
        r_zcr_el2: Z;
        r_icc_sre_el2: Z;
        r_icc_hppir1_el1: Z;
        r_spsr_el3: Z;
        r_elr_el3: Z;
        r_esr_el3: Z;
        r_scr_el3: Z;
        r_tpidr_el3: Z
      }.

  Record IDRegState :=
    mkRDRegState {
        ID_AA64PFR0_EL1: Z;
        ID_AA64PFR1_EL1: Z;
        ID_AA64DFR0_EL1: Z;
        ID_AA64DFR1_EL1: Z;
        ID_AA64AFR0_EL1: Z;
        ID_AA64AFR1_EL1: Z;
        ID_AA64ISAR0_EL1: Z;
        ID_AA64ISAR1_EL1: Z;
        ID_AA64MMFR0_EL1: Z;
	      ID_AA64MMFR1_EL1: Z;
	      ID_AA64MMFR2_EL1: Z
      }.

  Record ASMRegState :=
    mkASMRegState {
        a_CN: option bool;
        a_CZ: option bool;
        a_CC: option bool;
        a_CV: option bool;
        a_DAIFCLR: option bool;
        a_SP: Z;
        a_PC: (Z * Z);
        a_EL3: bool
      }.

  Definition zero_regs :=
    mkRegState
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0.

  Definition one_regs :=
    mkRegState
      1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
      1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
      1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1
      1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1.

  Record EmulatedTimerState :=
    mkEmulatedTimerState {
        t_masked: Z;
        t_asserted: Z
      }.

  Definition zero_timer := mkEmulatedTimerState 0 0.

  Record GranuleInfo :=
    mkGranuleInfo {
        (* granule info *)
        g_tag: Z;
        g_refcount: Z;
        g_rd: Z;
        g_map_addr: Z
      }.

  Record RecRvicState :=
    mkRecRvicState {
        r_rvic_enabled: Z;
        r_mask_bits: ZMap.t Z;
        r_pending_bits: ZMap.t Z
      }.

  Definition zero_rvic := mkRecRvicState 0 (ZMap.init 0) (ZMap.init 0).

  Record GranuleDataNormal :=
    mkGranuleDataNormal {
        (* Granule Info *)

        (* NS-Granule *)
        (* Data-Granule *)
        (* Table-Granule *)
        g_data: ZMap.t Z;
        (* realm_params:
              par_base: data[0]
              par_size: data[1]
              rec_list_addr: data[2]
              table_addr: data[3]
              measurement_algo: data[4]
         *)
        (* rec_params:
              gprs: data[0:8]
              pc: data[8]
              flags: data[9]
         *)
        (* rec_run:
              exit_reason: data[0]
              esr: data[1]
              far: data[2]
              hpfar: data[3]
              emulated_write_val: data[4]
              gprs: data[5:12]
              disposed_addr: data[12]
              is_emulated_mmio: data[13]
              emulated_read_val: data[14]
              target_rec: data[15]
         *)

        (* Realm-Granule *)
        g_realm_state: Z;
        g_par_base: Z;
        g_par_end: Z;
        g_rec_list: Z;
        g_rtt: Z;
        g_measurement_algo: Z;
        g_measurement_ctx: Z;
        g_measurement: Z;

        (* RecList-Granule *)
        g_recs: ZMap.t Z;

        (* Rec-Granule *)
        g_rvic: RecRvicState;
        g_runnable: Z
      }.

  Definition zero_granule_data_normal :=
    mkGranuleDataNormal
        (* g_data *) (ZMap.init 0)
        (* g_realm_state *) 0
        (* g_par_base *) 0
        (* g_par_end *) 0
        (* g_rec_list *) 0
        (* g_rtt *) 0
        (* g_measurement_algo *) 0
        (* g_measurement_ctx *) 0
        (* g_measurement *) 0
        (* g_recs *) (ZMap.init 0)
        (* g_rvic *) zero_rvic
        (* g_runnable *) 0.

  Record GranuleDataRec :=
    mkGranuleDataRec {
        (* Rec-Granule *)
        g_regs: RegState;
        g_pc: Z;
        g_pstate: Z;
        g_vtimer: EmulatedTimerState;
        g_ptimer: EmulatedTimerState;
        (* dispose_info *)
        g_dispose_pending: Z;
        g_dispose_addr: Z;
        g_dispose_size: Z;
        (* realm_info *)
        g_rec_rd: Z;
        g_rec_par_base: Z;
        g_rec_par_end: Z;
        g_rec_rec_list: Z;

        (* last_run_info *)
        g_esr: Z;
        g_running: option Z
      }.

  Record RecReadOnly :=
    mkRecReadOnly {
        g_inited: bool;
        g_rec: Z;
        g_rec_idx: Z
      }.

  Definition zero_granule_data_rec :=
    mkGranuleDataRec
        (* g_regs *) zero_regs
        (* g_pc *) 0
        (* g_pstate *) 0
        (* g_vtimer *) zero_timer
        (* g_ptimer *) zero_timer
        (* g_dispose_pending *) 0
        (* g_dispose_addr *) 0
        (* g_dispose_size *) 0
        (* g_rec_rd *) 0
        (* g_rec_par_base *) 0
        (* g_rec_par_end *) 0
        (* g_rec_rec_list *) 0
        (* g_esr *) 0
        (* g_running *) None.

  Definition zero_read_only :=
    mkRecReadOnly
        (* g_inited *) false
        (* g_rec *) 0
        (* g_rec_idx *) 0.

  Record AuxillaryVars :=
    mkAuxillaryVars {
        tbl_level: Z;
        tbl_index: Z;
        tbl_parent: Z
      }.

  Definition zero_aux :=
    mkAuxillaryVars 0 0 0.

  Record Granule :=
    mkGranule {
        glock: option Z;
        gref: option Z;
        gtype: Z;
        gcnt: Z;
        ginfo: GranuleInfo;
        gnorm: GranuleDataNormal;
        grec: GranuleDataRec;
        gro: RecReadOnly;
        gaux: AuxillaryVars
      }.

  Inductive realm_trap_type :=
  | WFX
  | HVC
  | SMC
  | IDREG
  | TIMER
  | ICC
  | DATA_ABORT
  | INSTR_ABORT
  | IRQ
  | FIQ.

  Inductive rmm_task :=
  | NSTRAP
  | REALMTRAP (t: realm_trap_type).

  Inductive MStage :=
  | RMM (task: rmm_task)
  | REALM (rd_gidx: Z) (rec_gidx: Z)
  | NS.

  Record PerCPU :=
    mkPerCPU {
        (* per CPU registers *)
        cpu_regs: RegState;
        asm_regs: ASMRegState;
        id_regs: IDRegState;

        (* per CPU buffer *)
        buffer: ZMap.t (option Z);

        (* per CPU temp variables *)
        ns_regs_el2: RegState;
        realm_params: ZMap.t Z;
        rec_params: ZMap.t Z;
        rec_run: ZMap.t Z;
        retval: Z;
        locked_g: ZMap.t Z;
        wi_last_level: Z;
        wi_llt: Z;
        wi_index: Z;
        rvic_x0: Z;
        rvic_x1: Z;
        rvic_x2: Z;
        rvic_x3: Z;
        rvic_target: Z;
        rvic_ns_notify: Z;
        psci_x0: Z;
        psci_x1: Z;
        psci_x2: Z;
        psci_x3: Z;
        psci_forward_x0: Z;
        psci_forward_x1: Z;
        psci_forward_x2: Z;
        psci_forward_x3: Z;
        psci_forward_psci_call: Z;
        target_rec: Z;
        el2_stack: list Z;
        el3_stack: list Z;
        ns_regs_el3: RegState;
        realm_regs_el3: RegState;
        cur_rec: option Z;
        mstage: MStage;
        trap_reason: Z;
        trap_type: realm_trap_type
      }.

  Record PerRealmSecureData :=
    mkPerRealmSecureData {
        sec_mem: ZMap.t (option Z);
        sec_regs: ZMap.t RegState;
        decl_regs: ZMap.t RegState
      }.

  Record State :=
    mkState {
        gs: ZMap.t Granule; (* from granule idx -> Granule *)
        gpt: ZMap.t bool; (* from granule idx -> secure(T)/non-secure(F) *)
        gpt_lk: ZMap.t (option Z);
        tlbs : Z -> Z -> Z;
        rtts : Z -> Z -> (Z * bool);
        realms: ZMap.t PerRealmSecureData
      }.

  Parameter empty_st: Z -> State. (* initial state *)

End DataType.

Parameter CPU_ID : Z. (* local CPU's CPU ID *)

Section Concurrency.

  Inductive ns_copy_type :=
  | READ_REALM_PARAMS
  | READ_REC_PARAMS
  | READ_REC_RUN
  | WRITE_REC_RUN (run: ZMap.t Z)
  | READ_DATA (gidx: Z).

  Inductive update_ref_type :=
  | GET_REF
  | INC_REF
  | DEC_REF.

  Inductive update_rec_list_type :=
  | GET_RECL
  | SET_RECL (gidx: Z)
  | UNSET_RECL.

  Inductive AtomicEvent :=
    (* acqure lock of gidx with tag *)
  | ACQ (gidx: Z)
    (* release lock *)
  | REL (gidx: Z) (g': Granule)
    (* access Rec's refcount protected *)
  | INIT_RO (gidx: Z) (g_rec: Z) (rec_idx: Z)
    (* update realm or rec's refcount *)
  | GET_GCNT (gidx: Z)
  | INC_GCNT (gidx: Z)
  | DEC_RD_GCNT (gidx: Z)
  | DEC_REC_GCNT (gidx: Z) (g': Granule)
    (* access rec_list *)
  | RECL (gidx: Z) (idx: Z) (t: update_rec_list_type)
    (* update the gpt entry *)
  | ACQ_GPT (gidx: Z)
  | REL_GPT (gidx: Z) (secure: bool)
    (* Higher Layer's RTT ops *)
  | RTT_WALK (root_gidx: Z) (map_addr: Z) (level: Z)
  | RTT_CREATE (root_gidx: Z) (map_addr: Z) (level: Z) (rtt_addr: Z)
  | RTT_DESTROY (root_gidx: Z) (map_addr: Z) (level: Z)
     (* read or write from a NS graunle *)
  | COPY_NS (gidx: Z) (t: ns_copy_type)
  (*
   Hypervisor & Realms' behavior
   *)
    (* memory access from NS world, addr -> physical address *)
  | NS_ACCESS_MEM (addr: Z) (val: Z)
  | REALM_ACCESS_MEM (rd: Z) (rec: Z) (addr: Z) (val: Z)
  | REALM_ACCESS_REG (rd: Z) (rec: Z) (reg: Z) (val: Z)
  | REALM_ACTIVATE (rd_gidx: Z)
  | REALM_TRAP (rd: Z) (rec: Z) (trap_type: realm_trap_type).

  Inductive Event :=
  | EVT (cpuid: Z) (e: AtomicEvent).

  Definition Log := list Event.

  (* input: current log output: other CPUs' events *)
  Definition Oracle := Log -> Log.

  Definition Replay := Log -> State -> option State.

End Concurrency.

Variable realm_trap_determ: Log -> realm_trap_type.

Section AbsData.

  Record RData :=
    mkRData {
        log: list Event; (* global log *)
        oracle: Oracle; (* mover oracle *)
        repl: Replay; (* replay function *)

        share: State; (* Shared states *)
        priv: PerCPU (* CPU local states *)
      }.

  Parameter empty_adt: RData.

End AbsData.

Definition update_r_x0 a b :=
  mkRegState b (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x0 : b }" := (update_r_x0 a b) (at level 1).

Definition update_r_x1 a b :=
  mkRegState (r_x0 a) b (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x1 : b }" := (update_r_x1 a b) (at level 1).

Definition update_r_x2 a b :=
  mkRegState (r_x0 a) (r_x1 a) b (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x2 : b }" := (update_r_x2 a b) (at level 1).

Definition update_r_x3 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) b (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x3 : b }" := (update_r_x3 a b) (at level 1).

Definition update_r_x4 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) b (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x4 : b }" := (update_r_x4 a b) (at level 1).

Definition update_r_x5 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) b (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x5 : b }" := (update_r_x5 a b) (at level 1).

Definition update_r_x6 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) b (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x6 : b }" := (update_r_x6 a b) (at level 1).

Definition update_r_x7 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) b (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x7 : b }" := (update_r_x7 a b) (at level 1).

Definition update_r_x8 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) b (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x8 : b }" := (update_r_x8 a b) (at level 1).

Definition update_r_x9 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) b (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x9 : b }" := (update_r_x9 a b) (at level 1).

Definition update_r_x10 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) b (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x10 : b }" := (update_r_x10 a b) (at level 1).

Definition update_r_x11 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) b (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x11 : b }" := (update_r_x11 a b) (at level 1).

Definition update_r_x12 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) b (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x12 : b }" := (update_r_x12 a b) (at level 1).

Definition update_r_x13 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) b (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x13 : b }" := (update_r_x13 a b) (at level 1).

Definition update_r_x14 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) b (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x14 : b }" := (update_r_x14 a b) (at level 1).

Definition update_r_x15 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) b (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x15 : b }" := (update_r_x15 a b) (at level 1).

Definition update_r_x16 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) b (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x16 : b }" := (update_r_x16 a b) (at level 1).

Definition update_r_x17 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) b (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x17 : b }" := (update_r_x17 a b) (at level 1).

Definition update_r_x18 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) b (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x18 : b }" := (update_r_x18 a b) (at level 1).

Definition update_r_x19 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) b (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x19 : b }" := (update_r_x19 a b) (at level 1).

Definition update_r_x20 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) b (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x20 : b }" := (update_r_x20 a b) (at level 1).

Definition update_r_x21 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) b (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x21 : b }" := (update_r_x21 a b) (at level 1).

Definition update_r_x22 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) b (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x22 : b }" := (update_r_x22 a b) (at level 1).

Definition update_r_x23 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) b (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x23 : b }" := (update_r_x23 a b) (at level 1).

Definition update_r_x24 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) b (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x24 : b }" := (update_r_x24 a b) (at level 1).

Definition update_r_x25 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) b (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x25 : b }" := (update_r_x25 a b) (at level 1).

Definition update_r_x26 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) b (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x26 : b }" := (update_r_x26 a b) (at level 1).

Definition update_r_x27 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) b (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x27 : b }" := (update_r_x27 a b) (at level 1).

Definition update_r_x28 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) b (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x28 : b }" := (update_r_x28 a b) (at level 1).

Definition update_r_x29 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) b (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x29 : b }" := (update_r_x29 a b) (at level 1).

Definition update_r_x30 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) b (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_x30 : b }" := (update_r_x30 a b) (at level 1).

Definition update_r_lr a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) b (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_lr : b }" := (update_r_lr a b) (at level 1).

Definition update_r_cntp_ctl_el0 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) b (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_cntp_ctl_el0 : b }" := (update_r_cntp_ctl_el0 a b) (at level 1).

Definition update_r_cntp_cval_el0 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) b (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_cntp_cval_el0 : b }" := (update_r_cntp_cval_el0 a b) (at level 1).

Definition update_r_cntp_tval_el0 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) b (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_cntp_tval_el0 : b }" := (update_r_cntp_tval_el0 a b) (at level 1).

Definition update_r_cntv_ctl_el0 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) b (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_cntv_ctl_el0 : b }" := (update_r_cntv_ctl_el0 a b) (at level 1).

Definition update_r_cntv_cval_el0 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) b (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_cntv_cval_el0 : b }" := (update_r_cntv_cval_el0 a b) (at level 1).

Definition update_r_cntv_tval_el0 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) b (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_cntv_tval_el0 : b }" := (update_r_cntv_tval_el0 a b) (at level 1).

Definition update_r_sp_el0 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) b (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_sp_el0 : b }" := (update_r_sp_el0 a b) (at level 1).

Definition update_r_pmcr_el0 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) b (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_pmcr_el0 : b }" := (update_r_pmcr_el0 a b) (at level 1).

Definition update_r_pmuserenr_el0 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) b (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_pmuserenr_el0 : b }" := (update_r_pmuserenr_el0 a b) (at level 1).

Definition update_r_tpidrro_el0 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) b (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_tpidrro_el0 : b }" := (update_r_tpidrro_el0 a b) (at level 1).

Definition update_r_tpidr_el0 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) b (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_tpidr_el0 : b }" := (update_r_tpidr_el0 a b) (at level 1).

Definition update_r_sp_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) b (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_sp_el1 : b }" := (update_r_sp_el1 a b) (at level 1).

Definition update_r_elr_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) b (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_elr_el1 : b }" := (update_r_elr_el1 a b) (at level 1).

Definition update_r_spsr_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) b (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_spsr_el1 : b }" := (update_r_spsr_el1 a b) (at level 1).

Definition update_r_csselr_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) b (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_csselr_el1 : b }" := (update_r_csselr_el1 a b) (at level 1).

Definition update_r_sctlr_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) b (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_sctlr_el1 : b }" := (update_r_sctlr_el1 a b) (at level 1).

Definition update_r_actlr_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) b (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_actlr_el1 : b }" := (update_r_actlr_el1 a b) (at level 1).

Definition update_r_cpacr_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) b (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_cpacr_el1 : b }" := (update_r_cpacr_el1 a b) (at level 1).

Definition update_r_zcr_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) b (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_zcr_el1 : b }" := (update_r_zcr_el1 a b) (at level 1).

Definition update_r_ttbr0_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) b (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_ttbr0_el1 : b }" := (update_r_ttbr0_el1 a b) (at level 1).

Definition update_r_ttbr1_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) b (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_ttbr1_el1 : b }" := (update_r_ttbr1_el1 a b) (at level 1).

Definition update_r_tcr_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) b (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_tcr_el1 : b }" := (update_r_tcr_el1 a b) (at level 1).

Definition update_r_esr_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) b (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_esr_el1 : b }" := (update_r_esr_el1 a b) (at level 1).

Definition update_r_afsr0_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) b (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_afsr0_el1 : b }" := (update_r_afsr0_el1 a b) (at level 1).

Definition update_r_afsr1_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) b (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_afsr1_el1 : b }" := (update_r_afsr1_el1 a b) (at level 1).

Definition update_r_far_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) b (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_far_el1 : b }" := (update_r_far_el1 a b) (at level 1).

Definition update_r_mair_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) b (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_mair_el1 : b }" := (update_r_mair_el1 a b) (at level 1).

Definition update_r_vbar_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) b (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_vbar_el1 : b }" := (update_r_vbar_el1 a b) (at level 1).

Definition update_r_contextidr_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) b (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_contextidr_el1 : b }" := (update_r_contextidr_el1 a b) (at level 1).

Definition update_r_tpidr_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) b (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_tpidr_el1 : b }" := (update_r_tpidr_el1 a b) (at level 1).

Definition update_r_amair_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) b (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_amair_el1 : b }" := (update_r_amair_el1 a b) (at level 1).

Definition update_r_cntkctl_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) b (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_cntkctl_el1 : b }" := (update_r_cntkctl_el1 a b) (at level 1).

Definition update_r_par_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) b (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_par_el1 : b }" := (update_r_par_el1 a b) (at level 1).

Definition update_r_mdscr_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) b (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_mdscr_el1 : b }" := (update_r_mdscr_el1 a b) (at level 1).

Definition update_r_mdccint_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) b (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_mdccint_el1 : b }" := (update_r_mdccint_el1 a b) (at level 1).

Definition update_r_disr_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) b (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_disr_el1 : b }" := (update_r_disr_el1 a b) (at level 1).

Definition update_r_mpam0_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) b (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_mpam0_el1 : b }" := (update_r_mpam0_el1 a b) (at level 1).

Definition update_r_cnthctl_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) b (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_cnthctl_el2 : b }" := (update_r_cnthctl_el2 a b) (at level 1).

Definition update_r_cntvoff_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) b (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_cntvoff_el2 : b }" := (update_r_cntvoff_el2 a b) (at level 1).

Definition update_r_cntpoff_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) b (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_cntpoff_el2 : b }" := (update_r_cntpoff_el2 a b) (at level 1).

Definition update_r_vmpidr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) b (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_vmpidr_el2 : b }" := (update_r_vmpidr_el2 a b) (at level 1).

Definition update_r_vttbr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) b (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_vttbr_el2 : b }" := (update_r_vttbr_el2 a b) (at level 1).

Definition update_r_vtcr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) b (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_vtcr_el2 : b }" := (update_r_vtcr_el2 a b) (at level 1).

Definition update_r_hcr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) b (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_hcr_el2 : b }" := (update_r_hcr_el2 a b) (at level 1).

Definition update_r_actlr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) b (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_actlr_el2 : b }" := (update_r_actlr_el2 a b) (at level 1).

Definition update_r_afsr0_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) b (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_afsr0_el2 : b }" := (update_r_afsr0_el2 a b) (at level 1).

Definition update_r_afsr1_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) b (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_afsr1_el2 : b }" := (update_r_afsr1_el2 a b) (at level 1).

Definition update_r_amair_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) b (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_amair_el2 : b }" := (update_r_amair_el2 a b) (at level 1).

Definition update_r_cptr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) b (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_cptr_el2 : b }" := (update_r_cptr_el2 a b) (at level 1).

Definition update_r_elr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) b (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_elr_el2 : b }" := (update_r_elr_el2 a b) (at level 1).

Definition update_r_esr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) b (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_esr_el2 : b }" := (update_r_esr_el2 a b) (at level 1).

Definition update_r_far_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) b (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_far_el2 : b }" := (update_r_far_el2 a b) (at level 1).

Definition update_r_hacr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) b (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_hacr_el2 : b }" := (update_r_hacr_el2 a b) (at level 1).

Definition update_r_hpfar_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) b (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_hpfar_el2 : b }" := (update_r_hpfar_el2 a b) (at level 1).

Definition update_r_hstr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) b (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_hstr_el2 : b }" := (update_r_hstr_el2 a b) (at level 1).

Definition update_r_mair_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) b (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_mair_el2 : b }" := (update_r_mair_el2 a b) (at level 1).

Definition update_r_mpam_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) b (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_mpam_el2 : b }" := (update_r_mpam_el2 a b) (at level 1).

Definition update_r_mpamhcr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) b (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_mpamhcr_el2 : b }" := (update_r_mpamhcr_el2 a b) (at level 1).

Definition update_r_pmscr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) b (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_pmscr_el2 : b }" := (update_r_pmscr_el2 a b) (at level 1).

Definition update_r_sctlr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) b (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_sctlr_el2 : b }" := (update_r_sctlr_el2 a b) (at level 1).

Definition update_r_scxtnum_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) b (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_scxtnum_el2 : b }" := (update_r_scxtnum_el2 a b) (at level 1).

Definition update_r_sp_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) b (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_sp_el2 : b }" := (update_r_sp_el2 a b) (at level 1).

Definition update_r_spsr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) b (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_spsr_el2 : b }" := (update_r_spsr_el2 a b) (at level 1).

Definition update_r_tcr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) b (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_tcr_el2 : b }" := (update_r_tcr_el2 a b) (at level 1).

Definition update_r_tfsr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) b (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_tfsr_el2 : b }" := (update_r_tfsr_el2 a b) (at level 1).

Definition update_r_tpidr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) b (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_tpidr_el2 : b }" := (update_r_tpidr_el2 a b) (at level 1).

Definition update_r_trfcr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) b (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_trfcr_el2 : b }" := (update_r_trfcr_el2 a b) (at level 1).

Definition update_r_ttbr0_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) b (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_ttbr0_el2 : b }" := (update_r_ttbr0_el2 a b) (at level 1).

Definition update_r_ttbr1_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) b (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_ttbr1_el2 : b }" := (update_r_ttbr1_el2 a b) (at level 1).

Definition update_r_vbar_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) b (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_vbar_el2 : b }" := (update_r_vbar_el2 a b) (at level 1).

Definition update_r_vdisr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) b (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_vdisr_el2 : b }" := (update_r_vdisr_el2 a b) (at level 1).

Definition update_r_vncr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) b (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_vncr_el2 : b }" := (update_r_vncr_el2 a b) (at level 1).

Definition update_r_vpidr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) b (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_vpidr_el2 : b }" := (update_r_vpidr_el2 a b) (at level 1).

Definition update_r_vsesr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) b (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_vsesr_el2 : b }" := (update_r_vsesr_el2 a b) (at level 1).

Definition update_r_vstcr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) b (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_vstcr_el2 : b }" := (update_r_vstcr_el2 a b) (at level 1).

Definition update_r_vsttbr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) b (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_vsttbr_el2 : b }" := (update_r_vsttbr_el2 a b) (at level 1).

Definition update_r_zcr_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) b (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_zcr_el2 : b }" := (update_r_zcr_el2 a b) (at level 1).

Definition update_r_icc_sre_el2 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) b (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_icc_sre_el2 : b }" := (update_r_icc_sre_el2 a b) (at level 1).

Definition update_r_icc_hppir1_el1 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) b (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_icc_hppir1_el1 : b }" := (update_r_icc_hppir1_el1 a b) (at level 1).

Definition update_r_spsr_el3 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) b (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_spsr_el3 : b }" := (update_r_spsr_el3 a b) (at level 1).

Definition update_r_elr_el3 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) b (r_esr_el3 a) (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_elr_el3 : b }" := (update_r_elr_el3 a b) (at level 1).

Definition update_r_esr_el3 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) b (r_scr_el3 a) (r_tpidr_el3 a).
Notation "a {r_esr_el3 : b }" := (update_r_esr_el3 a b) (at level 1).

Definition update_r_scr_el3 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) b (r_tpidr_el3 a).
Notation "a {r_scr_el3 : b }" := (update_r_scr_el3 a b) (at level 1).

Definition update_r_tpidr_el3 a b :=
  mkRegState (r_x0 a) (r_x1 a) (r_x2 a) (r_x3 a) (r_x4 a) (r_x5 a) (r_x6 a) (r_x7 a) (r_x8 a) (r_x9 a) (r_x10 a) (r_x11 a) (r_x12 a) (r_x13 a) (r_x14 a) (r_x15 a) (r_x16 a) (r_x17 a) (r_x18 a) (r_x19 a) (r_x20 a) (r_x21 a) (r_x22 a) (r_x23 a) (r_x24 a) (r_x25 a) (r_x26 a) (r_x27 a) (r_x28 a) (r_x29 a) (r_x30 a) (r_lr a) (r_cntp_ctl_el0 a) (r_cntp_cval_el0 a) (r_cntp_tval_el0 a) (r_cntv_ctl_el0 a) (r_cntv_cval_el0 a) (r_cntv_tval_el0 a) (r_sp_el0 a) (r_pmcr_el0 a) (r_pmuserenr_el0 a) (r_tpidrro_el0 a) (r_tpidr_el0 a) (r_sp_el1 a) (r_elr_el1 a) (r_spsr_el1 a) (r_csselr_el1 a) (r_sctlr_el1 a) (r_actlr_el1 a) (r_cpacr_el1 a) (r_zcr_el1 a) (r_ttbr0_el1 a) (r_ttbr1_el1 a) (r_tcr_el1 a) (r_esr_el1 a) (r_afsr0_el1 a) (r_afsr1_el1 a) (r_far_el1 a) (r_mair_el1 a) (r_vbar_el1 a) (r_contextidr_el1 a) (r_tpidr_el1 a) (r_amair_el1 a) (r_cntkctl_el1 a) (r_par_el1 a) (r_mdscr_el1 a) (r_mdccint_el1 a) (r_disr_el1 a) (r_mpam0_el1 a) (r_cnthctl_el2 a) (r_cntvoff_el2 a) (r_cntpoff_el2 a) (r_vmpidr_el2 a) (r_vttbr_el2 a) (r_vtcr_el2 a) (r_hcr_el2 a) (r_actlr_el2 a) (r_afsr0_el2 a) (r_afsr1_el2 a) (r_amair_el2 a) (r_cptr_el2 a) (r_elr_el2 a) (r_esr_el2 a) (r_far_el2 a) (r_hacr_el2 a) (r_hpfar_el2 a) (r_hstr_el2 a) (r_mair_el2 a) (r_mpam_el2 a) (r_mpamhcr_el2 a) (r_pmscr_el2 a) (r_sctlr_el2 a) (r_scxtnum_el2 a) (r_sp_el2 a) (r_spsr_el2 a) (r_tcr_el2 a) (r_tfsr_el2 a) (r_tpidr_el2 a) (r_trfcr_el2 a) (r_ttbr0_el2 a) (r_ttbr1_el2 a) (r_vbar_el2 a) (r_vdisr_el2 a) (r_vncr_el2 a) (r_vpidr_el2 a) (r_vsesr_el2 a) (r_vstcr_el2 a) (r_vsttbr_el2 a) (r_zcr_el2 a) (r_icc_sre_el2 a) (r_icc_hppir1_el1 a) (r_spsr_el3 a) (r_elr_el3 a) (r_esr_el3 a) (r_scr_el3 a) b.
Notation "a {r_tpidr_el3 : b }" := (update_r_tpidr_el3 a b) (at level 1).

Definition update_a_CN a b :=
  mkASMRegState b (a_CZ a) (a_CC a) (a_CV a) (a_DAIFCLR a) (a_SP a) (a_PC a) (a_EL3 a).
Notation "a {a_CN : b }" := (update_a_CN a b) (at level 1).

Definition update_a_CZ a b :=
  mkASMRegState (a_CN a) b (a_CC a) (a_CV a) (a_DAIFCLR a) (a_SP a) (a_PC a) (a_EL3 a).
Notation "a {a_CZ : b }" := (update_a_CZ a b) (at level 1).

Definition update_a_CC a b :=
  mkASMRegState (a_CN a) (a_CZ a) b (a_CV a) (a_DAIFCLR a) (a_SP a) (a_PC a) (a_EL3 a).
Notation "a {a_CC : b }" := (update_a_CC a b) (at level 1).

Definition update_a_CV a b :=
  mkASMRegState (a_CN a) (a_CZ a) (a_CC a) b (a_DAIFCLR a) (a_SP a) (a_PC a) (a_EL3 a).
Notation "a {a_CV : b }" := (update_a_CV a b) (at level 1).

Definition update_a_DAIFCLR a b :=
  mkASMRegState (a_CN a) (a_CZ a) (a_CC a) (a_CV a) b (a_SP a) (a_PC a) (a_EL3 a).
Notation "a {a_DAIFCLR : b }" := (update_a_DAIFCLR a b) (at level 1).

Definition update_a_SP a b :=
  mkASMRegState (a_CN a) (a_CZ a) (a_CC a) (a_CV a) (a_DAIFCLR a) b (a_PC a) (a_EL3 a).
Notation "a {a_SP : b }" := (update_a_SP a b) (at level 1).

Definition update_a_PC a b :=
  mkASMRegState (a_CN a) (a_CZ a) (a_CC a) (a_CV a) (a_DAIFCLR a) (a_SP a) b (a_EL3 a).
Notation "a {a_PC : b }" := (update_a_PC a b) (at level 1).

Definition update_a_EL3 a b :=
  mkASMRegState (a_CN a) (a_CZ a) (a_CC a) (a_CV a) (a_DAIFCLR a) (a_SP a) (a_PC a) b.
Notation "a {a_EL3 : b }" := (update_a_EL3 a b) (at level 1).

Definition update_t_masked a b :=
  mkEmulatedTimerState b (t_asserted a).
Notation "a {t_masked : b }" := (update_t_masked a b) (at level 1).

Definition update_t_asserted a b :=
  mkEmulatedTimerState (t_masked a) b.
Notation "a {t_asserted : b }" := (update_t_asserted a b) (at level 1).

Definition update_g_tag a b :=
  mkGranuleInfo b (g_refcount a) (g_rd a) (g_map_addr a).
Notation "a {g_tag : b }" := (update_g_tag a b) (at level 1).

Definition update_g_refcount a b :=
  mkGranuleInfo (g_tag a) b (g_rd a) (g_map_addr a).
Notation "a {g_refcount : b }" := (update_g_refcount a b) (at level 1).

Definition update_g_rd a b :=
  mkGranuleInfo (g_tag a) (g_refcount a) b (g_map_addr a).
Notation "a {g_rd : b }" := (update_g_rd a b) (at level 1).

Definition update_g_map_addr a b :=
  mkGranuleInfo (g_tag a) (g_refcount a) (g_rd a) b.
Notation "a {g_map_addr : b }" := (update_g_map_addr a b) (at level 1).

Definition update_r_rvic_enabled a b :=
  mkRecRvicState b (r_mask_bits a) (r_pending_bits a).
Notation "a {r_rvic_enabled : b }" := (update_r_rvic_enabled a b) (at level 1).

Definition update_r_mask_bits a b :=
  mkRecRvicState (r_rvic_enabled a) b (r_pending_bits a).
Notation "a {r_mask_bits : b }" := (update_r_mask_bits a b) (at level 1).

Definition update_r_pending_bits a b :=
  mkRecRvicState (r_rvic_enabled a) (r_mask_bits a) b.
Notation "a {r_pending_bits : b }" := (update_r_pending_bits a b) (at level 1).
Definition update_g_data a b :=
  mkGranuleDataNormal b (g_realm_state a) (g_par_base a) (g_par_end a) (g_rec_list a) (g_rtt a) (g_measurement_algo a) (g_measurement_ctx a) (g_measurement a) (g_recs a) (g_rvic a) (g_runnable a).
Notation "a {g_data : b }" := (update_g_data a b) (at level 1).

Definition update_g_realm_state a b :=
  mkGranuleDataNormal (g_data a) b (g_par_base a) (g_par_end a) (g_rec_list a) (g_rtt a) (g_measurement_algo a) (g_measurement_ctx a) (g_measurement a) (g_recs a) (g_rvic a) (g_runnable a).
Notation "a {g_realm_state : b }" := (update_g_realm_state a b) (at level 1).

Definition update_g_par_base a b :=
  mkGranuleDataNormal (g_data a) (g_realm_state a) b (g_par_end a) (g_rec_list a) (g_rtt a) (g_measurement_algo a) (g_measurement_ctx a) (g_measurement a) (g_recs a) (g_rvic a) (g_runnable a).
Notation "a {g_par_base : b }" := (update_g_par_base a b) (at level 1).

Definition update_g_par_end a b :=
  mkGranuleDataNormal (g_data a) (g_realm_state a) (g_par_base a) b (g_rec_list a) (g_rtt a) (g_measurement_algo a) (g_measurement_ctx a) (g_measurement a) (g_recs a) (g_rvic a) (g_runnable a).
Notation "a {g_par_end : b }" := (update_g_par_end a b) (at level 1).

Definition update_g_rec_list a b :=
  mkGranuleDataNormal (g_data a) (g_realm_state a) (g_par_base a) (g_par_end a) b (g_rtt a) (g_measurement_algo a) (g_measurement_ctx a) (g_measurement a) (g_recs a) (g_rvic a) (g_runnable a).
Notation "a {g_rec_list : b }" := (update_g_rec_list a b) (at level 1).

Definition update_g_rtt a b :=
  mkGranuleDataNormal (g_data a) (g_realm_state a) (g_par_base a) (g_par_end a) (g_rec_list a) b (g_measurement_algo a) (g_measurement_ctx a) (g_measurement a) (g_recs a) (g_rvic a) (g_runnable a).
Notation "a {g_rtt : b }" := (update_g_rtt a b) (at level 1).

Definition update_g_measurement_algo a b :=
  mkGranuleDataNormal (g_data a) (g_realm_state a) (g_par_base a) (g_par_end a) (g_rec_list a) (g_rtt a) b (g_measurement_ctx a) (g_measurement a) (g_recs a) (g_rvic a) (g_runnable a).
Notation "a {g_measurement_algo : b }" := (update_g_measurement_algo a b) (at level 1).

Definition update_g_measurement_ctx a b :=
  mkGranuleDataNormal (g_data a) (g_realm_state a) (g_par_base a) (g_par_end a) (g_rec_list a) (g_rtt a) (g_measurement_algo a) b (g_measurement a) (g_recs a) (g_rvic a) (g_runnable a).
Notation "a {g_measurement_ctx : b }" := (update_g_measurement_ctx a b) (at level 1).

Definition update_g_measurement a b :=
  mkGranuleDataNormal (g_data a) (g_realm_state a) (g_par_base a) (g_par_end a) (g_rec_list a) (g_rtt a) (g_measurement_algo a) (g_measurement_ctx a) b (g_recs a) (g_rvic a) (g_runnable a).
Notation "a {g_measurement : b }" := (update_g_measurement a b) (at level 1).

Definition update_g_recs a b :=
  mkGranuleDataNormal (g_data a) (g_realm_state a) (g_par_base a) (g_par_end a) (g_rec_list a) (g_rtt a) (g_measurement_algo a) (g_measurement_ctx a) (g_measurement a) b (g_rvic a) (g_runnable a).
Notation "a {g_recs : b }" := (update_g_recs a b) (at level 1).

Definition update_g_rvic a b :=
  mkGranuleDataNormal (g_data a) (g_realm_state a) (g_par_base a) (g_par_end a) (g_rec_list a) (g_rtt a) (g_measurement_algo a) (g_measurement_ctx a) (g_measurement a) (g_recs a) b (g_runnable a).
Notation "a {g_rvic : b }" := (update_g_rvic a b) (at level 1).

Definition update_g_runnable a b :=
  mkGranuleDataNormal (g_data a) (g_realm_state a) (g_par_base a) (g_par_end a) (g_rec_list a) (g_rtt a) (g_measurement_algo a) (g_measurement_ctx a) (g_measurement a) (g_recs a) (g_rvic a) b.
Notation "a {g_runnable : b }" := (update_g_runnable a b) (at level 1).

Definition update_g_regs a b :=
  mkGranuleDataRec b (g_pc a) (g_pstate a) (g_vtimer a) (g_ptimer a) (g_dispose_pending a) (g_dispose_addr a) (g_dispose_size a) (g_rec_rd a) (g_rec_par_base a) (g_rec_par_end a) (g_rec_rec_list a) (g_esr a) (g_running a).
Notation "a {g_regs : b }" := (update_g_regs a b) (at level 1).

Definition update_g_pc a b :=
  mkGranuleDataRec (g_regs a) b (g_pstate a) (g_vtimer a) (g_ptimer a) (g_dispose_pending a) (g_dispose_addr a) (g_dispose_size a) (g_rec_rd a) (g_rec_par_base a) (g_rec_par_end a) (g_rec_rec_list a) (g_esr a) (g_running a).
Notation "a {g_pc : b }" := (update_g_pc a b) (at level 1).

Definition update_g_pstate a b :=
  mkGranuleDataRec (g_regs a) (g_pc a) b (g_vtimer a) (g_ptimer a) (g_dispose_pending a) (g_dispose_addr a) (g_dispose_size a) (g_rec_rd a) (g_rec_par_base a) (g_rec_par_end a) (g_rec_rec_list a) (g_esr a) (g_running a).
Notation "a {g_pstate : b }" := (update_g_pstate a b) (at level 1).

Definition update_g_vtimer a b :=
  mkGranuleDataRec (g_regs a) (g_pc a) (g_pstate a) b (g_ptimer a) (g_dispose_pending a) (g_dispose_addr a) (g_dispose_size a) (g_rec_rd a) (g_rec_par_base a) (g_rec_par_end a) (g_rec_rec_list a) (g_esr a) (g_running a).
Notation "a {g_vtimer : b }" := (update_g_vtimer a b) (at level 1).

Definition update_g_ptimer a b :=
  mkGranuleDataRec (g_regs a) (g_pc a) (g_pstate a) (g_vtimer a) b (g_dispose_pending a) (g_dispose_addr a) (g_dispose_size a) (g_rec_rd a) (g_rec_par_base a) (g_rec_par_end a) (g_rec_rec_list a) (g_esr a) (g_running a).
Notation "a {g_ptimer : b }" := (update_g_ptimer a b) (at level 1).

Definition update_g_dispose_pending a b :=
  mkGranuleDataRec (g_regs a) (g_pc a) (g_pstate a) (g_vtimer a) (g_ptimer a) b (g_dispose_addr a) (g_dispose_size a) (g_rec_rd a) (g_rec_par_base a) (g_rec_par_end a) (g_rec_rec_list a) (g_esr a) (g_running a).
Notation "a {g_dispose_pending : b }" := (update_g_dispose_pending a b) (at level 1).

Definition update_g_dispose_addr a b :=
  mkGranuleDataRec (g_regs a) (g_pc a) (g_pstate a) (g_vtimer a) (g_ptimer a) (g_dispose_pending a) b (g_dispose_size a) (g_rec_rd a) (g_rec_par_base a) (g_rec_par_end a) (g_rec_rec_list a) (g_esr a) (g_running a).
Notation "a {g_dispose_addr : b }" := (update_g_dispose_addr a b) (at level 1).

Definition update_g_dispose_size a b :=
  mkGranuleDataRec (g_regs a) (g_pc a) (g_pstate a) (g_vtimer a) (g_ptimer a) (g_dispose_pending a) (g_dispose_addr a) b (g_rec_rd a) (g_rec_par_base a) (g_rec_par_end a) (g_rec_rec_list a) (g_esr a) (g_running a).
Notation "a {g_dispose_size : b }" := (update_g_dispose_size a b) (at level 1).

Definition update_g_rec_rd a b :=
  mkGranuleDataRec (g_regs a) (g_pc a) (g_pstate a) (g_vtimer a) (g_ptimer a) (g_dispose_pending a) (g_dispose_addr a) (g_dispose_size a) b (g_rec_par_base a) (g_rec_par_end a) (g_rec_rec_list a) (g_esr a) (g_running a).
Notation "a {g_rec_rd : b }" := (update_g_rec_rd a b) (at level 1).

Definition update_g_rec_par_base a b :=
  mkGranuleDataRec (g_regs a) (g_pc a) (g_pstate a) (g_vtimer a) (g_ptimer a) (g_dispose_pending a) (g_dispose_addr a) (g_dispose_size a) (g_rec_rd a) b (g_rec_par_end a) (g_rec_rec_list a) (g_esr a) (g_running a).
Notation "a {g_rec_par_base : b }" := (update_g_rec_par_base a b) (at level 1).

Definition update_g_rec_par_end a b :=
  mkGranuleDataRec (g_regs a) (g_pc a) (g_pstate a) (g_vtimer a) (g_ptimer a) (g_dispose_pending a) (g_dispose_addr a) (g_dispose_size a) (g_rec_rd a) (g_rec_par_base a) b (g_rec_rec_list a) (g_esr a) (g_running a).
Notation "a {g_rec_par_end : b }" := (update_g_rec_par_end a b) (at level 1).

Definition update_g_rec_rec_list a b :=
  mkGranuleDataRec (g_regs a) (g_pc a) (g_pstate a) (g_vtimer a) (g_ptimer a) (g_dispose_pending a) (g_dispose_addr a) (g_dispose_size a) (g_rec_rd a) (g_rec_par_base a) (g_rec_par_end a) b (g_esr a) (g_running a).
Notation "a {g_rec_rec_list : b }" := (update_g_rec_rec_list a b) (at level 1).

Definition update_g_esr a b :=
  mkGranuleDataRec (g_regs a) (g_pc a) (g_pstate a) (g_vtimer a) (g_ptimer a) (g_dispose_pending a) (g_dispose_addr a) (g_dispose_size a) (g_rec_rd a) (g_rec_par_base a) (g_rec_par_end a) (g_rec_rec_list a) b (g_running a).
Notation "a {g_esr : b }" := (update_g_esr a b) (at level 1).

Definition update_g_running a b :=
  mkGranuleDataRec (g_regs a) (g_pc a) (g_pstate a) (g_vtimer a) (g_ptimer a) (g_dispose_pending a) (g_dispose_addr a) (g_dispose_size a) (g_rec_rd a) (g_rec_par_base a) (g_rec_par_end a) (g_rec_rec_list a) (g_esr a) b.
Notation "a {g_running : b }" := (update_g_running a b) (at level 1).

Definition update_g_inited a b :=
  mkRecReadOnly b (g_rec a) (g_rec_idx a).
Notation "a {g_inited : b }" := (update_g_inited a b) (at level 1).

Definition update_g_rec a b :=
  mkRecReadOnly (g_inited a) b (g_rec_idx a).
Notation "a {g_rec : b }" := (update_g_rec a b) (at level 1).

Definition update_g_rec_idx a b :=
  mkRecReadOnly (g_inited a) (g_rec a) b.
Notation "a {g_rec_idx : b }" := (update_g_rec_idx a b) (at level 1).

Definition update_tbl_level a b :=
  mkAuxillaryVars b (tbl_index a) (tbl_parent a).
Notation "a {tbl_level : b }" := (update_tbl_level a b) (at level 1).

Definition update_tbl_index a b :=
  mkAuxillaryVars (tbl_level a) b (tbl_parent a).
Notation "a {tbl_index : b }" := (update_tbl_index a b) (at level 1).

Definition update_tbl_parent a b :=
  mkAuxillaryVars (tbl_level a) (tbl_index a) b.
Notation "a {tbl_parent : b }" := (update_tbl_parent a b) (at level 1).

Definition update_cpu_regs a b :=
  mkPerCPU b (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {cpu_regs : b }" := (update_cpu_regs a b) (at level 1).

Definition update_asm_regs a b :=
  mkPerCPU (cpu_regs a) b (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {asm_regs : b }" := (update_asm_regs a b) (at level 1).

Definition update_id_regs a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) b (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {id_regs : b }" := (update_id_regs a b) (at level 1).

Definition update_buffer a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) b (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {buffer : b }" := (update_buffer a b) (at level 1).

Definition update_ns_regs_el2 a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) b (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {ns_regs_el2 : b }" := (update_ns_regs_el2 a b) (at level 1).

Definition update_realm_params a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) b (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {realm_params : b }" := (update_realm_params a b) (at level 1).

Definition update_rec_params a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) b (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {rec_params : b }" := (update_rec_params a b) (at level 1).

Definition update_rec_run a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) b (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {rec_run : b }" := (update_rec_run a b) (at level 1).

Definition update_retval a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) b (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {retval : b }" := (update_retval a b) (at level 1).

Definition update_locked_g a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) b (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {locked_g : b }" := (update_locked_g a b) (at level 1).

Definition update_wi_last_level a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) b (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {wi_last_level : b }" := (update_wi_last_level a b) (at level 1).

Definition update_wi_llt a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) b (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {wi_llt : b }" := (update_wi_llt a b) (at level 1).

Definition update_wi_index a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) b (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {wi_index : b }" := (update_wi_index a b) (at level 1).

Definition update_rvic_x0 a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) b (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {rvic_x0 : b }" := (update_rvic_x0 a b) (at level 1).

Definition update_rvic_x1 a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) b (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {rvic_x1 : b }" := (update_rvic_x1 a b) (at level 1).

Definition update_rvic_x2 a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) b (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {rvic_x2 : b }" := (update_rvic_x2 a b) (at level 1).

Definition update_rvic_x3 a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) b (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {rvic_x3 : b }" := (update_rvic_x3 a b) (at level 1).

Definition update_rvic_target a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) b (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {rvic_target : b }" := (update_rvic_target a b) (at level 1).

Definition update_rvic_ns_notify a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) b (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {rvic_ns_notify : b }" := (update_rvic_ns_notify a b) (at level 1).

Definition update_psci_x0 a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) b (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {psci_x0 : b }" := (update_psci_x0 a b) (at level 1).

Definition update_psci_x1 a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) b (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {psci_x1 : b }" := (update_psci_x1 a b) (at level 1).

Definition update_psci_x2 a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) b (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {psci_x2 : b }" := (update_psci_x2 a b) (at level 1).

Definition update_psci_x3 a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) b (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {psci_x3 : b }" := (update_psci_x3 a b) (at level 1).

Definition update_psci_forward_x0 a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) b (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {psci_forward_x0 : b }" := (update_psci_forward_x0 a b) (at level 1).

Definition update_psci_forward_x1 a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) b (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {psci_forward_x1 : b }" := (update_psci_forward_x1 a b) (at level 1).

Definition update_psci_forward_x2 a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) b (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {psci_forward_x2 : b }" := (update_psci_forward_x2 a b) (at level 1).

Definition update_psci_forward_x3 a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) b (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {psci_forward_x3 : b }" := (update_psci_forward_x3 a b) (at level 1).

Definition update_psci_forward_psci_call a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) b (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {psci_forward_psci_call : b }" := (update_psci_forward_psci_call a b) (at level 1).

Definition update_target_rec a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) b (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {target_rec : b }" := (update_target_rec a b) (at level 1).

Definition update_el2_stack a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) b (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {el2_stack : b }" := (update_el2_stack a b) (at level 1).

Definition update_el3_stack a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) b (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {el3_stack : b }" := (update_el3_stack a b) (at level 1).

Definition update_ns_regs_el3 a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) b (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {ns_regs_el3 : b }" := (update_ns_regs_el3 a b) (at level 1).

Definition update_realm_regs_el3 a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) b (cur_rec a) (mstage a) (trap_reason a) (trap_type a).
Notation "a {realm_regs_el3 : b }" := (update_realm_regs_el3 a b) (at level 1).

Definition update_cur_rec a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) b (mstage a) (trap_reason a) (trap_type a).
Notation "a {cur_rec : b }" := (update_cur_rec a b) (at level 1).

Definition update_mstage a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) b (trap_reason a) (trap_type a).
Notation "a {mstage : b }" := (update_mstage a b) (at level 1).

Definition update_trap_reason a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) b (trap_type a).
Notation "a {trap_reason : b }" := (update_trap_reason a b) (at level 1).

Definition update_trap_type a b :=
  mkPerCPU (cpu_regs a) (asm_regs a) (id_regs a) (buffer a) (ns_regs_el2 a) (realm_params a) (rec_params a) (rec_run a) (retval a) (locked_g a) (wi_last_level a) (wi_llt a) (wi_index a) (rvic_x0 a) (rvic_x1 a) (rvic_x2 a) (rvic_x3 a) (rvic_target a) (rvic_ns_notify a) (psci_x0 a) (psci_x1 a) (psci_x2 a) (psci_x3 a) (psci_forward_x0 a) (psci_forward_x1 a) (psci_forward_x2 a) (psci_forward_x3 a) (psci_forward_psci_call a) (target_rec a) (el2_stack a) (el3_stack a) (ns_regs_el3 a) (realm_regs_el3 a) (cur_rec a) (mstage a) (trap_reason a) b.
Notation "a {trap_type : b }" := (update_trap_type a b) (at level 1).

Definition update_glock a b :=
  mkGranule b (gref a) (gtype a) (gcnt a) (ginfo a) (gnorm a) (grec a) (gro a) (gaux a).
Notation "a {glock : b }" := (update_glock a b) (at level 1).

Definition update_gref a b :=
  mkGranule (glock a) b (gtype a) (gcnt a) (ginfo a) (gnorm a) (grec a) (gro a) (gaux a).
Notation "a {gref : b }" := (update_gref a b) (at level 1).

Definition update_gtype a b :=
  mkGranule (glock a) (gref a) b (gcnt a) (ginfo a) (gnorm a) (grec a) (gro a) (gaux a).
Notation "a {gtype : b }" := (update_gtype a b) (at level 1).

Definition update_gcnt a b :=
  mkGranule (glock a) (gref a) (gtype a) b (ginfo a) (gnorm a) (grec a) (gro a) (gaux a).
Notation "a {gcnt : b }" := (update_gcnt a b) (at level 1).

Definition update_ginfo a b :=
  mkGranule (glock a) (gref a) (gtype a) (gcnt a) b (gnorm a) (grec a) (gro a) (gaux a).
Notation "a {ginfo : b }" := (update_ginfo a b) (at level 1).

Definition update_gnorm a b :=
  mkGranule (glock a) (gref a) (gtype a) (gcnt a) (ginfo a) b (grec a) (gro a) (gaux a).
Notation "a {gnorm : b }" := (update_gnorm a b) (at level 1).

Definition update_grec a b :=
  mkGranule (glock a) (gref a) (gtype a) (gcnt a) (ginfo a) (gnorm a) b (gro a) (gaux a).
Notation "a {grec : b }" := (update_grec a b) (at level 1).

Definition update_gro a b :=
  mkGranule (glock a) (gref a) (gtype a) (gcnt a) (ginfo a) (gnorm a) (grec a) b (gaux a).
Notation "a {gro : b }" := (update_gro a b) (at level 1).

Definition update_gaux a b :=
  mkGranule (glock a) (gref a) (gtype a) (gcnt a) (ginfo a) (gnorm a) (grec a) (gro a) b.
Notation "a {gaux : b }" := (update_gaux a b) (at level 1).

Definition update_sec_mem a b :=
  mkPerRealmSecureData b (sec_regs a) (decl_regs a).
Notation "a {sec_mem : b }" := (update_sec_mem a b) (at level 1).

Definition update_sec_regs a b :=
  mkPerRealmSecureData (sec_mem a) b(decl_regs a).
Notation "a {sec_regs : b }" := (update_sec_regs a b) (at level 1).

Definition update_decl_regs a b :=
  mkPerRealmSecureData (sec_mem a) (sec_regs a) b.
Notation "a {decl_regs : b }" := (update_decl_regs a b) (at level 1).

Definition update_gs a b :=
  mkState b (gpt a) (gpt_lk a) (tlbs a) (rtts a) (realms a).
Notation "a {gs : b }" := (update_gs a b) (at level 1).

Definition update_gpt a b :=
  mkState (gs a) b (gpt_lk a) (tlbs a) (rtts a) (realms a).
Notation "a {gpt : b }" := (update_gpt a b) (at level 1).

Definition update_gpt_lk a b :=
  mkState (gs a) (gpt a) b (tlbs a) (rtts a) (realms a).
Notation "a {gpt_lk : b }" := (update_gpt_lk a b) (at level 1).

Definition update_tlbs a b :=
  mkState (gs a) (gpt a) (gpt_lk a) b (rtts a) (realms a).
Notation "a {tlbs : b }" := (update_tlbs a b) (at level 1).

Definition update_rtts a b :=
  mkState (gs a) (gpt a) (gpt_lk a) (tlbs a) b (realms a).
Notation "a {rtts : b }" := (update_rtts a b) (at level 1).

Definition update_realms a b :=
  mkState (gs a) (gpt a) (gpt_lk a) (tlbs a) (rtts a) b.
Notation "a {realms : b }" := (update_realms a b) (at level 1).

Definition update_log a b :=
  mkRData b (oracle a) (repl a) (share a) (priv a).
Notation "a {log : b }" := (update_log a b) (at level 1).

Definition update_oracle a b :=
  mkRData (log a) b (repl a) (share a) (priv a).
Notation "a {oracle : b }" := (update_oracle a b) (at level 1).

Definition update_repl a b :=
  mkRData (log a) (oracle a) b (share a) (priv a).
Notation "a {repl : b }" := (update_repl a b) (at level 1).

Definition update_share a b :=
  mkRData (log a) (oracle a) (repl a) b (priv a).
Notation "a {share : b }" := (update_share a b) (at level 1).

Definition update_priv a b :=
  mkRData (log a) (oracle a) (repl a) (share a) b.
Notation "a {priv : b }" := (update_priv a b) (at level 1).

Definition get_reg (idx: Z) (reg: RegState) :=
  if idx =? x0 then r_x0 reg else
  if idx =? x1 then r_x1 reg else
  if idx =? x2 then r_x2 reg else
  if idx =? x3 then r_x3 reg else
  if idx =? x4 then r_x4 reg else
  if idx =? x5 then r_x5 reg else
  if idx =? x6 then r_x6 reg else
  if idx =? x7 then r_x7 reg else
  if idx =? x8 then r_x8 reg else
  if idx =? x9 then r_x9 reg else
  if idx =? x10 then r_x10 reg else
  if idx =? x11 then r_x11 reg else
  if idx =? x12 then r_x12 reg else
  if idx =? x13 then r_x13 reg else
  if idx =? x14 then r_x14 reg else
  if idx =? x15 then r_x15 reg else
  if idx =? x16 then r_x16 reg else
  if idx =? x17 then r_x17 reg else
  if idx =? x18 then r_x18 reg else
  if idx =? x19 then r_x19 reg else
  if idx =? x20 then r_x20 reg else
  if idx =? x21 then r_x21 reg else
  if idx =? x22 then r_x22 reg else
  if idx =? x23 then r_x23 reg else
  if idx =? x24 then r_x24 reg else
  if idx =? x25 then r_x25 reg else
  if idx =? x26 then r_x26 reg else
  if idx =? x27 then r_x27 reg else
  if idx =? x28 then r_x28 reg else
  if idx =? x29 then r_x29 reg else
  if idx =? x30 then r_x30 reg else
  if idx =? lr then r_lr reg else
  if idx =? cntp_ctl_el0 then r_cntp_ctl_el0 reg else
  if idx =? cntp_cval_el0 then r_cntp_cval_el0 reg else
  if idx =? cntp_tval_el0 then r_cntp_tval_el0 reg else
  if idx =? cntv_ctl_el0 then r_cntv_ctl_el0 reg else
  if idx =? cntv_cval_el0 then r_cntv_cval_el0 reg else
  if idx =? cntv_tval_el0 then r_cntv_tval_el0 reg else
  if idx =? sp_el0 then r_sp_el0 reg else
  if idx =? pmcr_el0 then r_pmcr_el0 reg else
  if idx =? pmuserenr_el0 then r_pmuserenr_el0 reg else
  if idx =? tpidrro_el0 then r_tpidrro_el0 reg else
  if idx =? tpidr_el0 then r_tpidr_el0 reg else
  if idx =? sp_el1 then r_sp_el1 reg else
  if idx =? elr_el1 then r_elr_el1 reg else
  if idx =? spsr_el1 then r_spsr_el1 reg else
  if idx =? csselr_el1 then r_csselr_el1 reg else
  if idx =? sctlr_el1 then r_sctlr_el1 reg else
  if idx =? actlr_el1 then r_actlr_el1 reg else
  if idx =? cpacr_el1 then r_cpacr_el1 reg else
  if idx =? zcr_el1 then r_zcr_el1 reg else
  if idx =? ttbr0_el1 then r_ttbr0_el1 reg else
  if idx =? ttbr1_el1 then r_ttbr1_el1 reg else
  if idx =? tcr_el1 then r_tcr_el1 reg else
  if idx =? esr_el1 then r_esr_el1 reg else
  if idx =? afsr0_el1 then r_afsr0_el1 reg else
  if idx =? afsr1_el1 then r_afsr1_el1 reg else
  if idx =? far_el1 then r_far_el1 reg else
  if idx =? mair_el1 then r_mair_el1 reg else
  if idx =? vbar_el1 then r_vbar_el1 reg else
  if idx =? contextidr_el1 then r_contextidr_el1 reg else
  if idx =? tpidr_el1 then r_tpidr_el1 reg else
  if idx =? amair_el1 then r_amair_el1 reg else
  if idx =? cntkctl_el1 then r_cntkctl_el1 reg else
  if idx =? par_el1 then r_par_el1 reg else
  if idx =? mdscr_el1 then r_mdscr_el1 reg else
  if idx =? mdccint_el1 then r_mdccint_el1 reg else
  if idx =? disr_el1 then r_disr_el1 reg else
  if idx =? mpam0_el1 then r_mpam0_el1 reg else
  if idx =? cnthctl_el2 then r_cnthctl_el2 reg else
  if idx =? cntvoff_el2 then r_cntvoff_el2 reg else
  if idx =? cntpoff_el2 then r_cntpoff_el2 reg else
  if idx =? vmpidr_el2 then r_vmpidr_el2 reg else
  if idx =? vttbr_el2 then r_vttbr_el2 reg else
  if idx =? vtcr_el2 then r_vtcr_el2 reg else
  if idx =? hcr_el2 then r_hcr_el2 reg else
  if idx =? actlr_el2 then r_actlr_el2 reg else
  if idx =? afsr0_el2 then r_afsr0_el2 reg else
  if idx =? afsr1_el2 then r_afsr1_el2 reg else
  if idx =? amair_el2 then r_amair_el2 reg else
  if idx =? cptr_el2 then r_cptr_el2 reg else
  if idx =? elr_el2 then r_elr_el2 reg else
  if idx =? esr_el2 then r_esr_el2 reg else
  if idx =? far_el2 then r_far_el2 reg else
  if idx =? hacr_el2 then r_hacr_el2 reg else
  if idx =? hpfar_el2 then r_hpfar_el2 reg else
  if idx =? hstr_el2 then r_hstr_el2 reg else
  if idx =? mair_el2 then r_mair_el2 reg else
  if idx =? mpam_el2 then r_mpam_el2 reg else
  if idx =? mpamhcr_el2 then r_mpamhcr_el2 reg else
  if idx =? pmscr_el2 then r_pmscr_el2 reg else
  if idx =? sctlr_el2 then r_sctlr_el2 reg else
  if idx =? scxtnum_el2 then r_scxtnum_el2 reg else
  if idx =? sp_el2 then r_sp_el2 reg else
  if idx =? spsr_el2 then r_spsr_el2 reg else
  if idx =? tcr_el2 then r_tcr_el2 reg else
  if idx =? tfsr_el2 then r_tfsr_el2 reg else
  if idx =? tpidr_el2 then r_tpidr_el2 reg else
  if idx =? trfcr_el2 then r_trfcr_el2 reg else
  if idx =? ttbr0_el2 then r_ttbr0_el2 reg else
  if idx =? ttbr1_el2 then r_ttbr1_el2 reg else
  if idx =? vbar_el2 then r_vbar_el2 reg else
  if idx =? vdisr_el2 then r_vdisr_el2 reg else
  if idx =? vncr_el2 then r_vncr_el2 reg else
  if idx =? vpidr_el2 then r_vpidr_el2 reg else
  if idx =? vsesr_el2 then r_vsesr_el2 reg else
  if idx =? vstcr_el2 then r_vstcr_el2 reg else
  if idx =? vsttbr_el2 then r_vsttbr_el2 reg else
  if idx =? zcr_el2 then r_zcr_el2 reg else
  if idx =? icc_sre_el2 then r_icc_sre_el2 reg else
  if idx =? ICC_HPPIR1_EL1 then r_icc_hppir1_el1 reg else
  if idx =? spsr_el3 then r_spsr_el3 reg else
  if idx =? elr_el3 then r_elr_el3 reg else
  if idx =? tpidr_el3 then r_tpidr_el3 reg else
  if idx =? esr_el3 then r_esr_el3 reg else
  if idx =? scr_el3 then r_scr_el3 reg else 0.

Definition set_reg (idx: Z) (val: Z) (reg: RegState) :=
  if idx =? x0 then reg {r_x0: val} else
  if idx =? x1 then reg {r_x1: val} else
  if idx =? x2 then reg {r_x2: val} else
  if idx =? x3 then reg {r_x3: val} else
  if idx =? x4 then reg {r_x4: val} else
  if idx =? x5 then reg {r_x5: val} else
  if idx =? x6 then reg {r_x6: val} else
  if idx =? x7 then reg {r_x7: val} else
  if idx =? x8 then reg {r_x8: val} else
  if idx =? x9 then reg {r_x9: val} else
  if idx =? x10 then reg {r_x10: val} else
  if idx =? x11 then reg {r_x11: val} else
  if idx =? x12 then reg {r_x12: val} else
  if idx =? x13 then reg {r_x13: val} else
  if idx =? x14 then reg {r_x14: val} else
  if idx =? x15 then reg {r_x15: val} else
  if idx =? x16 then reg {r_x16: val} else
  if idx =? x17 then reg {r_x17: val} else
  if idx =? x18 then reg {r_x18: val} else
  if idx =? x19 then reg {r_x19: val} else
  if idx =? x20 then reg {r_x20: val} else
  if idx =? x21 then reg {r_x21: val} else
  if idx =? x22 then reg {r_x22: val} else
  if idx =? x23 then reg {r_x23: val} else
  if idx =? x24 then reg {r_x24: val} else
  if idx =? x25 then reg {r_x25: val} else
  if idx =? x26 then reg {r_x26: val} else
  if idx =? x27 then reg {r_x27: val} else
  if idx =? x28 then reg {r_x28: val} else
  if idx =? x29 then reg {r_x29: val} else
  if idx =? x30 then reg {r_x30: val} else
  if idx =? lr then reg {r_lr: val} else
  if idx =? cntp_ctl_el0 then reg {r_cntp_ctl_el0: val} else
  if idx =? cntp_cval_el0 then reg {r_cntp_cval_el0: val} else
  if idx =? cntp_tval_el0 then reg {r_cntp_tval_el0: val} else
  if idx =? cntv_ctl_el0 then reg {r_cntv_ctl_el0: val} else
  if idx =? cntv_cval_el0 then reg {r_cntv_cval_el0: val} else
  if idx =? cntv_tval_el0 then reg {r_cntv_tval_el0: val} else
  if idx =? sp_el0 then reg {r_sp_el0: val} else
  if idx =? pmcr_el0 then reg {r_pmcr_el0: val} else
  if idx =? pmuserenr_el0 then reg {r_pmuserenr_el0: val} else
  if idx =? tpidrro_el0 then reg {r_tpidrro_el0: val} else
  if idx =? tpidr_el0 then reg {r_tpidr_el0: val} else
  if idx =? sp_el1 then reg {r_sp_el1: val} else
  if idx =? elr_el1 then reg {r_elr_el1: val} else
  if idx =? spsr_el1 then reg {r_spsr_el1: val} else
  if idx =? csselr_el1 then reg {r_csselr_el1: val} else
  if idx =? sctlr_el1 then reg {r_sctlr_el1: val} else
  if idx =? actlr_el1 then reg {r_actlr_el1: val} else
  if idx =? cpacr_el1 then reg {r_cpacr_el1: val} else
  if idx =? zcr_el1 then reg {r_zcr_el1: val} else
  if idx =? ttbr0_el1 then reg {r_ttbr0_el1: val} else
  if idx =? ttbr1_el1 then reg {r_ttbr1_el1: val} else
  if idx =? tcr_el1 then reg {r_tcr_el1: val} else
  if idx =? esr_el1 then reg {r_esr_el1: val} else
  if idx =? afsr0_el1 then reg {r_afsr0_el1: val} else
  if idx =? afsr1_el1 then reg {r_afsr1_el1: val} else
  if idx =? far_el1 then reg {r_far_el1: val} else
  if idx =? mair_el1 then reg {r_mair_el1: val} else
  if idx =? vbar_el1 then reg {r_vbar_el1: val} else
  if idx =? contextidr_el1 then reg {r_contextidr_el1: val} else
  if idx =? tpidr_el1 then reg {r_tpidr_el1: val} else
  if idx =? amair_el1 then reg {r_amair_el1: val} else
  if idx =? cntkctl_el1 then reg {r_cntkctl_el1: val} else
  if idx =? par_el1 then reg {r_par_el1: val} else
  if idx =? mdscr_el1 then reg {r_mdscr_el1: val} else
  if idx =? mdccint_el1 then reg {r_mdccint_el1: val} else
  if idx =? disr_el1 then reg {r_disr_el1: val} else
  if idx =? mpam0_el1 then reg {r_mpam0_el1: val} else
  if idx =? cnthctl_el2 then reg {r_cnthctl_el2: val} else
  if idx =? cntvoff_el2 then reg {r_cntvoff_el2: val} else
  if idx =? cntpoff_el2 then reg {r_cntpoff_el2: val} else
  if idx =? vmpidr_el2 then reg {r_vmpidr_el2: val} else
  if idx =? vttbr_el2 then reg {r_vttbr_el2: val} else
  if idx =? vtcr_el2 then reg {r_vtcr_el2: val} else
  if idx =? hcr_el2 then reg {r_hcr_el2: val} else
  if idx =? actlr_el2 then reg {r_actlr_el2: val} else
  if idx =? afsr0_el2 then reg {r_afsr0_el2: val} else
  if idx =? afsr1_el2 then reg {r_afsr1_el2: val} else
  if idx =? amair_el2 then reg {r_amair_el2: val} else
  if idx =? cptr_el2 then reg {r_cptr_el2: val} else
  if idx =? elr_el2 then reg {r_elr_el2: val} else
  if idx =? esr_el2 then reg {r_esr_el2: val} else
  if idx =? far_el2 then reg {r_far_el2: val} else
  if idx =? hacr_el2 then reg {r_hacr_el2: val} else
  if idx =? hpfar_el2 then reg {r_hpfar_el2: val} else
  if idx =? hstr_el2 then reg {r_hstr_el2: val} else
  if idx =? mair_el2 then reg {r_mair_el2: val} else
  if idx =? mpam_el2 then reg {r_mpam_el2: val} else
  if idx =? mpamhcr_el2 then reg {r_mpamhcr_el2: val} else
  if idx =? pmscr_el2 then reg {r_pmscr_el2: val} else
  if idx =? sctlr_el2 then reg {r_sctlr_el2: val} else
  if idx =? scxtnum_el2 then reg {r_scxtnum_el2: val} else
  if idx =? sp_el2 then reg {r_sp_el2: val} else
  if idx =? spsr_el2 then reg {r_spsr_el2: val} else
  if idx =? tcr_el2 then reg {r_tcr_el2: val} else
  if idx =? tfsr_el2 then reg {r_tfsr_el2: val} else
  if idx =? tpidr_el2 then reg {r_tpidr_el2: val} else
  if idx =? trfcr_el2 then reg {r_trfcr_el2: val} else
  if idx =? ttbr0_el2 then reg {r_ttbr0_el2: val} else
  if idx =? ttbr1_el2 then reg {r_ttbr1_el2: val} else
  if idx =? vbar_el2 then reg {r_vbar_el2: val} else
  if idx =? vdisr_el2 then reg {r_vdisr_el2: val} else
  if idx =? vncr_el2 then reg {r_vncr_el2: val} else
  if idx =? vpidr_el2 then reg {r_vpidr_el2: val} else
  if idx =? vsesr_el2 then reg {r_vsesr_el2: val} else
  if idx =? vstcr_el2 then reg {r_vstcr_el2: val} else
  if idx =? vsttbr_el2 then reg {r_vsttbr_el2: val} else
  if idx =? zcr_el2 then reg {r_zcr_el2: val} else
  if idx =? icc_sre_el2 then reg {r_icc_sre_el2: val} else
  if idx =? ICC_HPPIR1_EL1 then reg {r_icc_hppir1_el1: val} else
  if idx =? spsr_el3 then reg {r_spsr_el3: val} else
  if idx =? elr_el3 then reg {r_elr_el3: val} else
  if idx =? tpidr_el3 then reg {r_tpidr_el3: val} else
  if idx =? esr_el3 then reg {r_esr_el3: val} else
  if idx =? scr_el3 then reg {r_scr_el3: val} else reg.

Definition regs_is_int64_dec regset:
  {forall n, is_int64 (get_reg n regset) = true} + {~ forall n, is_int64 (get_reg n regset) = true}.
Proof.
  apply prop_dec.
Qed.

Definition query_oracle adt :=
  let lo := oracle adt (log adt) in
  when st == repl adt lo (share adt);
  Some (adt {log: lo ++ (log adt)} {share: st}).

Hint Unfold
  null_loc
  error_loc
  ginfo_loc
  buffer_loc
  pg_loc
  vtimer_loc
  ptimer_loc
  rvic_loc
  bitmap_loc
  rvic_pending_loc
  rvic_mask_loc
  spinlock_loc
  NULL.
