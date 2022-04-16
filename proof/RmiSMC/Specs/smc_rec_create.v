Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiOps.Spec.

Local Open Scope Z_scope.

Section Spec.

Definition init_grec r param mpidr rtt par_base par_end rd_gidx rec_list_gidx :=
  r {g_regs: (g_regs r) {r_x0: (param @ 0)} {r_x1: (param @ 1)} {r_x2: (param @ 2)}
                        {r_x3: (param @ 3)} {r_x4: (param @ 4)} {r_x5: (param @ 5)}
                        {r_x6: (param @ 6)} {r_x7: (param @ 7)}
                        {r_pmcr_el0: PMCR_EL0_RES1} {r_sctlr_el1: SCTLR_EL1_FLAGS} {r_mdscr_el1: MDSCR_EL1_TDCC_BIT}
                        {r_vmpidr_el2: mpidr} {r_cnthctl_el2 : CNTHCTL_EL2_NO_TRAPS}
                        {r_hcr_el2 : HCR_FLAGS} {r_vtcr_el2 : VTCR_FLAGS} {r_vttbr_el2 : rtt}}
    {g_pc: (param @ 8)} {g_pstate: PSTATE_INIT}
    {g_rec_par_base: par_base} {g_rec_par_end: par_end} {g_rec_rd: rd_gidx}
    {g_rec_rec_list: rec_list_gidx}.

Definition init_mask_bits m :=
  m # 0 == U64MAX # 1 == U64MAX # 2 == U64MAX # 3 == U64MAX # 4 == U64MAX # 5 == U64MAX # 6 == U64MAX # 7 == U64MAX.

Definition measure_rec c rec :=
  measure_extend_rec_sysregs
    (measure_extend_rec_pstate
        (measure_extend_rec_regs
          (measure_extend_rec_header c)
          (g_regs rec))
        (g_pstate rec))
    (g_regs rec).

Definition smc_rec_create_spec (rec_addr: Z64) (rd_addr: Z64) (mpidr: Z64) (rec_params_addr: Z64) (adt: RData) : option (RData * Z64) :=
  match rec_addr, rd_addr, mpidr, rec_params_addr with
  | VZ64 rec_addr, VZ64 rd_addr, VZ64 mpidr, VZ64 rec_params_addr =>
    rely is_int64 rec_addr; rely is_int64 rd_addr; rely is_int64 mpidr; rely is_int64 rec_params_addr;
    rely prop_dec (cur_rec (priv adt) = None);
    let param_gidx := __addr_to_gidx rec_params_addr in
    let rec_gidx := __addr_to_gidx rec_addr in
    let rd_gidx := __addr_to_gidx rd_addr in
    if (GRANULE_ALIGNED rec_params_addr) && (is_gidx param_gidx) &&
       (GRANULE_ALIGNED rec_addr) && (is_gidx rec_gidx)
    then
      when adt == query_oracle adt;
      let gn_rec := (gs (share adt)) @ rec_gidx in
      rely prop_dec (glock gn_rec = None);
      let e := EVT CPU_ID (ACQ rec_gidx) in
      let e' := EVT CPU_ID (REL rec_gidx (gn_rec {glock: Some CPU_ID})) in
      if g_tag (ginfo gn_rec) =? GRANULE_STATE_DELEGATED then
        rely (gtype gn_rec =? GRANULE_STATE_DELEGATED);
        if (GRANULE_ALIGNED rd_addr) && (is_gidx rd_gidx) then
          let gn_rd := (gs (share adt)) @ rd_gidx in
          rely prop_dec (glock gn_rd = None);
          let e1 := EVT CPU_ID (ACQ rd_gidx) in
          let e1' := EVT CPU_ID (REL rd_gidx (gn_rd {glock: Some CPU_ID})) in
          if g_tag (ginfo gn_rd) =? GRANULE_STATE_RD then
            rely (gtype gn_rd =? GRANULE_STATE_RD);
            rely prop_dec ((buffer (priv adt)) @ SLOT_NS = None);
            let e2 := EVT CPU_ID (COPY_NS param_gidx READ_REC_PARAMS) in
            let gn_param := (gs (share adt)) @ param_gidx in
            if g_tag (ginfo gn_param) =? GRANULE_STATE_NS then
              rely (gtype gn_param =? GRANULE_STATE_NS);
              let param := g_data (gnorm gn_param) in
              let adt := adt {log: e2 :: e1 :: e :: log adt} {priv: (priv adt) {rec_params: param}} in
              rely prop_dec ((buffer (priv adt)) @ SLOT_RD = None);
              rely prop_dec ((buffer (priv adt)) @ SLOT_REC = None);
              rely prop_dec ((buffer (priv adt)) @ SLOT_REC_LIST = None);
              let recl_gidx := g_rec_list (gnorm gn_rd) in
              let gn_recl := (gs (share adt)) @ recl_gidx in
              let rec_idx := __mpidr_to_rec_idx mpidr in
              rely (g_tag (ginfo gn_recl) =? GRANULE_STATE_REC_LIST);
              rely (gtype gn_recl =? GRANULE_STATE_REC_LIST);
              if (g_realm_state (gnorm gn_rd) =? REALM_STATE_NEW) &&
                 __mpidr_is_valid mpidr &&
                 (((g_data (gnorm gn_recl)) @ rec_idx) =? 0)
              then
                let rtt_gidx := g_rtt (gnorm gn_rd) in
                rely is_gidx rtt_gidx;
                let rtt_addr := __gidx_to_addr rtt_gidx in
                rely is_int64 rtt_addr;
                let rtt := Z.land rtt_addr 281474976710654 in
                rely is_int64 (g_par_base (gnorm gn_rd)); rely is_int64 (g_par_end (gnorm gn_rd));
                rely (prop_dec (forall i, is_int64 (param @ i) = true));
                let run := param @ 9 in
                let gn_rd' := gn_rd {gcnt: (gcnt gn_rd) + 1} in
                let gn_rec_list' := gn_recl {gnorm: (gnorm gn_recl) {g_data: (g_data (gnorm gn_recl)) # rec_idx == rec_gidx}} in
                let gn_rec' := gn_rec {ginfo: (ginfo gn_rec) {g_tag: GRANULE_STATE_REC} {g_rd: rd_gidx}}
                                      {grec: init_grec (grec gn_rec) param mpidr rtt  (g_par_base (gnorm gn_rd)) (g_par_end (gnorm gn_rd)) rd_gidx recl_gidx}
                                      {gnorm: (gnorm gn_rec) {g_rvic: (g_rvic (gnorm gn_rec)) {r_mask_bits: init_mask_bits (r_mask_bits (g_rvic (gnorm gn_rec)))}}}
                                      {gro: mkRecReadOnly true rec_gidx rec_idx} in
                rely (g_measurement_algo (gnorm gn_rec') =? 0);
                let gn_rec' := gn_rec' {gnorm: (gnorm gn_rec') {g_measurement_ctx: g_measurement_ctx (gnorm gn_rec')}
                                                               {g_runnable: Z.land run 1}} in
                let e3 := EVT CPU_ID (RECL recl_gidx rec_idx (SET_RECL rec_gidx)) in
                let e4 := EVT CPU_ID (INIT_RO rec_gidx rec_gidx rec_idx) in
                let e5 := EVT CPU_ID (INC_GCNT rd_gidx) in
                let e1' := EVT CPU_ID (REL rd_gidx (gn_rd' {glock: Some CPU_ID})) in
                let e' := EVT CPU_ID (REL rd_gidx (gn_rec' {glock: Some CPU_ID})) in
                Some (adt {log: e' :: e1' :: e5 :: e3 :: e2 :: log adt}
                          {share: (share adt) {gs: (gs (share adt)) # rec_gidx == (gn_rec' {gtype: GRANULE_STATE_REC})
                                                                                    # rd_gidx == gn_rd' # recl_gidx == gn_rec_list'}},
                      VZ64 0)
              else Some (adt {log: e' :: e1' :: log adt}, VZ64 1)
            else Some (adt {log: e' :: e1' :: e2 :: e1 :: e :: log adt}, VZ64 1)
          else Some (adt {log: e' :: e1' :: e1 :: e :: log adt}, VZ64 1)
        else Some (adt {log: e' :: e :: log adt}, VZ64 1)
      else Some (adt {log: e' :: e :: log adt}, VZ64 1)
    else Some (adt, VZ64 1)
  end.

End Spec.

