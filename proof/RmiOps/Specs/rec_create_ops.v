Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiAux2.Spec.

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

  Definition rec_create_ops_spec (g_rd': Pointer) (g_rec: Pointer) (rd: Pointer) (rec_list: Pointer) (rec: Pointer) (mpidr: Z64) (rec_idx: Z64) (adt: RData) : option RData :=
    match mpidr, rec_idx with
    | VZ64 mpidr, VZ64 rec_idx =>
      rely is_int64 mpidr; rely is_int64 rec_idx;
      rely (peq (base g_rd') ginfo_loc);
      rely (peq (base g_rec) ginfo_loc);
      rely (peq (base rd) buffer_loc);
      rely (peq (base rec_list) buffer_loc);
      rely (peq (base rec) buffer_loc);
      when rd_gidx == ((buffer (priv adt)) @ (offset rd));
      when rec_list_gidx == ((buffer (priv adt)) @ (offset rec_list));
      when rec_gidx == ((buffer (priv adt)) @ (offset rec));
      rely is_gidx rd_gidx; rely is_gidx rec_list_gidx; rely is_gidx rec_gidx;
      rely prop_dec (offset g_rd' = rd_gidx);
      rely prop_dec (offset g_rec = rec_gidx);
      let gn_rec := (gs (share adt)) @ rec_gidx in
      let gn_rec_list := (gs (share adt)) @ rec_list_gidx in
      let gn_rd := (gs (share adt)) @ rd_gidx in
      rely prop_dec (glock gn_rd = Some CPU_ID);
      rely prop_dec (glock gn_rec = Some CPU_ID);
      rely prop_dec (g_rec_list (gnorm gn_rd) = rec_list_gidx);
      rely (g_tag (ginfo gn_rd) =? GRANULE_STATE_RD);
      rely (g_tag (ginfo gn_rec_list) =? GRANULE_STATE_REC_LIST);
      rely (gtype gn_rec_list =? GRANULE_STATE_REC_LIST);
      rely (g_tag (ginfo gn_rec) =? GRANULE_STATE_DELEGATED);
      rely (gtype gn_rec =? GRANULE_STATE_DELEGATED);
      rely (negb (g_inited (gro gn_rec)));
      let rtt_gidx := g_rtt (gnorm gn_rd) in
      rely is_gidx rtt_gidx;
      let rtt_addr := __gidx_to_addr rtt_gidx in
      rely is_int64 rtt_addr;
      let rtt := Z.land rtt_addr 281474976710654 in
      rely is_int64 (g_par_base (gnorm gn_rd)); rely is_int64 (g_par_end (gnorm gn_rd));
      let param := rec_params (priv adt) in
      rely (prop_dec (forall i, is_int64 (param @ i) = true));
      let run := param @ 9 in
      let gn_rd' := gn_rd {gcnt: (gcnt gn_rd) + 1} in
      let gn_rec_list' := gn_rec_list {gnorm: (gnorm gn_rec_list) {g_data: (g_data (gnorm (gn_rec_list))) # rec_idx == rec_gidx}} in
      let gn_rec' := gn_rec {ginfo: (ginfo gn_rec) {g_tag: GRANULE_STATE_REC} {g_rd: rd_gidx}}
                            {grec: init_grec (grec gn_rec) param mpidr rtt  (g_par_base (gnorm gn_rd)) (g_par_end (gnorm gn_rd)) rd_gidx rec_list_gidx}
                            {gnorm: (gnorm gn_rec) {g_rvic: (g_rvic (gnorm gn_rec)) {r_mask_bits: init_mask_bits (r_mask_bits (g_rvic (gnorm gn_rec)))}}}
                            {gro: mkRecReadOnly true rec_gidx rec_idx} in
      let gn_rec' := gn_rec' {gnorm: (gnorm gn_rec')
                                       {g_measurement_ctx:
                                          if (g_measurement_algo (gnorm gn_rec')) =? MEASUREMENT_ALGO_SHA256 then
                                            measure_rec (g_measurement_ctx (gnorm gn_rec')) (grec gn_rec')
                                          else
                                            g_measurement_ctx (gnorm gn_rec')}
                                       {g_runnable: Z.land run 1}} in

      let e := EVT CPU_ID (RECL rec_list_gidx rec_idx (SET_RECL rec_gidx)) in
      let e1 := EVT CPU_ID (INIT_RO rec_gidx rec_gidx rec_idx) in
      let e2 := EVT CPU_ID (INC_GCNT rd_gidx) in
      Some adt {log: e2 :: e1 :: e :: log adt}
           {share: (share adt) {gs: (gs (share adt)) # rec_gidx == gn_rec' # rd_gidx == gn_rd' # rec_list_gidx == gn_rec_list'}}
  end.

End Spec.

