Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RmiAux.Spec.
Require Import AbsAccessor.Spec.
Require Import RmiOps.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition valid_realm_params base size :=
      (GRANULE_ALIGNED base) && (GRANULE_ALIGNED size) && (base + size >? base) && (base + size <? IPA_SIZE).

  Definition smc_realm_create_spec (rd_addr: Z64) (realm_params_addr: Z64) (adt: RData) : option (RData * Z64) :=
    match rd_addr, realm_params_addr with
    | VZ64 rd_addr, VZ64 realm_params_addr =>
      rely is_int64 rd_addr; rely is_int64 realm_params_addr;
      rely prop_dec (cur_rec (priv adt) = None);
      (* get_realm_params *)
      let param_gidx := __addr_to_gidx realm_params_addr in
      if (GRANULE_ALIGNED realm_params_addr) && (is_gidx param_gidx) then
        rely prop_dec ((buffer (priv adt)) @ SLOT_NS = None);
        let e := EVT CPU_ID (COPY_NS param_gidx READ_REALM_PARAMS) in
        let gn := (gs (share adt)) @ param_gidx in
        if (g_tag (ginfo gn) =? GRANULE_STATE_NS) then
          rely prop_dec (gtype gn = GRANULE_STATE_NS);
          let ns_data := g_data (gnorm gn) in
          let adt := adt {log: e :: log adt} {priv: (priv adt) {realm_params: ns_data}} in
          (* validate_realm_params *)
          let base := ns_data @ 0 in
          let size := ns_data @ 1 in
          let recl_addr := ns_data @ 2 in
          let rtt_addr := ns_data @ 3 in
          let algo := ns_data @ 4 in
          rely is_int64 base; rely is_int64 size; rely is_int64 (base + size);
          rely is_int64 recl_addr; rely is_int64 rtt_addr; rely is_int64 algo;
          if valid_realm_params base size then
            (* find_lock_three_delegated_granules *)
            if (negb (rd_addr =? rtt_addr)) && (negb (rd_addr =? recl_addr)) && (negb (rtt_addr =? recl_addr)) &&
              (GRANULE_ALIGNED rd_addr) && (GRANULE_ALIGNED rtt_addr) && (GRANULE_ALIGNED recl_addr)
            then
              let rd_gidx := __addr_to_gidx rd_addr in
              let rtt_gidx := __addr_to_gidx rtt_addr in
              let recl_gidx := __addr_to_gidx recl_addr in
              rely is_gidx rd_gidx; rely is_gidx rtt_gidx; rely is_gidx recl_gidx;
              rely prop_dec (rd_gidx <> rtt_gidx);
              rely prop_dec (rd_gidx <> recl_gidx);
              rely prop_dec (rtt_gidx <> recl_gidx);
              when adt == query_oracle adt;
              let st := share adt in
              let gn_rd := (gs st) @ rd_gidx in
              let gn_rtt := (gs st) @ rtt_gidx in
              let gn_recl := (gs st) @ recl_gidx in
              rely prop_dec (glock gn_rd = None);
              rely prop_dec (glock gn_rtt = None);
              rely prop_dec (glock gn_recl = None);
              let e1 := EVT CPU_ID (ACQ rd_gidx) in
              let e2 := EVT CPU_ID (ACQ rtt_gidx) in
              let e3 := EVT CPU_ID (ACQ recl_gidx) in
              if (g_tag (ginfo gn_rd) =? GRANULE_STATE_DELEGATED) &&
                (g_tag (ginfo gn_rtt) =? GRANULE_STATE_DELEGATED) &&
                (g_tag (ginfo gn_recl) =? GRANULE_STATE_DELEGATED)
              then
                rely (gtype gn_rd =? GRANULE_STATE_DELEGATED);
                rely (gtype gn_rtt =? GRANULE_STATE_DELEGATED);
                rely (gtype gn_recl =? GRANULE_STATE_DELEGATED);
                let adt := adt {log: e3 :: e2 :: e1 :: (log adt)}
                              {priv: (priv adt) {locked_g: (locked_g (priv adt)) # 0 == rd_gidx # 1 == rtt_gidx # 2 == recl_gidx}}
                in
                (* realm_create_ops *)
                let grtt' := gn_rtt {ginfo: (ginfo gn_rtt) {g_tag: GRANULE_STATE_TABLE} {g_rd: rd_gidx}} in
                let e1 := EVT CPU_ID (REL rtt_gidx (grtt' {glock: Some CPU_ID})) in
                let grecl' := gn_recl {ginfo: (ginfo gn_recl) {g_tag: GRANULE_STATE_REC_LIST}} in
                let e2 := EVT CPU_ID (REL recl_gidx (grecl' {glock: Some CPU_ID})) in
                rely prop_dec ((buffer (priv adt)) @ SLOT_RD = None);
                let grd' := gn_rd {gnorm: (gnorm gn_rd) {g_realm_state: REALM_STATE_NEW} {g_par_base: base}
                                                        {g_par_end: base + size} {g_rtt: rtt_gidx} {g_rec_list: recl_gidx}
                                                        {g_measurement_algo: if algo =? MEASUREMENT_ALGO_SHA256 then
                                                                              MEASUREMENT_ALGO_SHA256 else MEASUREMENT_ALGO_ZERO}
                                                        {g_measurement_ctx: if algo =? MEASUREMENT_ALGO_SHA256 then measure_start
                                                                            else (g_measurement_ctx (gnorm gn_rd))}}
                                  {ginfo: (ginfo gn_rd) {g_tag: GRANULE_STATE_RD}} in
                let e3 := EVT CPU_ID (REL rd_gidx (grd' {glock: Some CPU_ID})) in
                Some (adt {log: e3 :: e2 :: e1 :: (log adt)}
                          {share: (share adt) {gs: (gs (share adt)) # rd_gidx == (grd' {gtype: GRANULE_STATE_RD})
                                                                    # recl_gidx == (grecl' {gtype: GRANULE_STATE_REC_LIST})
                                                                    # rtt_gidx == (grtt' {gtype: GRANULE_STATE_TABLE})}},
                      VZ64 0)
              else
                let e1' := EVT CPU_ID (REL rd_gidx (gn_rd {glock: Some CPU_ID})) in
                let e2' := EVT CPU_ID (REL rtt_gidx (gn_rtt {glock: Some CPU_ID})) in
                let e3' := EVT CPU_ID (REL recl_gidx (gn_recl {glock: Some CPU_ID})) in
                Some (adt {log: e1' :: e2' :: e3' :: e3 :: e2 :: e1 :: log adt}, VZ64 1)
            else
              Some (adt, VZ64 1)
          else
            Some (adt, VZ64 1)
        else
          Some (adt {log: e :: log adt}, VZ64 1)
      else
        Some (adt, VZ64 1)
    end.

End Spec.
