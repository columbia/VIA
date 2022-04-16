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

  Definition smc_realm_destroy_spec (rd_addr: Z64) (adt: RData) : option (RData * Z64) :=
    match rd_addr with
    | VZ64 addr =>
      rely is_int64 addr;
      rely prop_dec (cur_rec (priv adt) = None);
      let gidx := __addr_to_gidx addr in
      if (GRANULE_ALIGNED addr) && (is_gidx gidx) then
        when adt == query_oracle adt;
        let gn := (gs (share adt)) @ gidx in
        rely prop_dec (glock gn = None);
        let e0 := EVT CPU_ID (ACQ gidx) in
        if (g_tag (ginfo gn) =? GRANULE_STATE_RD) && (gcnt gn =? 0) then
          rely prop_dec (gtype gn = GRANULE_STATE_RD);
          rely prop_dec ((buffer (priv adt)) @ SLOT_RD = None);
          rely prop_dec ((buffer (priv adt)) @ SLOT_TABLE = None);
          rely prop_dec ((buffer (priv adt)) @ SLOT_REC_LIST = None);
          let rtt_gidx := g_rtt (gnorm gn) in
          let recl_gidx := g_rec_list (gnorm gn) in
          rely is_gidx rtt_gidx; rely is_gidx recl_gidx;
          let gn := (gs (share adt)) @ gidx in
          let gn_rtt := (gs (share adt)) @ rtt_gidx in
          let gn_recl := (gs (share adt)) @ recl_gidx in
          rely prop_dec (glock gn_rtt = None);
          rely prop_dec (glock gn_recl = None);
          rely (g_tag (ginfo gn) =? GRANULE_STATE_RD);
          rely (g_tag (ginfo gn_rtt) =? GRANULE_STATE_TABLE);
          rely (g_tag (ginfo gn_recl) =? GRANULE_STATE_REC_LIST);
          rely (gtype gn =? GRANULE_STATE_RD);
          rely (gtype gn_rtt =? GRANULE_STATE_TABLE);
          rely (gtype gn_recl =? GRANULE_STATE_REC_LIST);
          rely is_int64 (g_refcount (ginfo gn_rtt));
          let e := EVT CPU_ID (ACQ rtt_gidx) in
          if g_refcount (ginfo gn_rtt) =? 0 then
            let grd' := gn {gnorm: zero_granule_data_normal} {grec: zero_granule_data_rec}
                          {ginfo: (ginfo gn) {g_tag: GRANULE_STATE_DELEGATED}} in
            let grecl' := gn_recl {ginfo: (ginfo gn_recl) {g_tag: GRANULE_STATE_DELEGATED}}
                                  {gnorm: zero_granule_data_normal} {grec: zero_granule_data_rec} in
            let grtt' := gn_rtt {ginfo: (ginfo gn_rtt) {g_rd: 0} {g_tag: GRANULE_STATE_DELEGATED}}
                                {gnorm: zero_granule_data_normal} {grec: zero_granule_data_rec} in
            let e1 := EVT CPU_ID (ACQ recl_gidx) in
            let e' := EVT CPU_ID (REL rtt_gidx (grtt' {glock: Some CPU_ID})) in
            let e'' := EVT CPU_ID (REL recl_gidx (grecl' {glock: Some CPU_ID})) in
            let e''' := EVT CPU_ID (REL gidx (grd' {glock: Some CPU_ID})) in
            Some (adt {log: e''' :: e'' :: e' :: e1 :: e :: e0 :: (log adt)}
                      {share: (share adt) {gs: (gs (share adt)) # rtt_gidx == (grtt' {gtype: GRANULE_STATE_DELEGATED})
                                                                # recl_gidx == (grecl' {gtype: GRANULE_STATE_DELEGATED})
                                                                # gidx == (grd' {gtype: GRANULE_STATE_DELEGATED})}},
                  VZ64 0)
          else
            let e' := EVT CPU_ID (REL rtt_gidx (gn_rtt {glock: Some CPU_ID})) in
            let e'' := EVT CPU_ID (REL gidx (gn {glock: Some CPU_ID})) in
            Some (adt {log: e'' :: e' :: e :: e0 :: log adt}, VZ64 1)
        else
          let e' := EVT CPU_ID (REL gidx (gn {glock: Some CPU_ID})) in
          Some (adt {log: e' :: e0 :: (log adt)}, VZ64 1)
      else Some (adt, VZ64 1)
    end.

End Spec.
