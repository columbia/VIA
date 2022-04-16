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

  Definition smc_rec_destroy_spec (rec_addr: Z64) (adt: RData) : option (RData * Z64) :=
    match rec_addr with
    | VZ64 addr =>
      rely is_int64 addr;
      rely prop_dec (cur_rec (priv adt) = None);
      let rec_gidx := __addr_to_gidx addr in
      if (GRANULE_ALIGNED addr) && (is_gidx rec_gidx) then
        when adt == query_oracle adt;
        let gn_rec := (gs (share adt)) @ rec_gidx in
        rely prop_dec (glock gn_rec = None);
        let e := EVT CPU_ID (ACQ rec_gidx) in
        let e' := EVT CPU_ID (REL rec_gidx (gn_rec {glock: Some CPU_ID})) in
        if (g_tag (ginfo gn_rec) =? GRANULE_STATE_REC) && (gcnt gn_rec =? 0) then
          rely prop_dec (gtype gn_rec = GRANULE_STATE_REC);
          rely prop_dec (gref gn_rec = None);
          rely prop_dec ((buffer (priv adt)) @ SLOT_REC_LIST = None);
          rely prop_dec ((buffer (priv adt)) @ SLOT_REC = None);
          rely (g_inited (gro gn_rec));
          let rd_gidx := g_rd (ginfo gn_rec) in
          let recl_gidx := g_rec_rec_list (grec gn_rec) in
          let rec_idx := g_rec_idx (gro gn_rec) in
          rely is_int64 rec_idx; rely is_gidx rd_gidx; rely is_gidx recl_gidx;
          let gn_recl := (gs (share adt)) @ recl_gidx in
          let gn_rd := (gs (share adt)) @ rd_gidx in
          rely (g_tag (ginfo gn_recl) =? GRANULE_STATE_REC_LIST);
          rely (g_tag (ginfo gn_rd) =? GRANULE_STATE_RD);
          rely (gtype gn_recl =? GRANULE_STATE_REC_LIST);
          rely (gtype gn_rd =? GRANULE_STATE_RD);
          let gn_recl' := gn_recl {gnorm: (gnorm gn_recl) {g_data: (g_data (gnorm gn_recl)) # rec_idx == 0}} in
          let gn_rec' := gn_rec {ginfo: (ginfo gn_rec) {g_rd: 0} {g_tag: GRANULE_STATE_DELEGATED}}
                                {gnorm: zero_granule_data_normal} {grec: zero_granule_data_rec} in
          rely (gcnt gn_rd >? 0);
          let gn_rd' := gn_rd {gcnt: (gcnt gn_rd) - 1} in
          let e1 := EVT CPU_ID (RECL recl_gidx rec_idx UNSET_RECL) in
          let e' := EVT CPU_ID (REL rec_gidx (gn_rec' {glock: Some CPU_ID})) in
          let e2 := EVT CPU_ID (DEC_RD_GCNT rd_gidx) in
          Some (adt {log: e2 :: e' :: e1 :: e :: log adt}
                    {share: (share adt) {gs: (gs (share adt)) # recl_gidx == gn_recl'
                                                              # rec_gidx == (gn_rec' {gtype: GRANULE_STATE_DELEGATED})
                                                              # rd_gidx == gn_rd'}},
                VZ64 0)
        else Some (adt {log: e' :: e :: log adt}, VZ64 1)
      else Some (adt, VZ64 1)
    end.

End Spec.

