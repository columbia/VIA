Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import TableDataOpsRef3.Spec.
Require Import TableDataOpsIntro.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition smc_data_create_spec (data_addr: Z64) (rd_addr: Z64) (map_addr: Z64) (src_addr: Z64) (adt: RData) : option (RData * Z64) :=
    match data_addr, rd_addr, map_addr, src_addr with
    | VZ64 data_addr, VZ64 rd_addr, VZ64 map_addr, VZ64 src_addr =>
      rely is_int64 data_addr; rely is_int64 rd_addr; rely is_int64 map_addr; rely is_int64 src_addr;
      let src_gidx := __addr_to_gidx src_addr in
      let data_gidx := __addr_to_gidx data_addr in
      let rd_gidx := __addr_to_gidx rd_addr in
      rely GRANULE_ALIGNED src_addr; rely GRANULE_ALIGNED data_addr; rely GRANULE_ALIGNED rd_addr;
      rely is_gidx src_gidx; rely is_gidx data_gidx; rely is_gidx rd_gidx;
      when adt == query_oracle adt;
      let gn_src := (gs (share adt)) @ src_gidx in
      let gn_data := (gs (share adt)) @ data_gidx in
      let gn_rd := (gs (share adt)) @ rd_gidx in
      rely prop_dec (glock gn_data = None);
      rely prop_dec (glock gn_rd = None);
      rely (g_tag (ginfo gn_data) =? GRANULE_STATE_DELEGATED);
      rely (g_tag (ginfo gn_rd) =? GRANULE_STATE_RD);
      let adt := adt {log: EVT CPU_ID (ACQ rd_gidx) :: EVT CPU_ID (ACQ data_gidx) :: log adt} in
      rely prop_dec ((buffer (priv adt)) @ SLOT_RD = None);
      rely prop_dec ((buffer (priv adt)) @ SLOT_TABLE = None);
      rely prop_dec ((buffer (priv adt)) @ SLOT_DELEGATED = None);
      rely prop_dec ((buffer (priv adt)) @ SLOT_NS = None);
      rely (g_realm_state (gnorm gn_rd) =? REALM_STATE_NEW);
      let idx0 := __addr_to_idx map_addr 0 in
      let idx1 := __addr_to_idx map_addr 1 in
      let idx2 := __addr_to_idx map_addr 2 in
      let idx3 := __addr_to_idx map_addr 3 in
      let ret_idx := idx3 in
      let root_gidx := (g_rtt (gnorm gn_rd)) in
      rely is_gidx root_gidx;
      let adt := adt {log: EVT CPU_ID (RTT_WALK root_gidx map_addr 3) :: log adt} in
      (* hold root lock *)
      let groot := (gs (share adt)) @ root_gidx in
      rely (tbl_level (gaux groot) =? 0);
      rely prop_dec (glock groot = None);
      rely (g_tag (ginfo groot) =? GRANULE_STATE_TABLE);
      rely (gtype groot =? GRANULE_STATE_TABLE);
      (* walk deeper root *)
      let entry0 := (g_data (gnorm groot)) @ idx0 in
      rely is_int64 entry0;
      let phys0 := __entry_to_phys entry0 3 in
      let lv1_gidx := __addr_to_gidx phys0 in
      rely ((__entry_is_table entry0) && (GRANULE_ALIGNED phys0) && (is_gidx lv1_gidx));
      (* level 1 valid, hold level 1 lock *)
      let glv1 := (gs (share adt)) @ lv1_gidx in
      rely prop_dec (glock glv1 = None);
      rely (tbl_level (gaux glv1) =? 1);
      (* walk deeper level 1 *)
      rely (g_tag (ginfo glv1) =? GRANULE_STATE_TABLE);
      rely (gtype glv1 =? GRANULE_STATE_TABLE);
      let entry1 := (g_data (gnorm glv1)) @ idx1 in
      rely is_int64 entry1;
      let phys1 := __entry_to_phys entry1 3 in
      let lv2_gidx := __addr_to_gidx phys1 in
      rely ((__entry_is_table entry1) && (GRANULE_ALIGNED phys1) && (is_gidx lv2_gidx));
      (* level 2 valid, hold level 2 lock *)
      let glv2 := (gs (share adt)) @ lv2_gidx in
      rely (tbl_level (gaux glv2) =? 2);
      rely prop_dec (glock glv2 = None);
      (* walk deeper level 2 *)
      rely (g_tag (ginfo glv2) =? GRANULE_STATE_TABLE);
      rely (gtype glv2 =? GRANULE_STATE_TABLE);
      let entry2 := (g_data (gnorm glv2)) @ idx2 in
      rely is_int64 entry2;
      let phys2 := __entry_to_phys entry2 3 in
      let lv3_gidx := __addr_to_gidx phys2 in
      rely ((__entry_is_table entry2) && (GRANULE_ALIGNED phys2) && (is_gidx lv3_gidx));
      (* level 2 valid, hold level 2 lock *)
      let glv3 := (gs (share adt)) @ lv3_gidx in
      rely prop_dec (glock glv3 = None);
      rely (tbl_level (gaux glv3) =? 3);
      let adt :=  adt {priv: (priv adt) {wi_llt: lv3_gidx} {wi_index: idx3}} in
      (* create data *)
      let llt_gidx := lv3_gidx in
      let idx := idx3 in
      let gn_llt := (gs (share adt)) @ llt_gidx in
      let gn_data := (gs (share adt)) @ data_gidx in
      let gn_src := (gs (share adt)) @ src_gidx in
      rely (g_tag (ginfo gn_llt) =? GRANULE_STATE_TABLE);
      rely (gtype gn_llt =? GRANULE_STATE_TABLE);
      rely (gtype gn_data =? GRANULE_STATE_DELEGATED);
      rely (g_tag (ginfo gn_src) =? GRANULE_STATE_NS);
      rely (gtype gn_src =? GRANULE_STATE_NS);
      rely prop_dec (glock gn_data = Some CPU_ID);
      rely (tbl_level (gaux gn_data) =? 0);
      let llt_pte := (g_data (gnorm gn_llt)) @ idx in
      rely is_int64 llt_pte;
      if PTE_TO_IPA_STATE llt_pte =? IPA_STATE_VACANT then
        rely prop_dec (rtts (share adt) rd_gidx (__addr_to_gidx map_addr) = (0, false));
        let e := EVT CPU_ID (COPY_NS src_gidx (READ_DATA data_gidx)) in
        let gdata' := gn_data {ginfo: (ginfo gn_data) {g_tag: GRANULE_STATE_DATA} {g_rd: rd_gidx}}
                              {gnorm: (gnorm gn_data) {g_data: g_data (gnorm gn_src)}}
                              {gaux: mkAuxillaryVars 0 0 (__addr_to_gidx map_addr)} in
        let pte_val := Z.lor (IPA_STATE_TO_PTE IPA_STATE_ABSENT) data_addr in
        let llt' := (g_data (gnorm gn_llt)) # idx == pte_val in
        let gllt' := gn_llt {ginfo : (ginfo gn_llt) {g_refcount : g_refcount (ginfo gn_llt) + 1}}
                            {gnorm: (gnorm gn_llt) {g_data: llt'}} in
        let cp := EVT CPU_ID (COPY_NS src_gidx (READ_DATA data_gidx)) in
        Some (adt {log: EVT CPU_ID (REL data_gidx (gdata' {glock: Some CPU_ID})) ::
                            EVT CPU_ID (REL rd_gidx (gn_rd {glock: Some CPU_ID})) ::
                            EVT CPU_ID (REL llt_gidx gllt' {glock: Some CPU_ID}) :: cp :: log adt}
                  {share : (share adt) {gs : ((gs (share adt)) # data_gidx == (gdata' {gtype: GRANULE_STATE_DATA})) # llt_gidx == gllt'}
                                        {rtts: fun rd ipa_gidx => if (rd =? rd_gidx) && (ipa_gidx =? __addr_to_gidx map_addr) then
                                                            (data_gidx, false)
                                                          else (rtts (share adt)) rd ipa_gidx}},
              VZ64 0)
      else
        Some (adt {log: EVT CPU_ID (REL data_gidx (gn_data {glock: Some CPU_ID})) ::
                            EVT CPU_ID (REL rd_gidx (gn_rd {glock: Some CPU_ID})) ::
                            EVT CPU_ID (REL llt_gidx gn_llt {glock: Some CPU_ID}) :: log adt},
              VZ64 1)
    end.

End Spec.

