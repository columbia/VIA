Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import TableDataOpsIntro.Spec.
Require Import TableDataOpsRef2.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition table_unmap3_spec (g_rd: Pointer) (map_addr: Z64) (level: Z64) (adt: RData) : option (RData * Z64) :=
    match map_addr, level with
    | VZ64 map_addr, VZ64 level =>
      rely is_int64 map_addr; rely (level >=? 3); rely GRANULE_ALIGNED map_addr; rely is_int64 level;
      let idx0 := __addr_to_idx map_addr 0 in
      let idx1 := __addr_to_idx map_addr 1 in
      let idx2 := __addr_to_idx map_addr 2 in
      let idx3 := __addr_to_idx map_addr 3 in
      let ret_idx := (if level =? 1 then idx0 else if level =? 2 then idx1 else if level =? 3 then idx2 else idx3) in
      rely (peq (base g_rd) ginfo_loc);
      rely prop_dec ((buffer (priv adt)) @ SLOT_RD = None);
      rely prop_dec ((buffer (priv adt)) @ SLOT_TABLE = None);
      let rd_gidx := (offset g_rd) in
      let grd := (gs (share adt)) @ rd_gidx in
      rely (g_tag (ginfo grd) =? GRANULE_STATE_RD);
      rely prop_dec (glock grd = Some CPU_ID);
      let root_gidx := (g_rtt (gnorm grd)) in
      rely is_gidx rd_gidx; rely is_gidx root_gidx;
      when adt == query_oracle adt;
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
      if (__entry_is_table entry0) && (GRANULE_ALIGNED phys0) && (is_gidx lv1_gidx) then
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
        if (__entry_is_table entry1) && (GRANULE_ALIGNED phys1) && (is_gidx lv2_gidx) then
          (* level 2 valid, hold level 2 lock *)
          let glv2 := (gs (share adt)) @ lv2_gidx in
          rely (tbl_level (gaux glv2) =? 2);
          rely prop_dec (glock glv2 = None);
          if level =? 3 then
            (* walk until level 2 *)
            let adt := adt {log: EVT CPU_ID (RTT_WALK root_gidx map_addr 2) :: log adt} in
            let adt :=  adt {priv: (priv adt) {wi_llt: lv2_gidx} {wi_index: idx2}} in
            unmap_table lv2_gidx idx2 level map_addr adt
          else
            (* walk deeper level 2 *)
            rely (g_tag (ginfo glv2) =? GRANULE_STATE_TABLE);
            rely (gtype glv2 =? GRANULE_STATE_TABLE);
            let entry2 := (g_data (gnorm glv2)) @ idx2 in
            rely is_int64 entry2;
            let phys2 := __entry_to_phys entry2 3 in
            let lv3_gidx := __addr_to_gidx phys2 in
            if (__entry_is_table entry2) && (GRANULE_ALIGNED phys2) && (is_gidx lv3_gidx) then
              (* level 2 valid, hold level 2 lock *)
              let adt := adt {log: EVT CPU_ID (REL lv2_gidx glv2 {glock: Some CPU_ID}) :: EVT CPU_ID (ACQ lv3_gidx) :: log adt} in
              let glv3 := (gs (share adt)) @ lv3_gidx in
              rely prop_dec (glock glv3 = None);
              rely (tbl_level (gaux glv3) =? 3);
              if level =? 4 then
                (* walk until level 3 *)
                let adt := adt {log: EVT CPU_ID (RTT_WALK root_gidx map_addr 3) :: log adt} in
                let adt :=  adt {priv: (priv adt) {wi_llt: lv3_gidx} {wi_index: idx3}} in
                unmap_table lv3_gidx idx3 level map_addr adt
              else (* can't be other level *)
                None
            else
              (* level 3 invalid *)
              Some (adt {priv: (priv adt) {wi_llt: 0} {wi_index: ret_idx}}, VZ64 1)
        else
          (* level 2 invalid *)
          Some (adt {priv: (priv adt) {wi_llt: 0} {wi_index: ret_idx}}, VZ64 1)
      else
        (* level 1 invalid *)
        Some (adt {priv: (priv adt) {wi_llt: 0} {wi_index: ret_idx}}, VZ64 1)
  end.

End Spec.

