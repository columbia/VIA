Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import TableDataOpsIntro.Spec.
Require Import TableDataOpsRef1.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition table_create2_spec (g_rd: Pointer) (map_addr: Z64) (level: Z64) (g_rtt': Pointer) (rtt_addr: Z64) (adt: RData) : option (RData * Z64) :=
    match map_addr, level, rtt_addr with
    | VZ64 map_addr, VZ64 level, VZ64 rtt_addr =>
      rely is_int64 map_addr; rely is_int64 rtt_addr; rely GRANULE_ALIGNED map_addr; rely is_int64 level;
      let idx0 := __addr_to_idx map_addr 0 in
      let idx1 := __addr_to_idx map_addr 1 in
      let idx2 := __addr_to_idx map_addr 2 in
      let idx3 := __addr_to_idx map_addr 3 in
      let ret_idx := (if level =? 1 then idx0 else if level =? 2 then idx1 else if level =? 3 then idx2 else idx3) in
      let rtt_gidx := __addr_to_gidx rtt_addr in
      rely is_gidx rtt_gidx;
      rely (peq (base g_rd) ginfo_loc);
      rely (peq (base g_rtt') ginfo_loc);
      rely (offset g_rtt' =? rtt_gidx);
      rely prop_dec ((buffer (priv adt)) @ SLOT_RD = None);
      rely prop_dec ((buffer (priv adt)) @ SLOT_TABLE = None);
      rely prop_dec ((buffer (priv adt)) @ SLOT_DELEGATED = None);
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
      if level =? 1 then
        (* walk until root *)
        let adt := adt {log: EVT CPU_ID (RTT_WALK root_gidx map_addr 0) :: log adt} in
        let adt :=  adt {priv: (priv adt) {wi_llt: root_gidx} {wi_index: idx0}} in
        create_table root_gidx idx0 rtt_addr rtt_gidx rd_gidx 1 map_addr adt
      else
        (* walk deeper root *)
        rely (level >? 1);
        rely (g_tag (ginfo groot) =? GRANULE_STATE_TABLE);
        rely (gtype groot =? GRANULE_STATE_TABLE);
        let entry0 := (g_data (gnorm groot)) @ idx0 in
        rely is_int64 entry0;
        let phys0 := __entry_to_phys entry0 3 in
        let lv1_gidx := __addr_to_gidx phys0 in
        if (__entry_is_table entry0) && (GRANULE_ALIGNED phys0) && (is_gidx lv1_gidx) then
          (* level 1 valid, hold level 1 lock *)
          let glv1 := (gs (share adt)) @ lv1_gidx in
          rely prop_dec (glock glv1 = None);
          rely (tbl_level (gaux glv1) =? 1);
          if level =? 2 then
            (* walk until level 1 *)
            let adt := adt {log: EVT CPU_ID (RTT_WALK root_gidx map_addr 1) :: log adt} in
            let adt :=  adt {priv: (priv adt) {wi_llt: lv1_gidx} {wi_index: idx1}} in
            create_table lv1_gidx idx1 rtt_addr rtt_gidx rd_gidx 2 map_addr adt
          else
            (* walk deeper level 1 *)
            rely (level >? 2);
            rely (g_tag (ginfo glv1) =? GRANULE_STATE_TABLE);
            rely (gtype glv1 =? GRANULE_STATE_TABLE);
            let entry1 := (g_data (gnorm glv1)) @ idx1 in
            rely is_int64 entry1;
            let phys1 := __entry_to_phys entry1 3 in
            let lv2_gidx := __addr_to_gidx phys1 in
            if (__entry_is_table entry1) && (GRANULE_ALIGNED phys1) && (is_gidx lv2_gidx) then
              (* level 2 valid, hold level 2 lock *)
              let adt := adt {log: EVT CPU_ID (RTT_WALK root_gidx map_addr 2) :: log adt} in
              let glv2 := (gs (share adt)) @ lv2_gidx in
              rely (tbl_level (gaux glv2) =? 2);
              rely prop_dec (glock glv2 = None);
              if level =? 3 then
                (* walk until level 2 *)
                let adt :=  adt {priv: (priv adt) {wi_llt: lv2_gidx} {wi_index: idx2}} in
                create_table lv2_gidx idx2 rtt_addr rtt_gidx rd_gidx 3 map_addr adt
              else None
            else
              (* level 2 invalid *)
              Some (adt {priv: (priv adt) {wi_llt: 0} {wi_index: ret_idx}}, VZ64 1)
        else
          (* level 1 invalid *)
          Some (adt {priv: (priv adt) {wi_llt: 0} {wi_index: ret_idx}}, VZ64 1)
    end.

End Spec.

