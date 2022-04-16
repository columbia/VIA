Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import TableAux.Spec.
Require Import AbsAccessor.Spec.
Require Import TableDataOpsIntro.Spec.
Require Import TableDataOpsRef3.Spec.
Require Import TableAux.Specs.granule_fill_table.

Local Open Scope Z_scope.

Section Spec.

  Definition destroy_table (llt_gidx: Z) (idx: Z) (rtt_addr: Z) (rtt_gidx: Z) (level: Z) (map_addr: Z) (adt: RData) :=
    let gn_llt := (gs (share adt)) @ llt_gidx in
    let llt_pte := (g_data (gnorm gn_llt)) @ idx in
    rely (g_tag (ginfo gn_llt) =? GRANULE_STATE_TABLE);
    rely (gtype gn_llt =? GRANULE_STATE_TABLE);
    rely is_int64 llt_pte;
    if (__entry_is_table llt_pte) && (rtt_addr =? (Z.land llt_pte ADDRESS_MASK)) then
      rely GRANULE_ALIGNED rtt_addr;
      let gn_rtt := (gs (share adt)) @ rtt_gidx in
      rely prop_dec (glock gn_rtt = None);
      rely (g_tag (ginfo gn_rtt) =? GRANULE_STATE_TABLE);
      rely (gtype gn_rtt =? GRANULE_STATE_TABLE);
      rely (tbl_level (gaux gn_llt) =? level - 1);
      rely (tbl_level (gaux gn_rtt) =? level);
      let e := EVT CPU_ID (ACQ rtt_gidx) in
      let e' := EVT CPU_ID (REL rtt_gidx (gn_rtt {glock: Some CPU_ID})) in
      rely prop_dec (forall i : ZIndexed.t, is_int64 (g_data (gnorm gn_rtt)) @ i = true);
      let ipa_gidx := __addr_to_gidx map_addr in
      let tlbs' := (fun ipa_state cpu gidx =>
                      if ipa_state =? IPA_STATE_PRESENT then
                        if (gidx >=? ipa_gidx) && (gidx <? ipa_gidx + 512) then -1
                        else tlbs (share adt) cpu gidx
                      else
                        if gidx =? ipa_gidx then -1
                        else tlbs (share adt) cpu gidx) in
      if (g_refcount (ginfo gn_rtt)) =? 1 then
        rely (g_refcount (ginfo gn_llt) >? 0);
        let ipa_state :=
            (if prop_dec (exists i : Z, 0 <= i < PGTES_PER_TABLE /\ PTE_TO_IPA_STATE (g_data (gnorm gn_rtt)) @ i = IPA_STATE_DESTROYED)
             then IPA_STATE_DESTROYED else IPA_STATE_VACANT)
        in
        let llt' := (g_data (gnorm gn_llt)) # idx == (IPA_STATE_TO_PTE ipa_state) in
        let gllt' := gn_llt {ginfo: (ginfo gn_llt) {g_refcount: (g_refcount (ginfo gn_llt)) - 1}}
                            {gnorm: (gnorm gn_llt) {g_data: llt'}} in
        let grtt' := gn_rtt {ginfo: (ginfo gn_rtt) {g_tag: GRANULE_STATE_DELEGATED} {g_rd: 0} {g_refcount: 0}}
                            {gnorm : zero_granule_data_normal} {grec: zero_granule_data_rec} in
        let e' := EVT CPU_ID (REL rtt_gidx (grtt' {glock: Some CPU_ID})) in
        Some (adt {log: EVT CPU_ID (REL llt_gidx gllt') :: e' :: e :: log adt}
                  {share : (share adt) {gs : ((gs (share adt)) # rtt_gidx == (grtt' {gtype: GRANULE_STATE_DELEGATED}))
                                                               # llt_gidx == gllt'}
                                       {tlbs: tlbs' ipa_state}},
              VZ64 0)
      else
        if (g_refcount (ginfo gn_rtt)) =? PGTES_PER_TABLE + 1 then
          rely (level =? RTT_PAGE_LEVEL);
          let pgte := (g_data (gnorm gn_rtt)) @ 0 in
          let ipa_state := PTE_TO_IPA_STATE pgte in
          let base_pa' := __entry_to_phys pgte (level - 1) in
          let base_pa := __entry_to_phys pgte level in
          rely is_int64 base_pa;
          rely is_int64 (base_pa + PGTES_PER_TABLE * GRANULE_SIZE);
          rely (__addr_is_level_aligned base_pa (level - 1));
          rely prop_dec (forall i : Z, 0 <= i < PGTES_PER_TABLE ->
                                  let e := (g_data (gnorm gn_rtt)) @ i in
                                  let pa := __entry_to_phys e level in
                                  PTE_TO_IPA_STATE e = ipa_state /\ pa = base_pa + i * GRANULE_SIZE);
          let new_pgte := (if ipa_state =? IPA_STATE_PRESENT then Z.lor (Z.lor (IPA_STATE_TO_PTE ipa_state) base_pa') PGTE_S2_BLOCK
                           else Z.lor (IPA_STATE_TO_PTE ipa_state) base_pa') in
          let llt' := (g_data (gnorm gn_llt)) # idx == new_pgte in
          let gllt' := gn_llt {gnorm: (gnorm gn_llt) {g_data: llt'}} in
          let grtt' := gn_rtt {ginfo: (ginfo gn_rtt) {g_tag: GRANULE_STATE_DELEGATED} {g_rd: 0} {g_refcount: 0}}
                              {gnorm : zero_granule_data_normal} {grec: zero_granule_data_rec} in
          let e' := EVT CPU_ID (REL rtt_gidx (grtt' {glock: Some CPU_ID})) in
          Some (adt {log: EVT CPU_ID (REL llt_gidx gllt') :: e' :: e :: log adt}
                    {share : (share adt) {gs : ((gs (share adt)) # rtt_gidx == (grtt' {gtype: GRANULE_STATE_DELEGATED}))
                                                                # llt_gidx == gllt'}
                                        {tlbs: tlbs' ipa_state}},
                VZ64 0)
        else None
    else Some (adt {log: EVT CPU_ID (REL llt_gidx gn_llt {glock: Some CPU_ID}) :: log adt}, VZ64 1).

  Definition smc_rtt_destroy_spec (rtt_addr: Z64) (rd_addr: Z64) (map_addr: Z64) (level: Z64) (adt: RData) : option (RData * Z64) :=
    match rtt_addr, rd_addr, map_addr, level with
    | VZ64 rtt_addr, VZ64 rd_addr, VZ64 map_addr, VZ64 level =>
      rely is_int64 rtt_addr; rely is_int64 rd_addr; rely is_int64 map_addr; rely is_int64 level;
      if (level >=? 1) && (level <=? 3) && __addr_is_level_aligned map_addr 3 then
        let rtt_gidx := __addr_to_gidx rtt_addr in
        let rd_gidx := __addr_to_gidx rd_addr in
        rely GRANULE_ALIGNED rtt_addr; rely GRANULE_ALIGNED rd_addr; rely GRANULE_ALIGNED map_addr;
        rely is_gidx rtt_gidx; rely is_gidx rd_gidx;
        when adt == query_oracle adt;
        let gn_rtt := (gs (share adt)) @ rtt_gidx in
        let grd := (gs (share adt)) @ rd_gidx in
        rely prop_dec (glock gn_rtt = None);
        rely prop_dec (glock grd = None);
        rely (g_tag (ginfo gn_rtt) =? GRANULE_STATE_DELEGATED);
        rely (g_tag (ginfo grd) =? GRANULE_STATE_RD);
        rely (gtype grd =? GRANULE_STATE_RD);
        let adt := adt {log: EVT CPU_ID (ACQ rd_gidx) :: EVT CPU_ID (ACQ rtt_gidx) :: log adt} in
        let idx0 := __addr_to_idx map_addr 0 in
        let idx1 := __addr_to_idx map_addr 1 in
        let idx2 := __addr_to_idx map_addr 2 in
        let idx3 := __addr_to_idx map_addr 3 in
        let ret_idx := (if level =? 1 then idx0 else if level =? 2 then idx1 else if level =? 3 then idx2 else idx3) in
        rely is_int64 idx0; rely is_int64 idx1; rely is_int64 idx2; rely is_int64 idx3;
        let rtt_gidx := __addr_to_gidx rtt_addr in
        rely is_gidx rtt_gidx;
        rely prop_dec ((buffer (priv adt)) @ SLOT_RD = None);
        rely prop_dec ((buffer (priv adt)) @ SLOT_TABLE = None);
        rely prop_dec ((buffer (priv adt)) @ SLOT_RTT2 = None);
        let root_gidx := (g_rtt (gnorm grd)) in
        rely is_gidx rd_gidx;
        (* hold root lock *)
        rely is_gidx root_gidx;
        let groot := (gs (share adt)) @ root_gidx in
        rely (tbl_level (gaux groot) =? 0);
        rely prop_dec (glock groot = None);
        rely (g_tag (ginfo groot) =? GRANULE_STATE_TABLE);
        rely (gtype groot =? GRANULE_STATE_TABLE);
        if level =? 1 then
          (* walk until root *)
          let adt := adt {log: EVT CPU_ID (RTT_WALK root_gidx map_addr 0) :: log adt} in
          let adt :=  adt {priv: (priv adt) {wi_llt: root_gidx} {wi_index: idx0}} in
          destroy_table root_gidx idx0 rtt_addr rtt_gidx 1 map_addr adt
        else
          (* walk deeper root *)
          rely (level >? 1);
          let entry0 := (g_data (gnorm groot)) @ idx0 in
            rely is_int64 entry0;
            let phys0 := __entry_to_phys entry0 3 in
            let lv1_gidx := __addr_to_gidx phys0 in
            rely is_int64 phys0;
            rely (__entry_is_table entry0) && (GRANULE_ALIGNED phys0) && (is_gidx lv1_gidx);
            (* level 1 valid, hold level 1 lock *)
            let glv1 := (gs (share adt)) @ lv1_gidx in
            rely prop_dec (glock glv1 = None);
            rely (tbl_level (gaux glv1) =? 1);
            if level =? 2 then
              (* walk until level 1 *)
              let adt := adt {log: EVT CPU_ID (RTT_WALK root_gidx map_addr 1) :: log adt} in
              let adt :=  adt {priv: (priv adt) {wi_llt: lv1_gidx} {wi_index: idx1}} in
              destroy_table lv1_gidx idx1 rtt_addr rtt_gidx 2 map_addr adt
            else
              (* walk deeper level 1 *)
              rely (level >? 2);
              rely (g_tag (ginfo glv1) =? GRANULE_STATE_TABLE);
              rely (gtype glv1 =? GRANULE_STATE_TABLE);
              let entry1 := (g_data (gnorm glv1)) @ idx1 in
              rely is_int64 entry1;
              let phys1 := __entry_to_phys entry1 3 in
              let lv2_gidx := __addr_to_gidx phys1 in
              rely is_int64 phys1;
              rely (__entry_is_table entry1) && (GRANULE_ALIGNED phys1) && (is_gidx lv2_gidx);
              (* level 2 valid, hold level 2 lock *)
              let glv2 := (gs (share adt)) @ lv2_gidx in
              rely (tbl_level (gaux glv2) =? 2);
              rely prop_dec (glock glv2 = None);
              if level =? 3 then
                (* walk until level 2 *)
                let adt := adt {log: EVT CPU_ID (RTT_WALK root_gidx map_addr 2) :: log adt} in
                let adt :=  adt {priv: (priv adt) {wi_llt: lv2_gidx} {wi_index: idx2}} in
                destroy_table lv2_gidx idx2 rtt_addr rtt_gidx 3 map_addr adt
              else None
      else Some (adt, VZ64 0)
    end.

End Spec.

