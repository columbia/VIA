Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import TableAux2.Spec.
Require Import TableAux.Spec.
Require Import TableAux.Specs.granule_fill_table.

Local Open Scope Z_scope.

Section Spec.

  Definition table_destroy_aux_spec (g_llt: Pointer) (g_tbl: Pointer) (ll_table: Pointer) (level: Z64) (index: Z64) (map_addr: Z64) (adt: RData) : option (RData * Z64) :=
    match level, index, map_addr with
    | VZ64 level, VZ64 index, VZ64 map_addr =>
      rely is_int64 level; rely is_int64 index; rely is_int64 map_addr; rely GRANULE_ALIGNED map_addr;
      rely (peq (base g_llt) ginfo_loc);
      rely (peq (base g_tbl) ginfo_loc);
      rely (peq (base ll_table) buffer_loc);
      rely prop_dec ((offset ll_table) = SLOT_TABLE);
      rely prop_dec ((buffer (priv adt)) @ SLOT_RTT2 = None);
      when llt_gidx == (buffer (priv adt)) @ (offset ll_table);
      rely prop_dec (llt_gidx = (offset g_llt));
      let rtt_gidx := offset g_tbl in
      rely is_gidx rtt_gidx; rely is_gidx llt_gidx;
      rely prop_dec (llt_gidx <> rtt_gidx);
      let gn_llt := (gs (share adt)) @ llt_gidx in
      let gn_rtt := (gs (share adt)) @ rtt_gidx in
      let llt_pte := (g_data (gnorm gn_llt)) @ index in
      rely is_int64 llt_pte;
      rely prop_dec (glock gn_rtt = Some CPU_ID);
      rely prop_dec (glock gn_llt = Some CPU_ID);
      rely (g_tag (ginfo gn_rtt) =? GRANULE_STATE_TABLE);
      rely (g_tag (ginfo gn_llt) =? GRANULE_STATE_TABLE);
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
        let llt' := (g_data (gnorm gn_llt)) # index == (IPA_STATE_TO_PTE ipa_state) in
        let gllt' := gn_llt {ginfo: (ginfo gn_llt) {g_refcount: (g_refcount (ginfo gn_llt)) - 1}}
                            {gnorm: (gnorm gn_llt) {g_data: llt'}} in
        let grtt' := gn_rtt {ginfo: (ginfo gn_rtt) {g_tag: GRANULE_STATE_DELEGATED} {g_rd: 0} {g_refcount: 0}}
                            {gnorm : zero_granule_data_normal} {grec: zero_granule_data_rec} in
        Some (adt {share : (share adt) {gs : ((gs (share adt)) # rtt_gidx == grtt') # llt_gidx == gllt'}
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
          let llt' := (g_data (gnorm gn_llt)) # index == new_pgte in
          let gllt' := gn_llt {gnorm: (gnorm gn_llt) {g_data: llt'}} in
          let grtt' := gn_rtt {ginfo: (ginfo gn_rtt) {g_tag: GRANULE_STATE_DELEGATED} {g_rd: 0} {g_refcount: 0}}
                              {gnorm : zero_granule_data_normal} {grec: zero_granule_data_rec} in
          Some (adt {share : (share adt) {gs : ((gs (share adt)) # rtt_gidx == grtt') # llt_gidx == gllt'}
                                        {tlbs: tlbs' ipa_state}},
                VZ64 0)
        else None
    end.

End Spec.

