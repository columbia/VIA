Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import TableAux2.Spec.
Require Import TableAux.Specs.granule_fill_table.

Local Open Scope Z_scope.

Section Spec.

  Definition table_create_aux_spec (g_rd': Pointer) (g_llt: Pointer) (g_rtt': Pointer) (llt_pte: Z64) (ll_table: Pointer) (level: Z64) (index: Z64) (map_addr: Z64) (rtt_addr: Z64) (adt: RData) : option RData :=
    match llt_pte, level, index, map_addr, rtt_addr with
    | VZ64 llt_pte, VZ64 level, VZ64 index, VZ64 map_addr, VZ64 rtt_addr =>
      rely is_int64 llt_pte; rely is_int64 level; rely is_int64 index; rely is_int64 map_addr; rely is_int64 rtt_addr;
      rely prop_dec ((buffer (priv adt)) @ SLOT_DELEGATED = None);
      rely (peq (base g_rd') ginfo_loc);
      rely (peq (base g_llt) ginfo_loc);
      rely (peq (base g_rtt') ginfo_loc);
      rely (peq (base ll_table) buffer_loc);
      rely ((offset ll_table) =? SLOT_TABLE);
      let rd_gidx := offset g_rd' in
      let llt_gidx := offset g_llt in
      let rtt_gidx := offset g_rtt' in
      rely is_gidx rd_gidx; rely is_gidx llt_gidx; rely is_gidx rtt_gidx;
      when lltg == (buffer (priv adt)) @ (offset ll_table);
      rely prop_dec (lltg = llt_gidx);
      let gn_llt := (gs (share adt)) @ llt_gidx in
      let gn_rtt := (gs (share adt)) @ rtt_gidx in
      rely (g_tag (ginfo gn_llt) =? GRANULE_STATE_TABLE);
      rely (gtype gn_llt =? GRANULE_STATE_TABLE);
      rely (gtype gn_rtt =? GRANULE_STATE_DELEGATED);
      rely prop_dec (glock gn_llt = Some CPU_ID);
      rely prop_dec (glock gn_rtt = Some CPU_ID);
      let ipa_state := PTE_TO_IPA_STATE llt_pte in
      if (ipa_state =? IPA_STATE_VACANT) || (ipa_state =? IPA_STATE_DESTROYED) then
        let pte_val := IPA_STATE_TO_PTE ipa_state in
        match fill_table (Z.to_nat PGTES_PER_TABLE) (g_data (gnorm gn_rtt)) 0 pte_val 0 with
        | (tbl', _, _) =>
          let llt' := (g_data (gnorm gn_llt)) # index == (Z.lor rtt_addr PGTE_S2_TABLE) in
          let grtt' := gn_rtt {ginfo: (ginfo gn_rtt) {g_tag: GRANULE_STATE_TABLE} {g_rd: rd_gidx} {g_refcount: (g_refcount (ginfo (gn_rtt))) + 1}}
                              {gnorm : (gnorm gn_rtt) {g_data : tbl'}} {gaux: mkAuxillaryVars level index llt_gidx} in
          let gllt' := gn_llt {ginfo : (ginfo gn_llt) {g_refcount : g_refcount (ginfo gn_llt) + 1}}
                            {gnorm: (gnorm gn_llt) {g_data: llt'}} in
          Some adt {share : (share adt) {gs : ((gs (share adt)) # rtt_gidx == grtt') # llt_gidx == gllt'}}
        end
      else
        if ipa_state =? IPA_STATE_ABSENT then
          rely (level =? RTT_PAGE_LEVEL);
          let pa := __entry_to_phys llt_pte 2 in
          let pte_val := Z.lor (IPA_STATE_TO_PTE IPA_STATE_ABSENT) pa in
          match fill_table (Z.to_nat PGTES_PER_TABLE) (g_data (gnorm gn_rtt)) 0 pte_val GRANULE_SIZE with
          | (tbl', _, _) =>
            let llt' := (g_data (gnorm gn_llt)) # index == (Z.lor rtt_addr PGTE_S2_TABLE) in
            let grtt' := gn_rtt {ginfo: (ginfo gn_rtt) {g_tag: GRANULE_STATE_TABLE} {g_rd: rd_gidx}
                                                      {g_refcount: (g_refcount (ginfo (gn_rtt))) + PGTES_PER_TABLE + 1}}
                                {gnorm : (gnorm gn_rtt) {g_data : tbl'}} {gaux: mkAuxillaryVars level index llt_gidx} in
            let gllt' := gn_llt {gnorm: (gnorm gn_llt) {g_data: llt'}} in
            Some adt {share : (share adt) {gs : ((gs (share adt)) # rtt_gidx == grtt') # llt_gidx == gllt'}}
          end
        else if ipa_state =? IPA_STATE_PRESENT then
              rely (level =? RTT_PAGE_LEVEL);
              rely GRANULE_ALIGNED map_addr;
              let pa := __entry_to_phys llt_pte 2 in
              let pte_val := Z.lor (Z.lor (IPA_STATE_TO_PTE IPA_STATE_PRESENT) pa) PGTE_S2_PAGE in
              match fill_table (Z.to_nat PGTES_PER_TABLE) (g_data (gnorm gn_rtt)) 0 pte_val GRANULE_SIZE with
              | (tbl', _, _) =>
                let llt' := (g_data (gnorm gn_llt)) # index == (Z.lor rtt_addr PGTE_S2_TABLE) in
                let grtt' := gn_rtt {ginfo: (ginfo gn_rtt) {g_tag: GRANULE_STATE_TABLE} {g_rd: rd_gidx}
                                                            {g_refcount: (g_refcount (ginfo (gn_rtt))) + PGTES_PER_TABLE + 1}}
                                    {gnorm : (gnorm gn_rtt) {g_data : tbl'}} {gaux: mkAuxillaryVars level index llt_gidx} in
                let gllt' := gn_llt {gnorm: (gnorm gn_llt) {g_data: llt'}} in
                let ipa_gidx := __addr_to_gidx map_addr in
                let tlbs' := fun cpu gidx => if gidx =? ipa_gidx then -1 else tlbs (share adt) cpu gidx in
                Some adt {share : (share adt) {gs : ((gs (share adt)) # rtt_gidx == grtt') # llt_gidx == gllt'} {tlbs: tlbs'}}
              end
            else None
    end.

End Spec.

