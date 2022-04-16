Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import TableAux.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition table_create_init_present_spec (level: Z64) (ll_table: Pointer) (index: Z64) (map_addr: Z64) (llt_pte: Z64) (pte: Pointer) (g_rtt: Pointer) (adt: RData) : option RData :=
    match level, llt_pte, index, map_addr with
    | VZ64 level, VZ64 llt_pte, VZ64 index, VZ64 map_addr =>
      rely is_int64 llt_pte; rely is_int64 map_addr; rely is_int64 index;
      if level =? 3 then
        let pa := __entry_to_phys llt_pte 2 in
        rely is_int64 pa;
        let pte_val := Z.lor (Z.lor (IPA_STATE_TO_PTE IPA_STATE_PRESENT) pa) PGTE_S2_PAGE in
        rely is_int64 pte_val; rely is_int64 (pte_val + GRANULE_SIZE * PGTES_PER_TABLE);
        rely (peq (base pte) buffer_loc);
        rely (peq (base ll_table) buffer_loc);
        rely (peq (base g_rtt) ginfo_loc);
        when rtt_gidx == (buffer (priv adt)) @ (offset pte);
        when llt_gidx == (buffer (priv adt)) @ (offset ll_table);
        rely is_gidx llt_gidx; rely is_gidx rtt_gidx;
        rely prop_dec (rtt_gidx = offset g_rtt);
        rely prop_dec (llt_gidx <> rtt_gidx);
        let gn_llt := (gs (share adt)) @ llt_gidx in
        let gn_rtt := (gs (share adt)) @ rtt_gidx in
        rely prop_dec (glock gn_llt = Some CPU_ID);
        rely prop_dec (glock gn_rtt = Some CPU_ID);
        rely g_tag (ginfo gn_llt) =? GRANULE_STATE_TABLE;
        rely g_tag (ginfo gn_rtt) =? GRANULE_STATE_TABLE;
        rely GRANULE_ALIGNED map_addr;
        let ipa_gidx := __addr_to_gidx map_addr in
        match fill_table (Z.to_nat PGTES_PER_TABLE) (g_data (gnorm gn_rtt)) 0 pte_val GRANULE_SIZE with
        | (table', _, _) =>
          let grtt' := gn_rtt {gnorm : (gnorm gn_rtt) {g_data : table'}}
                              {ginfo: (ginfo gn_rtt) {g_refcount: (g_refcount (ginfo gn_rtt)) + 512}} in
          let gllt' := gn_llt {gnorm: (gnorm gn_llt) {g_data: (g_data (gnorm gn_llt)) # index == 0}} in
          Some adt {share : (share adt) {gs : ((gs (share adt)) # llt_gidx == gllt') # rtt_gidx == grtt'}
                                        {tlbs: fun cpu gidx => if gidx =? ipa_gidx then -1 else tlbs (share adt) cpu gidx}}
        end
      else None
    end.

End Spec.

