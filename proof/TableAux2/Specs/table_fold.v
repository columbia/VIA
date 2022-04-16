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

  Definition table_fold_spec (table: Pointer) (level: Z64) (g_tbl: Pointer) (adt: RData) : option (RData * Z64) :=
    match level with
    | VZ64 level =>
      rely is_int64 level; rely (level >? 0);
      rely peq (base table) buffer_loc;
      rely peq (base g_tbl) ginfo_loc;
      when gidx == (buffer (priv adt)) @ (offset table);
      let tbl_gidx := offset g_tbl in
      rely is_gidx gidx;
      rely prop_dec (gidx = tbl_gidx);
      let gn := (gs (share adt)) @ gidx in
      let gn_tbl := (gs (share adt)) @ tbl_gidx in
      rely prop_dec (glock gn = Some CPU_ID);
      rely prop_dec (glock gn_tbl = Some CPU_ID);
      rely g_tag (ginfo gn) =? GRANULE_STATE_TABLE;
      rely prop_dec (forall i, is_int64 ((g_data (gnorm gn)) @ i) = true);
      let pgte := (g_data (gnorm gn)) @ 0 in
      let ipa_state := PTE_TO_IPA_STATE pgte in
      let base_pa' := __entry_to_phys pgte (level - 1) in
      let base_pa := __entry_to_phys pgte level in
      rely is_int64 base_pa; rely is_int64 (base_pa + PGTES_PER_TABLE * GRANULE_SIZE);
      rely (level =? RTT_PAGE_LEVEL);
      rely (__addr_is_level_aligned base_pa (level - 1));
      rely prop_dec (forall i (Hi: 0 <= i < PGTES_PER_TABLE),
                      let e := (g_data (gnorm gn)) @ i in
                      let pa := __entry_to_phys e level in
                      PTE_TO_IPA_STATE e = ipa_state /\ pa = base_pa + i * GRANULE_SIZE);
      let new_pgte := (if ipa_state =? IPA_STATE_PRESENT then
                          Z.lor (Z.lor (IPA_STATE_TO_PTE ipa_state) base_pa') PGTE_S2_BLOCK
                        else Z.lor (IPA_STATE_TO_PTE ipa_state) base_pa') in
      rely is_int64 new_pgte;
      let g' := gn_tbl {ginfo : (ginfo gn_tbl) {g_refcount : g_refcount (ginfo gn_tbl) - PGTES_PER_TABLE}} in
      Some (adt {share : (share adt) {gs : (gs (share adt)) # tbl_gidx == g'}}, VZ64 new_pgte)
    end.

End Spec.

