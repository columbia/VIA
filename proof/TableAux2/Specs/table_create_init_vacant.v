Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import TableAux.Spec.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition table_create_init_vacant_spec (ipa_state: Z64) (pte: Pointer) (g_llt: Pointer) (adt: RData) : option RData :=
    match ipa_state with
    | VZ64 ipa_state =>
      rely is_int64 ipa_state;
      let pte_val := IPA_STATE_TO_PTE ipa_state in
      rely is_int64 pte_val; rely is_int64 (pte_val + GRANULE_SIZE * PGTES_PER_TABLE);
      rely (peq (base pte) buffer_loc);
      rely (peq (base g_llt) ginfo_loc);
      when gidx == (buffer (priv adt)) @ (offset pte);
      let llt_gidx := offset g_llt in
      rely is_gidx llt_gidx;
      let gn := (gs (share adt)) @ gidx in
      let gn_llt := (gs (share adt)) @ llt_gidx in
      rely prop_dec (glock gn = Some CPU_ID);
      rely prop_dec (glock gn_llt = Some CPU_ID);
      rely g_tag (ginfo gn) =? GRANULE_STATE_TABLE;
      rely prop_dec (gidx <> llt_gidx);
      match fill_table (Z.to_nat PGTES_PER_TABLE) (g_data (gnorm gn)) 0 pte_val 0 with
      | (table', _, _) =>
        let g' := gn {gnorm : (gnorm gn) {g_data : table'}} in
        let llt' := gn_llt {ginfo: (ginfo gn_llt) {g_refcount: (g_refcount (ginfo gn_llt)) + 1}} in
        Some adt {share : (share adt) {gs : (gs (share adt)) # gidx == g' # llt_gidx == llt'}}
      end
    end.

End Spec.
