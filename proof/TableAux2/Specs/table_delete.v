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

  Definition table_delete_spec (table: Pointer) (g_llt: Pointer) (adt: RData) : option (RData * Z64) :=
    rely peq (base table) buffer_loc;
    rely peq (base g_llt) ginfo_loc;
    when gidx == (buffer (priv adt)) @ (offset table);
    let llt_gidx := offset g_llt in
    rely is_gidx llt_gidx;
    let gn := (gs (share adt)) @ gidx in
    let gn_llt := (gs (share adt)) @ llt_gidx in
    rely prop_dec (glock gn = Some CPU_ID);
    rely prop_dec (glock gn_llt = Some CPU_ID);
    rely (g_refcount (ginfo gn_llt) >? 0);
    rely g_tag (ginfo gn) =? GRANULE_STATE_TABLE;
    rely prop_dec (forall i, is_int64 ((g_data (gnorm gn)) @ i) = true);
    let ipa_state :=
        (if prop_dec (exists i, 0 <= i < PGTES_PER_TABLE /\ PTE_TO_IPA_STATE ((g_data (gnorm gn)) @ i) = IPA_STATE_DESTROYED)
         then IPA_STATE_DESTROYED else IPA_STATE_VACANT) in
    let new_pgte := IPA_STATE_TO_PTE ipa_state in
    let g' := gn_llt {ginfo: (ginfo gn_llt) {g_refcount: g_refcount (ginfo gn_llt) - 1}} in
    Some (adt {share: (share adt) {gs: (gs (share adt)) # llt_gidx == g'}}, VZ64 new_pgte).

End Spec.

