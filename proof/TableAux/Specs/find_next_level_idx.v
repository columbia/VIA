Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition find_next_level_idx_spec (g_tbl: Pointer) (idx: Z64) (adt: RData) : option (RData * Pointer) :=
    match idx with
    | VZ64 idx =>
      rely is_int64 idx;
      rely (peq (base g_tbl) ginfo_loc);
      rely prop_dec ((buffer (priv adt)) @ SLOT_TABLE = None);
      let gidx := offset g_tbl in
      let gn := (gs (share adt)) @ gidx in
      rely is_gidx gidx;
      rely (g_tag (ginfo gn) =? GRANULE_STATE_TABLE);
      rely prop_dec (glock gn = Some CPU_ID);
      let entry := (g_data (gnorm gn)) @ idx in
      rely is_int64 entry;
      let phys := __entry_to_phys entry 3 in
      let gidx := __addr_to_gidx phys in
      rely is_int64 phys; rely is_int gidx;
      if (__entry_is_table entry) && (GRANULE_ALIGNED phys) && (is_gidx gidx) then
        Some (adt, (ginfo_loc, gidx))
      else Some (adt, NULL)
    end.

End Spec.

