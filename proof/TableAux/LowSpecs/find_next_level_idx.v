Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition find_next_level_idx_spec0 (g_tbl: Pointer) (idx: Z64) (adt: RData) : option (RData * Pointer) :=
    match g_tbl, idx with
    | (_g_tbl_base, _g_tbl_ofst), VZ64 _idx =>
      when'' _table_base, _table_ofst, adt == granule_map_spec (_g_tbl_base, _g_tbl_ofst) 5 adt;
      rely is_int _table_ofst;
      rely is_int64 _idx;
      when' _entry == pgte_read_spec (_table_base, _table_ofst) (VZ64 _idx) adt;
      rely is_int64 _entry;
      when adt == buffer_unmap_spec (_table_base, _table_ofst) adt;
      when _t'6 == entry_is_table_spec (VZ64 _entry) adt;
      rely is_int _t'6;
      if (_t'6 =? 0) then
        when'' _next_base, _next_ofst == null_ptr_spec  adt;
        rely is_int _next_ofst;
        Some (adt, (_next_base, _next_ofst))
      else
        when' _t'4 == entry_to_phys_spec (VZ64 _entry) (VZ64 3) adt;
        rely is_int64 _t'4;
        when'' _t'5_base, _t'5_ofst == find_granule_spec (VZ64 _t'4) adt;
        rely is_int _t'5_ofst;
        Some (adt, (_t'5_base, _t'5_ofst))
     end
    .

End SpecLow.
