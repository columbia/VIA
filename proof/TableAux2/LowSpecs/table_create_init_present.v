Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import TableAux.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition table_create_init_present_spec0 (level: Z64) (ll_table: Pointer) (index: Z64) (map_addr: Z64) (llt_pte: Z64) (pte: Pointer) (g_rtt: Pointer) (adt: RData) : option RData :=
    match level, ll_table, index, map_addr, llt_pte, pte, g_rtt with
    | VZ64 _level, (_ll_table_base, _ll_table_ofst), VZ64 _index, VZ64 _map_addr, VZ64 _llt_pte, (_pte_base, _pte_ofst), (_g_rtt_base, _g_rtt_ofst) =>
      if (_level =? 3) then
        rely is_int64 _index;
        when adt == pgte_write_spec (_ll_table_base, _ll_table_ofst) (VZ64 _index) (VZ64 0) adt;
        rely is_int64 _map_addr;
        when adt == invalidate_block_spec (VZ64 _map_addr) adt;
        rely is_int64 (_level - 1);
        rely is_int64 _llt_pte;
        when' _pa == entry_to_phys_spec (VZ64 _llt_pte) (VZ64 (_level - 1)) adt;
        rely is_int64 _pa;
        rely is_int64 (2 * 72057594037927936);
        rely is_int64 (Z.lor (2 * 72057594037927936) _pa);
        rely is_int64 (Z.lor (Z.lor (2 * 72057594037927936) _pa) 2011);
        when adt == granule_fill_table_spec (_pte_base, _pte_ofst) (VZ64 (Z.lor (Z.lor (2 * 72057594037927936) _pa) 2011)) (VZ64 4096) adt;
        when adt == granule_refcount_inc_spec (_g_rtt_base, _g_rtt_ofst) (VZ64 512) adt;
        Some adt
      else
        when adt == assert_cond_spec 0 adt;
        Some adt
     end
    .

End SpecLow.
