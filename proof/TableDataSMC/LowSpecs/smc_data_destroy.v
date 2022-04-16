Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import TableDataOpsIntro.Spec.
Require Import TableDataOpsRef3.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition smc_data_destroy_spec0 (rd_addr: Z64) (map_addr: Z64) (adt: RData) : option (RData * Z64) :=
    match rd_addr, map_addr with
    | VZ64 _rd_addr, VZ64 _map_addr =>
      rely is_int64 _rd_addr;
      when'' _g_rd_base, _g_rd_ofst, adt == find_lock_granule_spec (VZ64 _rd_addr) (VZ64 2) adt;
      rely is_int _g_rd_ofst;
      when _t'3 == is_null_spec (_g_rd_base, _g_rd_ofst) adt;
      rely is_int _t'3;
      if (_t'3 =? 1) then
        let _ret := 1 in
        Some (adt, (VZ64 _ret))
      else
        rely is_int64 _map_addr;
        when' _ret, adt == data_destroy3_spec (_g_rd_base, _g_rd_ofst) (VZ64 _map_addr) adt;
        rely is_int64 _ret;
        when adt == granule_unlock_spec (_g_rd_base, _g_rd_ofst) adt;
        Some (adt, (VZ64 _ret))
     end
    .

End SpecLow.
