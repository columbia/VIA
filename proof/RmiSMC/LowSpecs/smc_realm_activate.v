Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiOps.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition smc_realm_activate_spec0 (rd_addr: Z64) (adt: RData) : option (RData * Z64) :=
    match rd_addr with
    | VZ64 _rd_addr =>
      rely is_int64 _rd_addr;
      when'' _g_rd_base, _g_rd_ofst, adt == find_lock_granule_spec (VZ64 _rd_addr) (VZ64 2) adt;
      when _t'4 == is_null_spec (_g_rd_base, _g_rd_ofst) adt;
      rely is_int _t'4;
      if (_t'4 =? 0) then
        when'' _rd_base, _rd_ofst, adt == granule_map_spec (_g_rd_base, _g_rd_ofst) 2 adt;
        when _t'3 == get_rd_state_spec (_rd_base, _rd_ofst) adt;
        rely is_int _t'3;
        if (_t'3 =? 0) then
          when adt == realm_activate_ops_spec (_rd_base, _rd_ofst) adt;
          let _ret := 0 in
          when adt == buffer_unmap_spec (_rd_base, _rd_ofst) adt;
          when adt == granule_unlock_spec (_g_rd_base, _g_rd_ofst) adt;
          Some (adt, (VZ64 _ret))
        else
          let _ret := 1 in
          when adt == buffer_unmap_spec (_rd_base, _rd_ofst) adt;
          when adt == granule_unlock_spec (_g_rd_base, _g_rd_ofst) adt;
          Some (adt, (VZ64 _ret))
      else
        let _ret := 1 in
        Some (adt, (VZ64 _ret))
     end
    .

End SpecLow.
