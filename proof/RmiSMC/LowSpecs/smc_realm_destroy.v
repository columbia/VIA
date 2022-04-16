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

  Definition smc_realm_destroy_spec0 (rd_addr: Z64) (adt: RData) : option (RData * Z64) :=
    match rd_addr with
    | VZ64 _rd_addr =>
      rely is_int64 _rd_addr;
      when'' _g_rd_base, _g_rd_ofst, adt == find_lock_unused_granule_spec (VZ64 _rd_addr) (VZ64 2) adt;
      when _t'6 == is_null_spec (_g_rd_base, _g_rd_ofst) adt;
      rely is_int _t'6;
      if (_t'6 =? 0) then
        when'' _rd_base, _rd_ofst, adt == granule_map_spec (_g_rd_base, _g_rd_ofst) 2 adt;
        when'' _g_rtt_base, _g_rtt_ofst == get_rd_g_rtt_spec (_rd_base, _rd_ofst) adt;
        rely is_int _g_rtt_ofst;
        when'' _g_rec_list_base, _g_rec_list_ofst == get_rd_g_rec_list_spec (_rd_base, _rd_ofst) adt;
        rely is_int _g_rec_list_ofst;
        when adt == buffer_unmap_spec (_rd_base, _rd_ofst) adt;
        when adt == granule_lock_spec (_g_rtt_base, _g_rtt_ofst) adt;
        when' _t'5, adt == get_g_rtt_refcount_spec (_g_rtt_base, _g_rtt_ofst) adt;
        rely is_int64 _t'5;
        if (negb (_t'5 =? 0)) then
          when adt == granule_unlock_spec (_g_rtt_base, _g_rtt_ofst) adt;
          let _ret := 1 in
          when adt == granule_unlock_spec (_g_rd_base, _g_rd_ofst) adt;
          Some (adt, (VZ64 _ret))
        else
          when adt == realm_destroy_ops_spec (_g_rtt_base, _g_rtt_ofst) (_g_rec_list_base, _g_rec_list_ofst) (_g_rd_base, _g_rd_ofst) adt;
          let _ret := 0 in
          when adt == granule_unlock_spec (_g_rd_base, _g_rd_ofst) adt;
          Some (adt, (VZ64 _ret))
      else
        let _ret := 1 in
        Some (adt, (VZ64 _ret))
     end
    .

End SpecLow.
