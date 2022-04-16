Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import TableAux.Spec.
Require Import AbsAccessor.Spec.
Require Import TableDataOpsIntro.Spec.
Require Import TableDataOpsRef3.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition smc_rtt_create_spec0 (rtt_addr: Z64) (rd_addr: Z64) (map_addr: Z64) (level: Z64) (adt: RData) : option (RData * Z64) :=
    match rtt_addr, rd_addr, map_addr, level with
    | VZ64 _rtt_addr, VZ64 _rd_addr, VZ64 _map_addr, VZ64 _level =>
      let _ret := 0 in
      rely is_int64 _map_addr;
      rely is_int64 _level;
      when _t'1 == validate_table_commands_spec (VZ64 _map_addr) (VZ64 _level) (VZ64 1) (VZ64 3) (VZ64 3) adt;
      rely is_int _t'1;
      rely is_int64 _t'1;
      let _ret := _t'1 in
      if (_ret =? 0) then
        rely is_int64 _rtt_addr;
        when'' _g_rtt_base, _g_rtt_ofst, adt == find_lock_granule_spec (VZ64 _rtt_addr) (VZ64 1) adt;
        rely is_int _g_rtt_ofst;
        when _t'6 == is_null_spec (_g_rtt_base, _g_rtt_ofst) adt;
        rely is_int _t'6;
        if (_t'6 =? 1) then
          let _ret := 1 in
          Some (adt, (VZ64 _ret))
        else
          rely is_int64 _rd_addr;
          when'' _g_rd_base, _g_rd_ofst, adt == find_lock_granule_spec (VZ64 _rd_addr) (VZ64 2) adt;
          rely is_int _g_rd_ofst;
          when _t'5 == is_null_spec (_g_rd_base, _g_rd_ofst) adt;
          rely is_int _t'5;
          if (_t'5 =? 1) then
            let _ret := 1 in
            when adt == granule_unlock_spec (_g_rtt_base, _g_rtt_ofst) adt;
            Some (adt, (VZ64 _ret))
          else
            when' _ret, adt == table_create3_spec (_g_rd_base, _g_rd_ofst) (VZ64 _map_addr) (VZ64 _level) (_g_rtt_base, _g_rtt_ofst) (VZ64 _rtt_addr) adt;
            rely is_int64 _ret;
            when adt == granule_unlock_spec (_g_rd_base, _g_rd_ofst) adt;
            when adt == granule_unlock_spec (_g_rtt_base, _g_rtt_ofst) adt;
            Some (adt, (VZ64 _ret))
      else
        Some (adt, (VZ64 _ret))
     end
    .

End SpecLow.
