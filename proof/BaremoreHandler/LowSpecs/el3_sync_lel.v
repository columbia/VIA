Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import BaremoreService.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition el3_sync_lel_spec0  (adt: RData) : option RData :=
    when _reason, adt == baremore_enter_spec  adt;
    rely is_int _reason;
    if (_reason =? 256) then
      when' _addr == get_monitor_call_arg_spec  adt;
      rely is_int64 _addr;
      when' _ret, adt == asc_mark_realm_spec (VZ64 _addr) adt;
      rely is_int64 _ret;
      when adt == baremore_return_rmm_spec (VZ64 _ret) adt;
      Some adt
    else
      if (_reason =? 257) then
        when' _addr == get_monitor_call_arg_spec  adt;
        rely is_int64 _addr;
        when' _t'5, adt == asc_mark_nonsecure_spec (VZ64 _addr) adt;
        rely is_int64 _t'5;
        rely is_int _t'5;
        let _ret := _t'5 in
        rely is_int64 _ret;
        when adt == baremore_return_rmm_spec (VZ64 _ret) adt;
        Some adt
      else
        if (_reason =? 3) then
          when adt == baremore_to_ns_spec  adt;
          Some adt
        else
          if (_reason =? 4) then
            when adt == baremore_to_rmm_spec  adt;
            Some adt
          else
            when adt == assert_cond_spec 0 adt;
            Some adt
    .

End SpecLow.
