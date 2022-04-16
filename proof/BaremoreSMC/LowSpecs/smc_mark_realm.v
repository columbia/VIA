Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import BaremoreHandler.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition smc_mark_realm_spec0 (addr: Z64) (adt: RData) : option RData :=
    match addr with
    | VZ64 _addr =>
      rely is_int64 (3288334336 + 256);
      rely is_int (3288334336 + 256);
      rely is_int64 _addr;
      when adt == set_monitor_call_spec (3288334336 + 256) (VZ64 _addr) adt;
      when adt == el3_sync_lel_spec  adt;
      when' _t'1 == get_monitor_call_ret_spec  adt;
      rely is_int64 _t'1;
      rely is_int _t'1;
      let _ret := _t'1 in
      rely is_int (1 - _ret);
      when adt == assert_cond_spec (1 - _ret) adt;
      Some adt
     end
    .

End SpecLow.
