Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import BaremoreHandler.Spec.
Require Import AbsAccessor.Spec.
Require Import SMCHandler.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition rmm_handler_spec  (adt: RData) : option RData :=
    when adt == el3_sync_lel_spec  adt;
    when adt == enter_rmm_spec  adt;
    when' _function_id == read_reg_spec 0 adt;
    rely is_int64 _function_id;
    when' _arg0 == read_reg_spec 1 adt;
    rely is_int64 _arg0;
    when' _arg1 == read_reg_spec 2 adt;
    rely is_int64 _arg1;
    when' _arg2 == read_reg_spec 3 adt;
    rely is_int64 _arg2;
    when' _arg3 == read_reg_spec 4 adt;
    rely is_int64 _arg3;
    when' _ret, adt == handle_ns_smc_spec (VZ64 _function_id) (VZ64 _arg0) (VZ64 _arg1) (VZ64 _arg2) (VZ64 _arg3) adt;
    rely is_int64 _ret;
    if (negb (_ret =? 2)) then
      when adt == exit_rmm_spec (VZ64 _ret) adt;
      when adt == el3_sync_lel_spec  adt;
      Some adt
    else
      Some adt.

End Spec.

