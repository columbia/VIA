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

  Definition smc_granule_delegate_spec0 (addr: Z64) (adt: RData) : option (RData * Z64) :=
    match addr with
    | VZ64 _addr =>
      rely is_int64 _addr;
      when'' _g_base, _g_ofst, adt == find_lock_granule_spec (VZ64 _addr) (VZ64 0) adt;
      when _t'2 == is_null_spec (_g_base, _g_ofst) adt;
      rely is_int _t'2;
      if (_t'2 =? 0) then
        when adt == granule_delegate_ops_spec (_g_base, _g_ofst) (VZ64 _addr) adt;
        let _ret := 0 in
        Some (adt, (VZ64 _ret))
      else
        let _ret := 1 in
        Some (adt, (VZ64 _ret))
     end
    .

End SpecLow.
