Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition asc_mark_realm_spec0 (addr: Z64) (adt: RData) : option (RData * Z64) :=
    match addr with
    | VZ64 _addr =>
      let _ret := 0 in
      rely is_int64 _addr;
      when' _idx == addr_to_gidx_spec (VZ64 _addr) adt;
      rely is_int64 _idx;
      when _t'4 == check_granule_idx_spec (VZ64 _idx) adt;
      rely is_int _t'4;
      if (_t'4 =? 0) then
        let _ret := 1 in
        Some (adt, (VZ64 _ret))
      else
        when'' _lock_base, _lock_ofst == find_spinlock_spec (VZ64 _addr) adt;
        rely is_int _lock_ofst;
        when adt == spinlock_acquire_spec (_lock_base, _lock_ofst) adt;
        when' _t'3 == get_pas_spec (VZ64 _idx) adt;
        rely is_int64 _t'3;
        rely is_int _t'3;
        let _pas := _t'3 in
        if (negb (_pas =? 9)) then
          let _ret := 1 in
          when adt == spinlock_release_spec (_lock_base, _lock_ofst) adt;
          Some (adt, (VZ64 _ret))
        else
          when adt == set_pas_spec (VZ64 _idx) (VZ64 11) adt;
          when adt == tlbi_by_pa_spec (VZ64 _addr) adt;
          when adt == spinlock_release_spec (_lock_base, _lock_ofst) adt;
          Some (adt, (VZ64 _ret))
     end
    .

End SpecLow.
