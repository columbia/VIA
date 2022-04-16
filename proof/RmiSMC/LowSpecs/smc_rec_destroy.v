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

  Definition smc_rec_destroy_spec0 (rec_addr: Z64) (adt: RData) : option (RData * Z64) :=
    match rec_addr with
    | VZ64 _rec_addr =>
      rely is_int64 _rec_addr;
      when'' _g_rec_base, _g_rec_ofst, adt == find_lock_unused_granule_spec (VZ64 _rec_addr) (VZ64 3) adt;
      when _t'2 == is_null_spec (_g_rec_base, _g_rec_ofst) adt;
      rely is_int _t'2;
      if (_t'2 =? 0) then
        when adt == rec_destroy_ops_spec (_g_rec_base, _g_rec_ofst) adt;
        let _ret := 0 in
        Some (adt, (VZ64 _ret))
      else
        let _ret := 1 in
        Some (adt, (VZ64 _ret))
     end
    .

End SpecLow.
