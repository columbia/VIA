Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.

Local Open Scope Z_scope.

Section SpecLow.

  Definition rvic_target_is_valid_spec0 (target: Z64) (adt: RData) : option Z :=
    match target with
    | VZ64 _target =>
      let _mask := 1095233437695 in
      rely is_int64 (18446744073709551615 - _mask);
      rely is_int64 (Z.land _target (18446744073709551615 - _mask));
      let _tmp := (Z.land _target (18446744073709551615 - _mask)) in
      if (_tmp =? 0) then
        let _ret := 1 in
        Some _ret
      else
        let _ret := 0 in
        Some _ret
     end
    .

End SpecLow.
