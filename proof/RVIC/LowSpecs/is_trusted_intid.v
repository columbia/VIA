Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.

Local Open Scope Z_scope.

Section SpecLow.

  Definition is_trusted_intid_spec0 (intid: Z64) (adt: RData) : option Z :=
    match intid with
    | VZ64 _intid =>
      if (_intid >=? 0) then
        let _t'1 := (_intid <=? 31) in
        if _t'1 then
          Some 1
        else
          Some 0
      else
        let _t'1 := 0 in
        Some 0
     end
    .

End SpecLow.
