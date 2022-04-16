Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.

Local Open Scope Z_scope.

Section Spec.

  Definition rvic_target_is_valid_spec (target: Z64) (adt: RData) : option Z :=
    match target with
    | VZ64 target =>
        rely is_int64 target;
        let tmp := (Z.land target 18446742978476113920) in
        rely is_int64 tmp;
        if tmp =? 0 then
          Some 1
        else
          Some 0
    end.

End Spec.

