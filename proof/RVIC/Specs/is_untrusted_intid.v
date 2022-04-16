Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.

Local Open Scope Z_scope.

Section Spec.

  Definition is_untrusted_intid_spec (intid: Z64) (adt: RData) : option Z :=
    match intid with
    | VZ64 intid =>
      if (intid >=? 32) && (intid <=? 511) then
          Some 1
      else
          Some 0
    end.

End Spec.

