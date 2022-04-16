Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition realm_ns_step_spec0  (adt: RData) : option (RData * Z64) :=
    when' ret, adt == user_step_spec  adt;
    rely is_int64 ret;
    Some (adt, VZ64 ret)
    .

End SpecLow.
