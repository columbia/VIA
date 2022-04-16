Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition realm_activate_ops_spec0 (rd: Pointer) (adt: RData) : option RData :=
    match rd with
    | (_rd_base, _rd_ofst) =>
      when adt == measurement_finish_spec (_rd_base, _rd_ofst) adt;
      when adt == set_rd_state_spec (_rd_base, _rd_ofst) 1 adt;
      Some adt
     end
    .

End SpecLow.
