Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PSCIHandler.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition handle_realm_rsi_spec0 (rec: Pointer) (adt: RData) : option (RData * Z) :=
    None.

End SpecLow.
