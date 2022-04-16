Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition psci_version_spec (rec: Pointer) (adt: RData) : option RData :=
    Some adt {priv: (priv adt) {psci_x0: 65537}}.

End Spec.
