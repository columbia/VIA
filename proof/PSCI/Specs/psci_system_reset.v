Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import PSCIAux2.Spec.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition psci_system_reset_spec (rec: Pointer) (adt: RData) : option RData :=
    when adt == system_off_reboot_spec rec adt;
    Some adt {priv: (priv adt) {psci_forward_psci_call: 1}}.

End Spec.

