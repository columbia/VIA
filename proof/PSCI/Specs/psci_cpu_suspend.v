Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition psci_cpu_suspend_spec (rec: Pointer) (entry_point_address: Z64) (context_id: Z64) (adt: RData) : option RData :=
    Some adt {priv : (priv adt) {psci_forward_psci_call : 1} {psci_x0: PSCI_RETURN_SUCCESS}}.

End Spec.

