Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import PSCIAux2.Spec.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition psci_system_reset_spec0 (rec: Pointer) (adt: RData) : option RData :=
    match rec with
    | (_rec_base, _rec_ofst) =>
      when adt == system_off_reboot_spec (_rec_base, _rec_ofst) adt;
      when adt == set_psci_result_forward_psci_call_spec 1 adt;
      Some adt
     end
    .

End SpecLow.
