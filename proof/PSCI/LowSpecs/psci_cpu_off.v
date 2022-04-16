Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition psci_cpu_off_spec0 (rec: Pointer) (adt: RData) : option RData :=
    match rec with
    | (_rec_base, _rec_ofst) =>
      when adt == set_psci_result_forward_psci_call_spec 1 adt;
      when adt == set_rec_runnable_spec (_rec_base, _rec_ofst) 0 adt;
      when adt == set_psci_result_x0_spec (VZ64 0) adt;
      Some adt
     end
    .

End SpecLow.
