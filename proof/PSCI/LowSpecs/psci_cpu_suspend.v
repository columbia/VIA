Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition psci_cpu_suspend_spec0 (rec: Pointer) (entry_point_address: Z64) (context_id: Z64) (adt: RData) : option RData :=
    match rec, entry_point_address, context_id with
    | (_rec_base, _rec_ofst), VZ64 _entry_point_address, VZ64 _context_id =>
      when adt == set_psci_result_forward_psci_call_spec 1 adt;
      when adt == set_psci_result_x0_spec (VZ64 0) adt;
      Some adt
     end
    .

End SpecLow.
