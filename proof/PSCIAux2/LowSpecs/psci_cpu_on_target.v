Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PSCIAux.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition psci_cpu_on_target_spec0 (g_target_rec: Pointer) (target_rec: Pointer) (rec: Pointer) (entry_point_address: Z64) (target_cpu: Z64) (adt: RData) : option RData :=
    match g_target_rec, target_rec, rec, entry_point_address, target_cpu with
    | (_g_target_rec_base, _g_target_rec_ofst), (_target_rec_base, _target_rec_ofst), (_rec_base, _rec_ofst), VZ64 _entry_point_address, VZ64 _target_cpu =>
      when _t'1 == get_rec_runnable_spec (_target_rec_base, _target_rec_ofst) adt;
      rely is_int _t'1;
      if (negb (_t'1 =? 0)) then
        when adt == buffer_unmap_spec (_target_rec_base, _target_rec_ofst) adt;
        when adt == granule_unlock_spec (_g_target_rec_base, _g_target_rec_ofst) adt;
        when adt == set_psci_result_x0_spec (VZ64 4294967292) adt;
        Some adt
      else
        when adt == psci_reset_rec_spec (_rec_base, _rec_ofst) (_target_rec_base, _target_rec_ofst) adt;
        rely is_int64 _entry_point_address;
        when adt == set_rec_pc_spec (_target_rec_base, _target_rec_ofst) (VZ64 _entry_point_address) adt;
        when adt == set_rec_runnable_spec (_target_rec_base, _target_rec_ofst) 1 adt;
        when adt == set_psci_result_forward_psci_call_spec 1 adt;
        rely is_int64 _target_cpu;
        when adt == set_psci_result_forward_x1_spec (VZ64 _target_cpu) adt;
        when adt == buffer_unmap_spec (_target_rec_base, _target_rec_ofst) adt;
        when adt == granule_unlock_spec (_g_target_rec_base, _g_target_rec_ofst) adt;
        when adt == set_psci_result_x0_spec (VZ64 0) adt;
        Some adt
     end
    .

End SpecLow.
