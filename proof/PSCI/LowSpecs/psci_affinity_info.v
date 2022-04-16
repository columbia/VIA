Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PSCIAux2.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition psci_affinity_info_spec0 (rec: Pointer) (target_affinity: Z64) (lowest_affinity_level: Z64) (adt: RData) : option RData :=
    match rec, target_affinity, lowest_affinity_level with
    | (_rec_base, _rec_ofst), VZ64 _target_affinity, VZ64 _lowest_affinity_level =>
      if (negb (_lowest_affinity_level =? 0)) then
        when adt == set_psci_result_x0_spec (VZ64 4294967294) adt;
        Some adt
      else
        rely is_int64 _target_affinity;
        when'' _g_target_rec_base, _g_target_rec_ofst, adt == psci_lookup_target_spec (_rec_base, _rec_ofst) (VZ64 _target_affinity) adt;
        rely is_int _g_target_rec_ofst;
        when _t'4 == is_null_spec (_g_target_rec_base, _g_target_rec_ofst) adt;
        rely is_int _t'4;
        if (_t'4 =? 1) then
          when adt == set_psci_result_x0_spec (VZ64 4294967294) adt;
          Some adt
        else
          when'' _target_rec_base, _target_rec_ofst, adt == granule_map_spec (_g_target_rec_base, _g_target_rec_ofst) 4 adt;
          rely is_int _target_rec_ofst;
          when _runnable == get_rec_runnable_spec (_target_rec_base, _target_rec_ofst) adt;
          rely is_int _runnable;
          if (_runnable =? 1) then
            let _ret := 0 in
            when adt == buffer_unmap_spec (_target_rec_base, _target_rec_ofst) adt;
            when adt == granule_unlock_spec (_g_target_rec_base, _g_target_rec_ofst) adt;
            rely is_int64 _ret;
            when adt == set_psci_result_x0_spec (VZ64 _ret) adt;
            Some adt
          else
            let _ret := 1 in
            when adt == buffer_unmap_spec (_target_rec_base, _target_rec_ofst) adt;
            when adt == granule_unlock_spec (_g_target_rec_base, _g_target_rec_ofst) adt;
            rely is_int64 _ret;
            when adt == set_psci_result_x0_spec (VZ64 _ret) adt;
            Some adt
     end
    .

End SpecLow.
