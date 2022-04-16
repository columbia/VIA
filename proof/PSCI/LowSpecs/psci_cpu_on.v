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

  Definition psci_cpu_on_spec0 (rec: Pointer) (target_cpu: Z64) (entry_point_address: Z64) (context_id: Z64) (adt: RData) : option RData :=
    match rec, target_cpu, entry_point_address, context_id with
    | (_rec_base, _rec_ofst), VZ64 _target_cpu, VZ64 _entry_point_address, VZ64 _context_id =>
      when' _par_base == get_rec_par_base_spec (_rec_base, _rec_ofst) adt;
      rely is_int64 _par_base;
      when' _par_end == get_rec_par_end_spec (_rec_base, _rec_ofst) adt;
      rely is_int64 _par_end;
      if (_entry_point_address <? _par_base) then
        let _t'8 := 1 in
        when adt == set_psci_result_x0_spec (VZ64 4294967287) adt;
        Some adt
      else
        let _t'8 := (_entry_point_address >=? _par_end) in
        if _t'8 then
          when adt == set_psci_result_x0_spec (VZ64 4294967287) adt;
          Some adt
        else
          rely is_int64 _target_cpu;
          when' _t'3 == mpidr_to_rec_idx_spec (VZ64 _target_cpu) adt;
          rely is_int64 _t'3;
          rely is_int _t'3;
          let _idx1 := _t'3 in
          when' _t'4 == get_rec_rec_idx_spec (_rec_base, _rec_ofst) adt;
          rely is_int64 _t'4;
          rely is_int _t'4;
          let _idx2 := _t'4 in
          if (_idx1 =? _idx2) then
            when adt == set_psci_result_x0_spec (VZ64 4294967292) adt;
            Some adt
          else
            when'' _g_target_rec_base, _g_target_rec_ofst, adt == psci_lookup_target_spec (_rec_base, _rec_ofst) (VZ64 _target_cpu) adt;
            rely is_int _g_target_rec_ofst;
            when _t'7 == is_null_spec (_g_target_rec_base, _g_target_rec_ofst) adt;
            rely is_int _t'7;
            if (_t'7 =? 1) then
              when adt == set_psci_result_x0_spec (VZ64 4294967294) adt;
              Some adt
            else
              when'' _target_rec_base, _target_rec_ofst, adt == granule_map_spec (_g_target_rec_base, _g_target_rec_ofst) 4 adt;
              rely is_int _target_rec_ofst;
              rely is_int64 _entry_point_address;
              when adt == psci_cpu_on_target_spec (_g_target_rec_base, _g_target_rec_ofst) (_target_rec_base, _target_rec_ofst) (_rec_base, _rec_ofst) (VZ64 _entry_point_address) (VZ64 _target_cpu) adt;
              Some adt
     end
    .

End SpecLow.
