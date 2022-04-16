Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RVIC3.Spec.
Require Import AbsAccessor.Spec.
Require Import RVIC2.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition set_clear_masked_spec0 (rec: Pointer) (target: Z64) (intid: Z64) (masked: Z) (adt: RData) : option RData :=
    match rec, target, intid, masked with
    | (_rec_base, _rec_ofst), VZ64 _target, VZ64 _intid, _masked =>
      rely is_int64 _target;
      rely is_int64 _intid;
      when' _x0, adt == validate_and_lookup_target_spec (_rec_base, _rec_ofst) (VZ64 _target) (VZ64 _intid) adt;
      rely is_int64 _x0;
      when'' _target_rec_base, _target_rec_ofst == get_target_rec_spec  adt;
      rely is_int _target_rec_ofst;
      when adt == set_rvic_result_x0_spec (VZ64 _x0) adt;
      if (_x0 =? 0) then
        when'' _rvic_base, _rvic_ofst == get_rec_rvic_spec (_target_rec_base, _target_rec_ofst) adt;
        rely is_int _rvic_ofst;
        if (_masked =? 1) then
          when adt == rvic_set_masked_spec (_rvic_base, _rvic_ofst) (VZ64 _intid) adt;
          when'' _g_rec_base, _g_rec_ofst == get_rec_g_rec_spec (_target_rec_base, _target_rec_ofst) adt;
          rely is_int _g_rec_ofst;
          when adt == buffer_unmap_spec (_target_rec_base, _target_rec_ofst) adt;
          when adt == granule_unlock_spec (_g_rec_base, _g_rec_ofst) adt;
          Some adt
        else
          when _was_masked == rvic_is_masked_spec (_rvic_base, _rvic_ofst) (VZ64 _intid) adt;
          rely is_int _was_masked;
          when _need_notify == need_ns_notify_spec (_rec_base, _rec_ofst) (_target_rec_base, _target_rec_ofst) (VZ64 _intid) adt;
          rely is_int _need_notify;
          if (negb (_was_masked =? 0)) then
            let _t'6 := (negb (_need_notify =? 0)) in
            if _t'6 then
              when adt == set_rvic_result_ns_notify_spec 1 adt;
              when adt == set_rvic_result_target_spec (VZ64 _target) adt;
              when'' _g_rec_base, _g_rec_ofst == get_rec_g_rec_spec (_target_rec_base, _target_rec_ofst) adt;
              rely is_int _g_rec_ofst;
              when adt == buffer_unmap_spec (_target_rec_base, _target_rec_ofst) adt;
              when adt == granule_unlock_spec (_g_rec_base, _g_rec_ofst) adt;
              Some adt
            else
              when adt == rvic_clear_masked_spec (_rvic_base, _rvic_ofst) (VZ64 _intid) adt;
              when'' _g_rec_base, _g_rec_ofst == get_rec_g_rec_spec (_target_rec_base, _target_rec_ofst) adt;
              rely is_int _g_rec_ofst;
              when adt == buffer_unmap_spec (_target_rec_base, _target_rec_ofst) adt;
              when adt == granule_unlock_spec (_g_rec_base, _g_rec_ofst) adt;
              Some adt
          else
            let _t'6 := 0 in
            when adt == rvic_clear_masked_spec (_rvic_base, _rvic_ofst) (VZ64 _intid) adt;
            when'' _g_rec_base, _g_rec_ofst == get_rec_g_rec_spec (_target_rec_base, _target_rec_ofst) adt;
            rely is_int _g_rec_ofst;
            when adt == buffer_unmap_spec (_target_rec_base, _target_rec_ofst) adt;
            when adt == granule_unlock_spec (_g_rec_base, _g_rec_ofst) adt;
            Some adt
      else
        Some adt
     end
    .

End SpecLow.
