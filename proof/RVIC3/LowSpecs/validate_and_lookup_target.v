Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RVIC2.Spec.
Require Import RVIC.Spec.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition validate_and_lookup_target_spec0 (rec: Pointer) (target: Z64) (intid: Z64) (adt: RData) : option (RData * Z64) :=
    match rec, target, intid with
    | (_rec_base, _rec_ofst), VZ64 _target, VZ64 _intid =>
      rely is_int64 _target;
      when _target_valid == rvic_target_is_valid_spec (VZ64 _target) adt;
      rely is_int _target_valid;
      if (_target_valid =? 0) then
        Some (adt, (VZ64 1))
      else
        rely is_int64 _intid;
        when _t'4 == is_trusted_intid_spec (VZ64 _intid) adt;
        rely is_int _t'4;
        if (_t'4 =? 0) then
          when _t'6 == is_untrusted_intid_spec (VZ64 _intid) adt;
          rely is_int _t'6;
          let _t'5 := (_t'6 =? 0) in
          if _t'5 then
            Some (adt, (VZ64 1))
          else
            when adt == find_lock_map_target_rec_spec (_rec_base, _rec_ofst) (VZ64 _target) adt;
            when'' _t'2_base, _t'2_ofst == get_target_rec_spec  adt;
            rely is_int _t'2_ofst;
            when _t'3 == is_null_spec (_t'2_base, _t'2_ofst) adt;
            rely is_int _t'3;
            if (_t'3 =? 1) then
              Some (adt, (VZ64 1))
            else
              Some (adt, (VZ64 0))
        else
          let _t'5 := 0 in
          when adt == find_lock_map_target_rec_spec (_rec_base, _rec_ofst) (VZ64 _target) adt;
          when'' _t'2_base, _t'2_ofst == get_target_rec_spec  adt;
          rely is_int _t'2_ofst;
          when _t'3 == is_null_spec (_t'2_base, _t'2_ofst) adt;
          rely is_int _t'3;
          if (_t'3 =? 1) then
            Some (adt, (VZ64 1))
          else
            Some (adt, (VZ64 0))
     end
    .

End SpecLow.
