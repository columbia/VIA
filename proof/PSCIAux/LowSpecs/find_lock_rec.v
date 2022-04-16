Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition find_lock_rec_spec0 (g_rd: Pointer) (rec_list: Pointer) (rec_idx: Z64) (adt: RData) : option (RData * Pointer) :=
    match g_rd, rec_list, rec_idx with
    | (_g_rd_base, _g_rd_ofst), (_rec_list_base, _rec_list_ofst), VZ64 _rec_idx =>
      rely is_int64 _rec_idx;
      when'' _g_rec_base, _g_rec_ofst, adt == realm_get_rec_entry_spec (VZ64 _rec_idx) (_rec_list_base, _rec_list_ofst) adt;
      rely is_int _g_rec_ofst;
      when _t'10 == is_null_spec (_g_rec_base, _g_rec_ofst) adt;
      rely is_int _t'10;
      if (_t'10 =? 1) then
        Some (adt, (_g_rec_base, _g_rec_ofst))
      else
        when adt == granule_lock_spec (_g_rec_base, _g_rec_ofst) adt;
        when _t'9, adt == granule_get_state_spec (_g_rec_base, _g_rec_ofst) adt;
        rely is_int _t'9;
        if (_t'9 =? 3) then
          when'' _t'3_base, _t'3_ofst == get_g_rec_rd_spec (_g_rec_base, _g_rec_ofst) adt;
          rely is_int _t'3_ofst;
          when _t'4 == ptr_eq_spec (_t'3_base, _t'3_ofst) (_g_rd_base, _g_rd_ofst) adt;
          rely is_int _t'4;
          if (_t'4 =? 1) then
            when'' _t'6_base, _t'6_ofst, adt == realm_get_rec_entry_spec (VZ64 _rec_idx) (_rec_list_base, _rec_list_ofst) adt;
            rely is_int _t'6_ofst;
            when _t'7 == ptr_eq_spec (_t'6_base, _t'6_ofst) (_g_rec_base, _g_rec_ofst) adt;
            rely is_int _t'7;
            let _t'5 := (_t'7 =? 1) in
            if _t'5 then
              Some (adt, (_g_rec_base, _g_rec_ofst))
            else
              when adt == granule_unlock_spec (_g_rec_base, _g_rec_ofst) adt;
              when'' _t'2_base, _t'2_ofst == null_ptr_spec  adt;
              rely is_int _t'2_ofst;
              Some (adt, (_t'2_base, _t'2_ofst))
          else
            let _t'5 := 0 in
            when adt == granule_unlock_spec (_g_rec_base, _g_rec_ofst) adt;
            when'' _t'2_base, _t'2_ofst == null_ptr_spec  adt;
            rely is_int _t'2_ofst;
            Some (adt, (_t'2_base, _t'2_ofst))
        else
          when adt == granule_unlock_spec (_g_rec_base, _g_rec_ofst) adt;
          when'' _t'8_base, _t'8_ofst == null_ptr_spec  adt;
          rely is_int _t'8_ofst;
          Some (adt, (_t'8_base, _t'8_ofst))
     end
    .

End SpecLow.
