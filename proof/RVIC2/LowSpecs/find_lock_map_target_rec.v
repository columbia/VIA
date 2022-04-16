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

  Definition find_lock_map_target_rec_spec0 (rec: Pointer) (target: Z64) (adt: RData) : option RData :=
    match rec, target with
    | (_rec_base, _rec_ofst), VZ64 _target =>
      rely is_int64 _target;
      when' _idx1 == mpidr_to_rec_idx_spec (VZ64 _target) adt;
      rely is_int64 _idx1;
      when' _idx2 == get_rec_rec_idx_spec (_rec_base, _rec_ofst) adt;
      rely is_int64 _idx2;
      if (_idx1 =? _idx2) then
        when'' _g_base, _g_ofst == get_rec_g_rec_spec (_rec_base, _rec_ofst) adt;
        rely is_int _g_ofst;
        when adt == granule_lock_spec (_g_base, _g_ofst) adt;
        when'' _t'4_base, _t'4_ofst, adt == granule_map_spec (_g_base, _g_ofst) 4 adt;
        rely is_int _t'4_ofst;
        when adt == set_target_rec_spec (_t'4_base, _t'4_ofst) adt;
        Some adt
      else
        when'' _g_rd_base, _g_rd_ofst == get_rec_g_rd_spec (_rec_base, _rec_ofst) adt;
        rely is_int _g_rd_ofst;
        when'' _g_rec_list_base, _g_rec_list_ofst == get_rec_g_rec_list_spec (_rec_base, _rec_ofst) adt;
        rely is_int _g_rec_list_ofst;
        when'' _rec_list_base, _rec_list_ofst, adt == granule_map_spec (_g_rec_list_base, _g_rec_list_ofst) 6 adt;
        rely is_int _rec_list_ofst;
        when' _t'8 == mpidr_to_rec_idx_spec (VZ64 _target) adt;
        rely is_int64 _t'8;
        when'' _t'9_base, _t'9_ofst, adt == find_lock_rec_spec (_g_rd_base, _g_rd_ofst) (_rec_list_base, _rec_list_ofst) (VZ64 _t'8) adt;
        rely is_int _t'9_ofst;
        when adt == buffer_unmap_spec (_rec_list_base, _rec_list_ofst) adt;
        when _t'12 == is_null_spec (_t'9_base, _t'9_ofst) adt;
        rely is_int _t'12;
        if (_t'12 =? 1) then
          when'' _t'10_base, _t'10_ofst == null_ptr_spec  adt;
          rely is_int _t'10_ofst;
          when adt == set_target_rec_spec (_t'10_base, _t'10_ofst) adt;
          Some adt
        else
          when'' _t'11_base, _t'11_ofst, adt == granule_map_spec (_t'9_base, _t'9_ofst) 4 adt;
          rely is_int _t'11_ofst;
          when adt == set_target_rec_spec (_t'11_base, _t'11_ofst) adt;
          Some adt
     end
    .

End SpecLow.
