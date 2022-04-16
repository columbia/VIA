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

  Definition psci_lookup_target_spec0 (rec: Pointer) (target: Z64) (adt: RData) : option (RData * Pointer) :=
    match rec, target with
    | (_rec_base, _rec_ofst), VZ64 _target =>
      rely is_int64 _target;
      when _valid == mpidr_is_valid_spec (VZ64 _target) adt;
      rely is_int _valid;
      if (_valid =? 0) then
        when'' _t'2_base, _t'2_ofst == null_ptr_spec  adt;
        rely is_int _t'2_ofst;
        Some (adt, (_t'2_base, _t'2_ofst))
      else
        when'' _g_rd_base, _g_rd_ofst == get_rec_g_rd_spec (_rec_base, _rec_ofst) adt;
        rely is_int _g_rd_ofst;
        when'' _g_rec_list_base, _g_rec_list_ofst == get_rec_g_rec_list_spec (_rec_base, _rec_ofst) adt;
        rely is_int _g_rec_list_ofst;
        when'' _rec_list_base, _rec_list_ofst, adt == granule_map_spec (_g_rec_list_base, _g_rec_list_ofst) 6 adt;
        rely is_int _rec_list_ofst;
        when' _t'6 == mpidr_to_rec_idx_spec (VZ64 _target) adt;
        rely is_int64 _t'6;
        when'' _t'7_base, _t'7_ofst, adt == find_lock_rec_spec (_g_rd_base, _g_rd_ofst) (_rec_list_base, _rec_list_ofst) (VZ64 _t'6) adt;
        rely is_int _t'7_ofst;
        when adt == buffer_unmap_spec (_rec_list_base, _rec_list_ofst) adt;
        Some (adt, (_t'7_base, _t'7_ofst))
     end
    .

End SpecLow.
