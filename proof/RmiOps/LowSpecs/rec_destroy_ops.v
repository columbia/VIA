Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition rec_destroy_ops_spec0 (g_rec: Pointer) (adt: RData) : option RData :=
    match g_rec with
    | (_g_rec_base, _g_rec_ofst) =>
      when'' _g_rd_base, _g_rd_ofst == get_g_rec_rd_spec (_g_rec_base, _g_rec_ofst) adt;
      rely is_int _g_rd_ofst;
      when'' _rec_base, _rec_ofst, adt == granule_map_spec (_g_rec_base, _g_rec_ofst) 3 adt;
      rely is_int _rec_ofst;
      when'' _t'3_base, _t'3_ofst == get_rec_g_rec_list_spec (_rec_base, _rec_ofst) adt;
      rely is_int _t'3_ofst;
      when'' _t'4_base, _t'4_ofst, adt == granule_map_spec (_t'3_base, _t'3_ofst) 6 adt;
      rely is_int _t'4_ofst;
      when' _t'5 == get_rec_rec_idx_spec (_rec_base, _rec_ofst) adt;
      rely is_int64 _t'5;
      when'' _t'6_base, _t'6_ofst == null_ptr_spec  adt;
      rely is_int _t'6_ofst;
      when adt == realm_set_rec_entry_spec (VZ64 _t'5) (_t'4_base, _t'4_ofst) (_t'6_base, _t'6_ofst) adt;
      when adt == buffer_unmap_spec (_t'4_base, _t'4_ofst) adt;
      when adt == buffer_unmap_spec (_rec_base, _rec_ofst) adt;
      when'' _t'7_base, _t'7_ofst == null_ptr_spec  adt;
      rely is_int _t'7_ofst;
      when adt == set_g_rec_rd_spec (_g_rec_base, _g_rec_ofst) (_t'7_base, _t'7_ofst) adt;
      when adt == granule_memzero_spec (_g_rec_base, _g_rec_ofst) 3 adt;
      when adt == granule_set_state_spec (_g_rec_base, _g_rec_ofst) 1 adt;
      when adt == granule_unlock_spec (_g_rec_base, _g_rec_ofst) adt;
      when adt == atomic_granule_put_release_spec (_g_rd_base, _g_rd_ofst) adt;
      Some adt
     end
    .

End SpecLow.
