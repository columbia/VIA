Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition realm_destroy_ops_spec0 (g_rtt: Pointer) (g_rec_list: Pointer) (g_rd: Pointer) (adt: RData) : option RData :=
    match g_rtt, g_rec_list, g_rd with
    | (_g_rtt_base, _g_rtt_ofst), (_g_rec_list_base, _g_rec_list_ofst), (_g_rd_base, _g_rd_ofst) =>
      when adt == granule_lock_spec (_g_rec_list_base, _g_rec_list_ofst) adt;
      when'' _t'1_base, _t'1_ofst == null_ptr_spec  adt;
      rely is_int _t'1_ofst;
      when adt == set_g_rtt_rd_spec (_g_rtt_base, _g_rtt_ofst) (_t'1_base, _t'1_ofst) adt;
      when adt == granule_memzero_spec (_g_rtt_base, _g_rtt_ofst) 5 adt;
      when adt == granule_set_state_spec (_g_rtt_base, _g_rtt_ofst) 1 adt;
      when adt == granule_unlock_spec (_g_rtt_base, _g_rtt_ofst) adt;
      when adt == granule_memzero_spec (_g_rec_list_base, _g_rec_list_ofst) 6 adt;
      when adt == granule_set_state_spec (_g_rec_list_base, _g_rec_list_ofst) 1 adt;
      when adt == granule_memzero_spec (_g_rd_base, _g_rd_ofst) 2 adt;
      when adt == granule_set_state_spec (_g_rd_base, _g_rd_ofst) 1 adt;
      when adt == granule_unlock_spec (_g_rec_list_base, _g_rec_list_ofst) adt;
      Some adt
     end
    .

End SpecLow.
