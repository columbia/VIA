Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiAux2.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition rec_create_ops_spec0 (g_rd: Pointer) (g_rec: Pointer) (rd: Pointer) (rec_list: Pointer) (rec: Pointer) (mpidr: Z64) (rec_idx: Z64) (adt: RData) : option RData :=
    match g_rd, g_rec, rd, rec_list, rec, mpidr, rec_idx with
    | (_g_rd_base, _g_rd_ofst), (_g_rec_base, _g_rec_ofst), (_rd_base, _rd_ofst), (_rec_list_base, _rec_list_ofst), (_rec_base, _rec_ofst), VZ64 _mpidr, VZ64 _rec_idx =>
      when adt == granule_set_state_spec (_g_rec_base, _g_rec_ofst) 3 adt;
      rely is_int64 _rec_idx;
      when adt == realm_set_rec_entry_spec (VZ64 _rec_idx) (_rec_list_base, _rec_list_ofst) (_g_rec_base, _g_rec_ofst) adt;
      when adt == init_rec_read_only_spec (_rec_base, _rec_ofst) (_g_rec_base, _g_rec_ofst) (VZ64 _rec_idx) adt;
      rely is_int64 _mpidr;
      when adt == init_rec_regs_spec (_rec_base, _rec_ofst) (VZ64 _mpidr) (_rd_base, _rd_ofst) adt;
      when'' _t'1_base, _t'1_ofst == get_rec_rvic_spec (_rec_base, _rec_ofst) adt;
      rely is_int _t'1_ofst;
      when adt == init_rec_rvic_state_spec (_t'1_base, _t'1_ofst) adt;
      when' _t'2 == get_rd_par_base_spec (_rd_base, _rd_ofst) adt;
      rely is_int64 _t'2;
      when adt == set_rec_par_base_spec (_rec_base, _rec_ofst) (VZ64 _t'2) adt;
      when' _t'3 == get_rd_par_end_spec (_rd_base, _rd_ofst) adt;
      rely is_int64 _t'3;
      when adt == set_rec_par_end_spec (_rec_base, _rec_ofst) (VZ64 _t'3) adt;
      when adt == set_rec_g_rd_spec (_rec_base, _rec_ofst) (_g_rd_base, _g_rd_ofst) adt;
      when'' _t'4_base, _t'4_ofst == get_rd_g_rec_list_spec (_rd_base, _rd_ofst) adt;
      rely is_int _t'4_ofst;
      when adt == set_rec_g_rec_list_spec (_rec_base, _rec_ofst) (_t'4_base, _t'4_ofst) adt;
      when adt == rec_granule_measure_spec (_rd_base, _rd_ofst) (_rec_base, _rec_ofst) (VZ64 4096) adt;
      when adt == set_g_rec_rd_spec (_g_rec_base, _g_rec_ofst) (_g_rd_base, _g_rd_ofst) adt;
      when adt == atomic_granule_get_spec (_g_rd_base, _g_rd_ofst) adt;
      when' _t'5 == get_rec_params_flags_spec  adt;
      rely is_int64 _t'5;
      rely is_int64 (Z.land _t'5 1);
      rely is_int (Z.land _t'5 1);
      when adt == set_rec_runnable_spec (_rec_base, _rec_ofst) (Z.land _t'5 1) adt;
      Some adt
     end
    .

End SpecLow.
