Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiAux.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition realm_create_ops_spec0  (adt: RData) : option RData :=
    when'' _g_rd_base, _g_rd_ofst == get_locked_granule_spec 0 adt;
    rely is_int _g_rd_ofst;
    when'' _g_rtt_base, _g_rtt_ofst == get_locked_granule_spec 1 adt;
    rely is_int _g_rtt_ofst;
    when'' _g_rec_list_base, _g_rec_list_ofst == get_locked_granule_spec 2 adt;
    rely is_int _g_rec_list_ofst;
    when adt == set_g_rtt_rd_spec (_g_rtt_base, _g_rtt_ofst) (_g_rd_base, _g_rd_ofst) adt;
    when adt == granule_set_state_spec (_g_rtt_base, _g_rtt_ofst) 5 adt;
    when adt == granule_unlock_spec (_g_rtt_base, _g_rtt_ofst) adt;
    when adt == granule_set_state_spec (_g_rec_list_base, _g_rec_list_ofst) 6 adt;
    when adt == granule_unlock_spec (_g_rec_list_base, _g_rec_list_ofst) adt;
    when'' _rd_base, _rd_ofst, adt == granule_map_spec (_g_rd_base, _g_rd_ofst) 2 adt;
    rely is_int _rd_ofst;
    when adt == granule_set_state_spec (_g_rd_base, _g_rd_ofst) 2 adt;
    when adt == set_rd_state_spec (_rd_base, _rd_ofst) 0 adt;
    when' _base == get_realm_params_par_base_spec  adt;
    rely is_int64 _base;
    when' _size == get_realm_params_par_size_spec  adt;
    rely is_int64 _size;
    when adt == set_rd_par_base_spec (_rd_base, _rd_ofst) (VZ64 _base) adt;
    rely is_int64 (_base + _size);
    when adt == set_rd_par_end_spec (_rd_base, _rd_ofst) (VZ64 (_base + _size)) adt;
    when adt == set_rd_g_rtt_spec (_rd_base, _rd_ofst) (_g_rtt_base, _g_rtt_ofst) adt;
    when adt == set_rd_g_rec_list_spec (_rd_base, _rd_ofst) (_g_rec_list_base, _g_rec_list_ofst) adt;
    when' _algo == get_realm_params_measurement_algo_spec  adt;
    rely is_int64 _algo;
    if (_algo =? 1) then
      when adt == set_rd_measurement_algo_spec (_rd_base, _rd_ofst) (VZ64 _algo) adt;
      when adt == measurement_start_spec (_rd_base, _rd_ofst) adt;
      when adt == buffer_unmap_spec (_rd_base, _rd_ofst) adt;
      when adt == granule_unlock_spec (_g_rd_base, _g_rd_ofst) adt;
      Some adt
    else
      when adt == set_rd_measurement_algo_spec (_rd_base, _rd_ofst) (VZ64 0) adt;
      when adt == measurement_start_spec (_rd_base, _rd_ofst) adt;
      when adt == buffer_unmap_spec (_rd_base, _rd_ofst) adt;
      when adt == granule_unlock_spec (_g_rd_base, _g_rd_ofst) adt;
      Some adt
    .

End SpecLow.
