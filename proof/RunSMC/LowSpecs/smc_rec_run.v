Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RunComplete.Spec.
Require Import RunAux.Spec.
Require Import RunLoop.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition smc_rec_run_spec0 (rec_addr: Z64) (rec_run_addr: Z64) (adt: RData) : option (RData * Z64) :=
    match rec_addr, rec_run_addr with
    | VZ64 _rec_addr, VZ64 _rec_run_addr =>
      rely is_int64 _rec_run_addr;
      when'' _g_rec_run_base, _g_rec_run_ofst == find_granule_spec (VZ64 _rec_run_addr) adt;
      rely is_int _g_rec_run_ofst;
      when _t'8 == is_null_spec (_g_rec_run_base, _g_rec_run_ofst) adt;
      rely is_int _t'8;
      if (_t'8 =? 1) then
        Some (adt, (VZ64 1))
      else
        rely is_int64 _rec_addr;
        when'' _g_rec_base, _g_rec_ofst, adt == find_lock_unused_granule_spec (VZ64 _rec_addr) (VZ64 3) adt;
        rely is_int _g_rec_ofst;
        when _t'7 == is_null_spec (_g_rec_base, _g_rec_ofst) adt;
        rely is_int _t'7;
        if (_t'7 =? 1) then
          Some (adt, (VZ64 1))
        else
          when adt == atomic_granule_get_spec (_g_rec_base, _g_rec_ofst) adt;
          when adt == granule_unlock_spec (_g_rec_base, _g_rec_ofst) adt;
          when adt == ns_granule_map_spec 0 (_g_rec_run_base, _g_rec_run_ofst) adt;
          when _t'6, adt == ns_buffer_read_rec_run_spec 0 adt;
          rely is_int _t'6;
          if (_t'6 =? 0) then
            when adt == ns_buffer_unmap_spec 0 adt;
            when adt == atomic_granule_put_release_spec (_g_rec_base, _g_rec_ofst) adt;
            Some (adt, (VZ64 1))
          else
            when'' _rec_base, _rec_ofst, adt == granule_map_spec (_g_rec_base, _g_rec_ofst) 3 adt;
            rely is_int _rec_ofst;
            when adt == granule_lock_spec (_g_rec_base, _g_rec_ofst) adt;
            when _t'5 == get_rec_runnable_spec (_rec_base, _rec_ofst) adt;
            rely is_int _t'5;
            if (_t'5 =? 0) then
              when adt == granule_unlock_spec (_g_rec_base, _g_rec_ofst) adt;
              when adt == buffer_unmap_spec (_rec_base, _rec_ofst) adt;
              when adt == ns_buffer_unmap_spec 0 adt;
              when adt == atomic_granule_put_release_spec (_g_rec_base, _g_rec_ofst) adt;
              Some (adt, (VZ64 1))
            else
              when _t'4, adt == complete_mmio_emulation_spec (_rec_base, _rec_ofst) adt;
              rely is_int _t'4;
              if (_t'4 =? 0) then
                when adt == granule_unlock_spec (_g_rec_base, _g_rec_ofst) adt;
                when adt == buffer_unmap_spec (_rec_base, _rec_ofst) adt;
                when adt == ns_buffer_unmap_spec 0 adt;
                when adt == atomic_granule_put_release_spec (_g_rec_base, _g_rec_ofst) adt;
                Some (adt, (VZ64 1))
              else
                when adt == complete_hvc_exit_spec (_rec_base, _rec_ofst) adt;
                when adt == reset_last_run_info_spec (_rec_base, _rec_ofst) adt;
                when adt == reset_disposed_info_spec (_rec_base, _rec_ofst) adt;
                when adt == granule_unlock_spec (_g_rec_base, _g_rec_ofst) adt;
                when adt == rec_run_loop_spec (_rec_base, _rec_ofst) adt;
                Some (adt, (VZ64 2))
     end
    .

End SpecLow.
