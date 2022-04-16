Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmSyncHandler.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Fixpoint  handle_exception_sync_loop0 (n: nat) (i: Z) rec_base rec_ofst adt :=
    match n with
    | O => Some (i, adt)
    | S n' =>
      match handle_exception_sync_loop0 n' i rec_base rec_ofst adt with
      | Some (i, adt) =>
        rely is_int i;
        when' gpr == get_rec_regs_spec (rec_base, rec_ofst) i adt;
        rely is_int64 gpr;
        when adt == set_rec_run_gprs_spec i (VZ64 gpr) adt;
        Some (i + 1, adt)
      | _ => None
      end
    end.

  Definition handle_exception_sync_spec0 (rec: Pointer) (adt: RData) : option (RData * Z) :=
    match rec with
    | (_rec_base, _rec_ofst) =>
      when' _esr == sysreg_read_spec 82 adt;
      rely is_int64 _esr;
      rely is_int64 (Z.land _esr 4227858432);
      let _ec := (Z.land _esr 4227858432) in
      if (_ec =? 67108864) then
        rely is_int64 (Z.lor 4227858432 1);
        rely is_int64 (Z.land _esr (Z.lor 4227858432 1));
        when adt == set_rec_run_esr_spec (VZ64 (Z.land _esr (Z.lor 4227858432 1))) adt;
        Some (adt, 0)
      else
        if (_ec =? 1476395008) then
          let _i := 0 in
          rely is_int64 (Z.lor 4227858432 65535);
          rely is_int64 (Z.land _esr (Z.lor 4227858432 65535));
          let _info := (Z.land _esr (Z.lor 4227858432 65535)) in
          rely is_int64 _info;
          when adt == set_rec_last_run_info_esr_spec (_rec_base, _rec_ofst) (VZ64 _info) adt;
          when adt == set_rec_run_esr_spec (VZ64 _info) adt;
          match handle_exception_sync_loop0 (Z.to_nat 7) 0 _rec_base _rec_ofst adt with
          | Some (i, adt) =>
            rely is_int i;
            Some (adt, 0)
          | _ => None
          end
        else
          if (_ec =? 1543503872) then
            when' _pc == sysreg_read_spec 81 adt;
            rely is_int64 _pc;
            rely is_int64 (_pc + 4);
            when adt == sysreg_write_spec 81 (VZ64 (_pc + 4)) adt;
            when _t'3, adt == handle_realm_rsi_spec (_rec_base, _rec_ofst) adt;
            rely is_int _t'3;
            Some (adt, _t'3)
          else
            if (_ec =? 1610612736) then
              when adt == handle_sysreg_access_trap_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
              when' _pc == sysreg_read_spec 81 adt;
              rely is_int64 _pc;
              rely is_int64 (_pc + 4);
              when adt == sysreg_write_spec 81 (VZ64 (_pc + 4)) adt;
              Some (adt, 1)
            else
              if (_ec =? 2147483648) then
                when _t'5, adt == handle_instruction_abort_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
                rely is_int _t'5;
                if (_t'5 =? 1) then
                  Some (adt, 0)
                else
                  when adt == set_rec_run_esr_spec (VZ64 0) adt;
                  when adt == set_rec_run_far_spec (VZ64 0) adt;
                  when adt == set_rec_run_hpfar_spec (VZ64 0) adt;
                  Some (adt, 0)
              else
                if (_ec =? 2415919104) then
                  when adt == handle_data_abort_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
                  Some (adt, 0)
                else
                  when adt == set_rec_run_esr_spec (VZ64 0) adt;
                  when adt == set_rec_run_far_spec (VZ64 0) adt;
                  when adt == set_rec_run_hpfar_spec (VZ64 0) adt;
                  Some (adt, 0)
     end
    .

End SpecLow.
