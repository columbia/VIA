Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmSyncHandlerAux.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition handle_data_abort_spec0 (rec: Pointer) (esr: Z64) (adt: RData) : option RData :=
    match rec, esr with
    | (_rec_base, _rec_ofst), VZ64 _esr =>
      let _far := 0 in
      when' _hpfar == sysreg_read_spec 85 adt;
      rely is_int64 _hpfar;
      let _write_val := 0 in
      when' _spsr == sysreg_read_spec 94 adt;
      rely is_int64 _spsr;
      rely is_int64 (Z.land _spsr 16);
      if (negb ((Z.land _spsr 16) =? 0)) then
        rely is_int64 (Z.land _esr 18446744073692774399);
        let _esr := (Z.land _esr 18446744073692774399) in
        rely is_int64 (Z.land _esr 16777216);
        if ((Z.land _esr 16777216) =? 0) then
          let _t'6 := 1 in
          rely is_int64 (Z.lor 4227858432 63);
          rely is_int64 (Z.land _esr (Z.lor 4227858432 63));
          let _esr := (Z.land _esr (Z.lor 4227858432 63)) in
          rely is_int64 _esr;
          when adt == set_rec_run_esr_spec (VZ64 _esr) adt;
          rely is_int64 _far;
          when adt == set_rec_run_far_spec (VZ64 _far) adt;
          when adt == set_rec_run_hpfar_spec (VZ64 _hpfar) adt;
          rely is_int64 _write_val;
          when adt == set_rec_run_emulated_write_val_spec (VZ64 _write_val) adt;
          Some adt
        else
          rely is_int64 _esr;
          when _t'7 == access_in_par_spec (_rec_base, _rec_ofst) (VZ64 _hpfar) (VZ64 _esr) adt;
          rely is_int _t'7;
          let _t'6 := (_t'7 =? 0) in
          if _t'6 then
            rely is_int64 (Z.lor 4227858432 63);
            rely is_int64 (Z.land _esr (Z.lor 4227858432 63));
            let _esr := (Z.land _esr (Z.lor 4227858432 63)) in
            when adt == set_rec_run_esr_spec (VZ64 _esr) adt;
            rely is_int64 _far;
            when adt == set_rec_run_far_spec (VZ64 _far) adt;
            when adt == set_rec_run_hpfar_spec (VZ64 _hpfar) adt;
            rely is_int64 _write_val;
            when adt == set_rec_run_emulated_write_val_spec (VZ64 _write_val) adt;
            Some adt
          else
            when adt == set_rec_last_run_info_esr_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
            when _t'4 == esr_is_write_spec (VZ64 _esr) adt;
            rely is_int _t'4;
            if (_t'4 =? 1) then
              when' _write_val == get_write_value_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
              rely is_int64 _write_val;
              when' _t'5 == sysreg_read_spec 83 adt;
              rely is_int64 _t'5;
              rely is_int64 (Z.land _t'5 4095);
              let _far := (Z.land _t'5 4095) in
              rely is_int64 (Z.land _esr 4095);
              let _esr := (Z.land _esr 4095) in
              when adt == set_rec_run_esr_spec (VZ64 _esr) adt;
              rely is_int64 _far;
              when adt == set_rec_run_far_spec (VZ64 _far) adt;
              when adt == set_rec_run_hpfar_spec (VZ64 _hpfar) adt;
              when adt == set_rec_run_emulated_write_val_spec (VZ64 _write_val) adt;
              Some adt
            else
              when' _t'5 == sysreg_read_spec 83 adt;
              rely is_int64 _t'5;
              rely is_int64 (Z.land _t'5 4095);
              let _far := (Z.land _t'5 4095) in
              rely is_int64 (Z.land _esr 4095);
              let _esr := (Z.land _esr 4095) in
              when adt == set_rec_run_esr_spec (VZ64 _esr) adt;
              rely is_int64 _far;
              when adt == set_rec_run_far_spec (VZ64 _far) adt;
              when adt == set_rec_run_hpfar_spec (VZ64 _hpfar) adt;
              rely is_int64 _write_val;
              when adt == set_rec_run_emulated_write_val_spec (VZ64 _write_val) adt;
              Some adt
      else
        rely is_int64 (Z.land _esr 16777216);
        if ((Z.land _esr 16777216) =? 0) then
          let _t'6 := 1 in
          rely is_int64 (Z.lor 4227858432 63);
          rely is_int64 (Z.land _esr (Z.lor 4227858432 63));
          let _esr := (Z.land _esr (Z.lor 4227858432 63)) in
          rely is_int64 _esr;
          when adt == set_rec_run_esr_spec (VZ64 _esr) adt;
          rely is_int64 _far;
          when adt == set_rec_run_far_spec (VZ64 _far) adt;
          when adt == set_rec_run_hpfar_spec (VZ64 _hpfar) adt;
          rely is_int64 _write_val;
          when adt == set_rec_run_emulated_write_val_spec (VZ64 _write_val) adt;
          Some adt
        else
          rely is_int64 _esr;
          when _t'7 == access_in_par_spec (_rec_base, _rec_ofst) (VZ64 _hpfar) (VZ64 _esr) adt;
          rely is_int _t'7;
          let _t'6 := (_t'7 =? 0) in
          if _t'6 then
            rely is_int64 (Z.lor 4227858432 63);
            rely is_int64 (Z.land _esr (Z.lor 4227858432 63));
            let _esr := (Z.land _esr (Z.lor 4227858432 63)) in
            when adt == set_rec_run_esr_spec (VZ64 _esr) adt;
            rely is_int64 _far;
            when adt == set_rec_run_far_spec (VZ64 _far) adt;
            when adt == set_rec_run_hpfar_spec (VZ64 _hpfar) adt;
            rely is_int64 _write_val;
            when adt == set_rec_run_emulated_write_val_spec (VZ64 _write_val) adt;
            Some adt
          else
            when adt == set_rec_last_run_info_esr_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
            when _t'4 == esr_is_write_spec (VZ64 _esr) adt;
            rely is_int _t'4;
            if (_t'4 =? 1) then
              when' _write_val == get_write_value_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
              rely is_int64 _write_val;
              when' _t'5 == sysreg_read_spec 83 adt;
              rely is_int64 _t'5;
              rely is_int64 (Z.land _t'5 4095);
              let _far := (Z.land _t'5 4095) in
              rely is_int64 (Z.land _esr 4095);
              let _esr := (Z.land _esr 4095) in
              when adt == set_rec_run_esr_spec (VZ64 _esr) adt;
              rely is_int64 _far;
              when adt == set_rec_run_far_spec (VZ64 _far) adt;
              when adt == set_rec_run_hpfar_spec (VZ64 _hpfar) adt;
              when adt == set_rec_run_emulated_write_val_spec (VZ64 _write_val) adt;
              Some adt
            else
              when' _t'5 == sysreg_read_spec 83 adt;
              rely is_int64 _t'5;
              rely is_int64 (Z.land _t'5 4095);
              let _far := (Z.land _t'5 4095) in
              rely is_int64 (Z.land _esr 4095);
              let _esr := (Z.land _esr 4095) in
              when adt == set_rec_run_esr_spec (VZ64 _esr) adt;
              rely is_int64 _far;
              when adt == set_rec_run_far_spec (VZ64 _far) adt;
              when adt == set_rec_run_hpfar_spec (VZ64 _hpfar) adt;
              rely is_int64 _write_val;
              when adt == set_rec_run_emulated_write_val_spec (VZ64 _write_val) adt;
              Some adt
     end
    .

End SpecLow.
