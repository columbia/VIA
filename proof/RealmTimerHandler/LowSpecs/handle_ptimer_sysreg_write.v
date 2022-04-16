Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition handle_ptimer_sysreg_write_spec0 (rec: Pointer) (esr: Z64) (adt: RData) : option RData :=
    match rec, esr with
    | (_rec_base, _rec_ofst), VZ64 _esr =>
      rely is_int64 _esr;
      when _rt == ESR_EL2_SYSREG_ISS_RT_spec (VZ64 _esr) adt;
      rely is_int _rt;
      when' _val == get_rec_regs_spec (_rec_base, _rec_ofst) _rt adt;
      rely is_int64 _val;
      rely is_int64 (Z.land _esr 4193310);
      rely is_int (Z.land _esr 4193310);
      let _ec := (Z.land _esr 4193310) in
      if (_ec =? 3209220) then
        when adt == sysreg_write_spec 34 (VZ64 _val) adt;
        when' _cntp_ctl == sysreg_read_spec 32 adt;
        rely is_int64 _cntp_ctl;
        when _t'6 == get_rec_ptimer_masked_spec (_rec_base, _rec_ofst) adt;
        rely is_int _t'6;
        if (negb (_t'6 =? 0)) then
          let _t'7 := 1 in
          when adt == set_rec_ptimer_asserted_spec (_rec_base, _rec_ofst) 0 adt;
          when' _t'4 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 69 adt;
          rely is_int64 _t'4;
          rely is_int64 (Z.lor _t'4 2048);
          when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 69 (VZ64 (Z.lor _t'4 2048)) adt;
          when' _t'5 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 69 adt;
          rely is_int64 _t'5;
          when adt == sysreg_write_spec 69 (VZ64 _t'5) adt;
          Some adt
        else
          when _t'8 == timer_condition_met_spec (VZ64 _cntp_ctl) adt;
          rely is_int _t'8;
          let _t'7 := (_t'8 =? 0) in
          if _t'7 then
            when adt == set_rec_ptimer_asserted_spec (_rec_base, _rec_ofst) 0 adt;
            when' _t'4 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 69 adt;
            rely is_int64 _t'4;
            rely is_int64 (Z.lor _t'4 2048);
            when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 69 (VZ64 (Z.lor _t'4 2048)) adt;
            when' _t'5 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 69 adt;
            rely is_int64 _t'5;
            when adt == sysreg_write_spec 69 (VZ64 _t'5) adt;
            Some adt
          else
            Some adt
      else
        if (_ec =? 3340292) then
          rely is_int64 (Z.land _val 2);
          rely is_int (Z.land _val 2);
          when adt == set_rec_ptimer_masked_spec (_rec_base, _rec_ofst) (Z.land _val 2) adt;
          rely is_int64 (Z.lor _val 2);
          when adt == sysreg_write_spec 32 (VZ64 (Z.lor _val 2)) adt;
          when' _cntp_ctl == sysreg_read_spec 32 adt;
          rely is_int64 _cntp_ctl;
          when _t'6 == get_rec_ptimer_masked_spec (_rec_base, _rec_ofst) adt;
          rely is_int _t'6;
          if (negb (_t'6 =? 0)) then
            let _t'7 := 1 in
            when adt == set_rec_ptimer_asserted_spec (_rec_base, _rec_ofst) 0 adt;
            when' _t'4 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 69 adt;
            rely is_int64 _t'4;
            rely is_int64 (Z.lor _t'4 2048);
            when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 69 (VZ64 (Z.lor _t'4 2048)) adt;
            when' _t'5 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 69 adt;
            rely is_int64 _t'5;
            when adt == sysreg_write_spec 69 (VZ64 _t'5) adt;
            Some adt
          else
            when _t'8 == timer_condition_met_spec (VZ64 _cntp_ctl) adt;
            rely is_int _t'8;
            let _t'7 := (_t'8 =? 0) in
            if _t'7 then
              when adt == set_rec_ptimer_asserted_spec (_rec_base, _rec_ofst) 0 adt;
              when' _t'4 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 69 adt;
              rely is_int64 _t'4;
              rely is_int64 (Z.lor _t'4 2048);
              when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 69 (VZ64 (Z.lor _t'4 2048)) adt;
              when' _t'5 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 69 adt;
              rely is_int64 _t'5;
              when adt == sysreg_write_spec 69 (VZ64 _t'5) adt;
              Some adt
            else
              Some adt
        else
          if (_ec =? 3471364) then
            when adt == sysreg_write_spec 33 (VZ64 _val) adt;
            when' _cntp_ctl == sysreg_read_spec 32 adt;
            rely is_int64 _cntp_ctl;
            when _t'6 == get_rec_ptimer_masked_spec (_rec_base, _rec_ofst) adt;
            rely is_int _t'6;
            if (negb (_t'6 =? 0)) then
              let _t'7 := 1 in
              when adt == set_rec_ptimer_asserted_spec (_rec_base, _rec_ofst) 0 adt;
              when' _t'4 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 69 adt;
              rely is_int64 _t'4;
              rely is_int64 (Z.lor _t'4 2048);
              when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 69 (VZ64 (Z.lor _t'4 2048)) adt;
              when' _t'5 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 69 adt;
              rely is_int64 _t'5;
              when adt == sysreg_write_spec 69 (VZ64 _t'5) adt;
              Some adt
            else
              when _t'8 == timer_condition_met_spec (VZ64 _cntp_ctl) adt;
              rely is_int _t'8;
              let _t'7 := (_t'8 =? 0) in
              if _t'7 then
                when adt == set_rec_ptimer_asserted_spec (_rec_base, _rec_ofst) 0 adt;
                when' _t'4 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 69 adt;
                rely is_int64 _t'4;
                rely is_int64 (Z.lor _t'4 2048);
                when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 69 (VZ64 (Z.lor _t'4 2048)) adt;
                when' _t'5 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 69 adt;
                rely is_int64 _t'5;
                when adt == sysreg_write_spec 69 (VZ64 _t'5) adt;
                Some adt
              else
                Some adt
          else
            when' _cntp_ctl == sysreg_read_spec 32 adt;
            rely is_int64 _cntp_ctl;
            when _t'6 == get_rec_ptimer_masked_spec (_rec_base, _rec_ofst) adt;
            rely is_int _t'6;
            if (negb (_t'6 =? 0)) then
              let _t'7 := 1 in
              when adt == set_rec_ptimer_asserted_spec (_rec_base, _rec_ofst) 0 adt;
              when' _t'4 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 69 adt;
              rely is_int64 _t'4;
              rely is_int64 (Z.lor _t'4 2048);
              when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 69 (VZ64 (Z.lor _t'4 2048)) adt;
              when' _t'5 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 69 adt;
              rely is_int64 _t'5;
              when adt == sysreg_write_spec 69 (VZ64 _t'5) adt;
              Some adt
            else
              when _t'8 == timer_condition_met_spec (VZ64 _cntp_ctl) adt;
              rely is_int _t'8;
              let _t'7 := (_t'8 =? 0) in
              if _t'7 then
                when adt == set_rec_ptimer_asserted_spec (_rec_base, _rec_ofst) 0 adt;
                when' _t'4 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 69 adt;
                rely is_int64 _t'4;
                rely is_int64 (Z.lor _t'4 2048);
                when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 69 (VZ64 (Z.lor _t'4 2048)) adt;
                when' _t'5 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 69 adt;
                rely is_int64 _t'5;
                when adt == sysreg_write_spec 69 (VZ64 _t'5) adt;
                Some adt
              else
                Some adt
     end
    .

End SpecLow.
