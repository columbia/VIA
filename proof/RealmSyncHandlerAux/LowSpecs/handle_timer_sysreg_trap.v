Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmTimerHandler.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition handle_timer_sysreg_trap_spec0 (rec: Pointer) (esr: Z64) (adt: RData) : option RData :=
    match rec, esr with
    | (_rec_base, _rec_ofst), VZ64 _esr =>
      rely is_int64 (Z.land _esr 4193310);
      rely is_int (Z.land _esr 4193310);
      let _ec := (Z.land _esr 4193310) in
      if (_ec =? 3209222) then
        let _t'5 := 1 in
        let _t'6 := 1 in
        rely is_int64 _esr;
        when _t'1 == ESR_EL2_SYSREG_IS_WRITE_spec (VZ64 _esr) adt;
        rely is_int _t'1;
        if (_t'1 =? 1) then
          when adt == handle_vtimer_sysreg_write_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
          Some adt
        else
          when adt == handle_vtimer_sysreg_read_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
          Some adt
      else
        let _t'5 := (_ec =? 3340294) in
        if _t'5 then
          let _t'6 := 1 in
          rely is_int64 _esr;
          when _t'1 == ESR_EL2_SYSREG_IS_WRITE_spec (VZ64 _esr) adt;
          rely is_int _t'1;
          if (_t'1 =? 1) then
            when adt == handle_vtimer_sysreg_write_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
            Some adt
          else
            when adt == handle_vtimer_sysreg_read_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
            Some adt
        else
          let _t'6 := (_ec =? 3471366) in
          if _t'6 then
            rely is_int64 _esr;
            when _t'1 == ESR_EL2_SYSREG_IS_WRITE_spec (VZ64 _esr) adt;
            rely is_int _t'1;
            if (_t'1 =? 1) then
              when adt == handle_vtimer_sysreg_write_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
              Some adt
            else
              when adt == handle_vtimer_sysreg_read_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
              Some adt
          else
            if (_ec =? 3209220) then
              let _t'3 := 1 in
              let _t'4 := 1 in
              rely is_int64 _esr;
              when _t'2 == ESR_EL2_SYSREG_IS_WRITE_spec (VZ64 _esr) adt;
              rely is_int _t'2;
              if (_t'2 =? 1) then
                when adt == handle_ptimer_sysreg_write_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
                Some adt
              else
                when adt == handle_ptimer_sysreg_read_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
                Some adt
            else
              let _t'3 := (_ec =? 3340292) in
              if _t'3 then
                let _t'4 := 1 in
                rely is_int64 _esr;
                when _t'2 == ESR_EL2_SYSREG_IS_WRITE_spec (VZ64 _esr) adt;
                rely is_int _t'2;
                if (_t'2 =? 1) then
                  when adt == handle_ptimer_sysreg_write_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
                  Some adt
                else
                  when adt == handle_ptimer_sysreg_read_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
                  Some adt
              else
                let _t'4 := (_ec =? 3471364) in
                if _t'4 then
                  rely is_int64 _esr;
                  when _t'2 == ESR_EL2_SYSREG_IS_WRITE_spec (VZ64 _esr) adt;
                  rely is_int _t'2;
                  if (_t'2 =? 1) then
                    when adt == handle_ptimer_sysreg_write_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
                    Some adt
                  else
                    when adt == handle_ptimer_sysreg_read_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
                    Some adt
                else
                  Some adt
     end
    .

End SpecLow.
