Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition handle_vtimer_sysreg_read_spec0 (rec: Pointer) (esr: Z64) (adt: RData) : option RData :=
    match rec, esr with
    | (_rec_base, _rec_ofst), VZ64 _esr =>
      rely is_int64 _esr;
      when _rt == ESR_EL2_SYSREG_ISS_RT_spec (VZ64 _esr) adt;
      rely is_int _rt;
      rely is_int64 (Z.land _esr 4193310);
      rely is_int (Z.land _esr 4193310);
      let _ec := (Z.land _esr 4193310) in
      if (_ec =? 3209222) then
        when' _t'2 == sysreg_read_spec 37 adt;
        rely is_int64 _t'2;
        when adt == set_rec_regs_spec (_rec_base, _rec_ofst) _rt (VZ64 _t'2) adt;
        Some adt
      else
        if (_ec =? 3340294) then
          when' _cntv_ctl == sysreg_read_spec 35 adt;
          rely is_int64 _cntv_ctl;
          when'' _t'4_base, _t'4_ofst == get_rec_vtimer_spec (_rec_base, _rec_ofst) adt;
          rely is_int _t'4_ofst;
          when' _t'5 == emulate_timer_ctl_read_spec (_t'4_base, _t'4_ofst) (VZ64 _cntv_ctl) adt;
          rely is_int64 _t'5;
          when adt == set_rec_regs_spec (_rec_base, _rec_ofst) _rt (VZ64 _t'5) adt;
          Some adt
        else
          if (_ec =? 3471366) then
            when' _t'6 == sysreg_read_spec 36 adt;
            rely is_int64 _t'6;
            when adt == set_rec_regs_spec (_rec_base, _rec_ofst) _rt (VZ64 _t'6) adt;
            Some adt
          else
            Some adt
     end
    .

End SpecLow.
