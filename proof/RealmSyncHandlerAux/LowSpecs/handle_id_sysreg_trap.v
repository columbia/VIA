Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition handle_id_sysreg_trap_spec0 (rec: Pointer) (esr: Z64) (adt: RData) : option RData :=
    match rec, esr with
    | (_rec_base, _rec_ofst), VZ64 _esr =>
      rely is_int64 (Z.land _esr 4193310);
      rely is_int (Z.land _esr 4193310);
      let _idreg := (Z.land _esr 4193310) in
      let _mask := 0 in
      rely is_int64 _esr;
      when _t'1 == ESR_EL2_SYSREG_IS_WRITE_spec (VZ64 _esr) adt;
      rely is_int _t'1;
      rely is_int (1 - _t'1);
      when adt == assert_cond_spec (1 - _t'1) adt;
      if (_idreg =? 3276812) then
        let _mask := 255 in
        when _t'2 == ESR_EL2_SYSREG_ISS_RT_spec (VZ64 _esr) adt;
        rely is_int _t'2;
        rely is_int _idreg;
        when' _t'3 == read_idreg_spec _idreg adt;
        rely is_int64 _t'3;
        rely is_int64 (18446744073709551615 - _mask);
        rely is_int64 (Z.land _t'3 (18446744073709551615 - _mask));
        when adt == set_rec_regs_spec (_rec_base, _rec_ofst) _t'2 (VZ64 (Z.land _t'3 (18446744073709551615 - _mask))) adt;
        Some adt
      else
        when _t'2 == ESR_EL2_SYSREG_ISS_RT_spec (VZ64 _esr) adt;
        rely is_int _t'2;
        rely is_int _idreg;
        when' _t'3 == read_idreg_spec _idreg adt;
        rely is_int64 _t'3;
        rely is_int64 (18446744073709551615 - _mask);
        rely is_int64 (Z.land _t'3 (18446744073709551615 - _mask));
        when adt == set_rec_regs_spec (_rec_base, _rec_ofst) _t'2 (VZ64 (Z.land _t'3 (18446744073709551615 - _mask))) adt;
        Some adt
     end
    .

End SpecLow.
