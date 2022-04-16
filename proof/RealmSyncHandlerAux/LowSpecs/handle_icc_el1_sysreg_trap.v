Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition handle_icc_el1_sysreg_trap_spec0 (rec: Pointer) (esr: Z64) (adt: RData) : option RData :=
    match rec, esr with
    | (_rec_base, _rec_ofst), VZ64 _esr =>
      rely is_int64 _esr;
      when _rt == ESR_EL2_SYSREG_ISS_RT_spec (VZ64 _esr) adt;
      rely is_int _rt;
      when _t'2 == ESR_EL2_SYSREG_IS_WRITE_spec (VZ64 _esr) adt;
      rely is_int _t'2;
      if (_t'2 =? 0) then
        when adt == set_rec_regs_spec (_rec_base, _rec_ofst) _rt (VZ64 0) adt;
        Some adt
      else
        Some adt
     end
    .

End SpecLow.
