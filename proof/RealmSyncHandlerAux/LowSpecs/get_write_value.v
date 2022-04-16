Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition get_write_value_spec0 (rec: Pointer) (esr: Z64) (adt: RData) : option Z64 :=
    match rec, esr with
    | (_rec_base, _rec_ofst), VZ64 _esr =>
      rely is_int64 _esr;
      when _rt == esr_srt_spec (VZ64 _esr) adt;
      rely is_int _rt;
      if (_rt =? 31) then
        Some (VZ64 0)
      else
        when' _t'2 == get_rec_regs_spec (_rec_base, _rec_ofst) _rt adt;
        rely is_int64 _t'2;
        when' _t'3 == access_mask_spec (VZ64 _esr) adt;
        rely is_int64 _t'3;
        rely is_int64 (Z.land _t'2 _t'3);
        Some (VZ64 (Z.land _t'2 _t'3))
     end
    .

End SpecLow.
