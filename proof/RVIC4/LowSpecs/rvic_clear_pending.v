Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RVIC2.Spec.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition rvic_clear_pending_spec0 (rvic: Pointer) (intid: Z64) (adt: RData) : option RData :=
    match rvic, intid with
    | (_rvic_base, _rvic_ofst), VZ64 _intid =>
      when'' _t'1_base, _t'1_ofst == get_rvic_pending_bits_spec (_rvic_base, _rvic_ofst) adt;
      rely is_int _t'1_ofst;
      rely is_int64 _intid;
      when adt == rvic_clear_flag_spec (VZ64 _intid) (_t'1_base, _t'1_ofst) adt;
      Some adt
     end
    .

End SpecLow.
