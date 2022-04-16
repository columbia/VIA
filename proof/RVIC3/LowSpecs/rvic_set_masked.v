Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RVIC2.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition rvic_set_masked_spec0 (rvic: Pointer) (intid: Z64) (adt: RData) : option RData :=
    match rvic, intid with
    | (_rvic_base, _rvic_ofst), VZ64 _intid =>
      when'' _bits_base, _bits_ofst == get_rvic_mask_bits_spec (_rvic_base, _rvic_ofst) adt;
      rely is_int _bits_ofst;
      rely is_int64 _intid;
      when adt == rvic_set_flag_spec (VZ64 _intid) (_bits_base, _bits_ofst) adt;
      Some adt
     end
    .

End SpecLow.
