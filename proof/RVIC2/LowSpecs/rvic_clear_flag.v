Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition rvic_clear_flag_spec0 (intid: Z64) (bitmap: Pointer) (adt: RData) : option RData :=
    match intid, bitmap with
    | VZ64 _intid, (_bitmap_base, _bitmap_ofst) =>
      rely is_int64 _intid;
      when' _idx == interrupt_bitmap_dword_spec (VZ64 _intid) adt;
      rely is_int64 _idx;
      when' _bit == interrupt_bit_spec (VZ64 _intid) adt;
      rely is_int64 _bit;
      when'' _t'3_base, _t'3_ofst == get_bitmap_loc_spec (_bitmap_base, _bitmap_ofst) (VZ64 _idx) adt;
      rely is_int _t'3_ofst;
      rely is_int _bit;
      when adt == atomic_bit_clear_release_64_spec (_t'3_base, _t'3_ofst) _bit adt;
      Some adt
     end
    .

End SpecLow.
