Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition data_granule_measure_spec0 (rd: Pointer) (data: Pointer) (offset: Z64) (data_size: Z64) (adt: RData) : option RData :=
    match rd, data, offset, data_size with
    | (_rd_base, _rd_ofst), (_data_base, _data_ofst), VZ64 _offset, VZ64 _data_size =>
      rely is_int64 _offset;
      when adt == measurement_extend_data_header_spec (_rd_base, _rd_ofst) (VZ64 _offset) adt;
      when adt == measurement_extend_data_spec (_rd_base, _rd_ofst) (_data_base, _data_ofst) adt;
      Some adt
     end
    .

End SpecLow.
