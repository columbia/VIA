Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition rec_granule_measure_spec0 (rd: Pointer) (rec: Pointer) (data_size: Z64) (adt: RData) : option RData :=
    match rd, rec, data_size with
    | (_rd_base, _rd_ofst), (_rec_base, _rec_ofst), VZ64 _data_size =>
      when adt == measurement_extend_rec_header_spec (_rd_base, _rd_ofst) (_rec_base, _rec_ofst) adt;
      when adt == measurement_extend_rec_regs_spec (_rd_base, _rd_ofst) (_rec_base, _rec_ofst) adt;
      when adt == measurement_extend_rec_pstate_spec (_rd_base, _rd_ofst) (_rec_base, _rec_ofst) adt;
      when adt == measurement_extend_rec_sysregs_spec (_rd_base, _rd_ofst) (_rec_base, _rec_ofst) adt;
      Some adt
     end
    .

End SpecLow.
