Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition restore_hcr_el2_spec0 (rec: Pointer) (adt: RData) : option RData :=
    match rec with
    | (_rec_base, _rec_ofst) =>
      when' _t'1 == get_rec_common_sysregs_spec (_rec_base, _rec_ofst) 75 adt;
      rely is_int64 _t'1;
      when adt == sysreg_write_spec 75 (VZ64 _t'1) adt;
      Some adt
     end
    .

End SpecLow.
