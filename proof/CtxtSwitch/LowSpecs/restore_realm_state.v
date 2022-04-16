Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import CtxtSwitchAux.Spec.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition restore_realm_state_spec0 (rec: Pointer) (adt: RData) : option RData :=
    match rec with
    | (_rec_base, _rec_ofst) =>
      when adt == restore_sysreg_state_spec (_rec_base, _rec_ofst) adt;
      when' _t'1 == get_rec_pc_spec (_rec_base, _rec_ofst) adt;
      rely is_int64 _t'1;
      when adt == sysreg_write_spec 81 (VZ64 _t'1) adt;
      when' _t'2 == get_rec_pstate_spec (_rec_base, _rec_ofst) adt;
      rely is_int64 _t'2;
      when adt == sysreg_write_spec 94 (VZ64 _t'2) adt;
      when' _icc == sysreg_read_spec 109 adt;
      rely is_int64 _icc;
      rely is_int64 (Z.land _icc 18446744073709551607);
      when adt == sysreg_write_spec 109 (VZ64 (Z.land _icc 18446744073709551607)) adt;
      Some adt
     end
    .

End SpecLow.
