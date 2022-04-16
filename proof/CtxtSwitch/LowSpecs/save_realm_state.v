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

  Definition save_realm_state_spec0 (rec: Pointer) (adt: RData) : option RData :=
    match rec with
    | (_rec_base, _rec_ofst) =>
      when adt == save_sysreg_state_spec (_rec_base, _rec_ofst) adt;
      when' _t'1 == sysreg_read_spec 81 adt;
      rely is_int64 _t'1;
      when adt == set_rec_pc_spec (_rec_base, _rec_ofst) (VZ64 _t'1) adt;
      when' _t'2 == sysreg_read_spec 94 adt;
      rely is_int64 _t'2;
      when adt == set_rec_pstate_spec (_rec_base, _rec_ofst) (VZ64 _t'2) adt;
      Some adt
     end
    .

End SpecLow.
