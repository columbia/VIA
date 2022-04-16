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

  Definition restore_ns_state_spec0  (adt: RData) : option RData :=
    when adt == restore_ns_state_sysreg_state_spec  adt;
    when' _t'1 == get_ns_state_spec 109 adt;
    rely is_int64 _t'1;
    when adt == sysreg_write_spec 109 (VZ64 _t'1) adt;
    Some adt
    .

End SpecLow.
