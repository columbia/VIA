Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition psci_reset_rec_spec0 (rec: Pointer) (target_rec: Pointer) (adt: RData) : option RData :=
    match rec, target_rec with
    | (_rec_base, _rec_ofst), (_target_rec_base, _target_rec_ofst) =>
      when adt == set_rec_pstate_spec (_target_rec_base, _target_rec_ofst) (VZ64 965) adt;
      when adt == set_rec_sysregs_spec (_target_rec_base, _target_rec_ofst) 47 (VZ64 12912760) adt;
      when' _reg == get_rec_sysregs_spec (_rec_base, _rec_ofst) 47 adt;
      rely is_int64 _reg;
      rely is_int64 (Z.land _reg 33554432);
      rely is_int64 (Z.lor 12912760 (Z.land _reg 33554432));
      when adt == set_rec_sysregs_spec (_target_rec_base, _target_rec_ofst) 47 (VZ64 (Z.lor 12912760 (Z.land _reg 33554432))) adt;
      Some adt
     end
    .

End SpecLow.
