Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition init_rec_sysregs_spec0 (rec: Pointer) (mpidr: Z64) (adt: RData) : option RData :=
    match rec, mpidr with
    | (_rec_base, _rec_ofst), VZ64 _mpidr =>
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 39 (VZ64 64) adt;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 47 (VZ64 12912760) adt;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 65 (VZ64 4096) adt;
      rely is_int64 _mpidr;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 72 (VZ64 _mpidr) adt;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 69 (VZ64 3072) adt;
      Some adt
     end
    .

End SpecLow.
