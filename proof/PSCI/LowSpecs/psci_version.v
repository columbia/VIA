Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition psci_version_spec0 (rec: Pointer) (adt: RData) : option RData :=
    match rec with
    | (_rec_base, _rec_ofst) =>
      let _version_1_1 := 65537 in
      rely is_int64 _version_1_1;
      when adt == set_psci_result_x0_spec (VZ64 _version_1_1) adt;
      Some adt
     end
    .

End SpecLow.
