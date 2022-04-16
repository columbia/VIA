Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition reset_last_run_info_spec0 (rec: Pointer) (adt: RData) : option RData :=
    match rec with
    | (_rec_base, _rec_ofst) =>
      when adt == set_rec_last_run_info_esr_spec (_rec_base, _rec_ofst) (VZ64 0) adt;
      Some adt
     end
    .

End SpecLow.
