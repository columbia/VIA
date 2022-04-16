Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition handle_excpetion_irq_lel_spec0 (rec: Pointer) (adt: RData) : option (RData * Z) :=
    match rec with
    | (_rec_base, _rec_ofst) =>
      when' _icc_hppir1_el1 == sysreg_read_spec 110 adt;
      rely is_int64 _icc_hppir1_el1;
      rely is_int64 (Z.land _icc_hppir1_el1 16777215);
      let _intid := (Z.land _icc_hppir1_el1 16777215) in
      if (_intid =? 27) then
        let _t'2 := 1 in
        Some (adt, 1)
      else
        let _t'2 := (_intid =? 30) in
        if _t'2 then
          Some (adt, 1)
        else
          when adt == set_rec_run_exit_reason_spec (VZ64 1) adt;
          Some (adt, 0)
     end
    .

End SpecLow.
