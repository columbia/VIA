Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition handle_instruction_abort_spec0 (rec: Pointer) (esr: Z64) (adt: RData) : option (RData * Z) :=
    match rec, esr with
    | (_rec_base, _rec_ofst), VZ64 _esr =>
      rely is_int64 (Z.land _esr 63);
      let _fsc := (Z.land _esr 63) in
      rely is_int64 (Z.land _fsc 18446744073709551612);
      let _fsc_type := (Z.land _fsc 18446744073709551612) in
      when' _hpfar == sysreg_read_spec 85 adt;
      rely is_int64 _hpfar;
      if (_fsc_type =? 12) then
        Some (adt, 0)
      else
        if (negb (_fsc_type =? 4)) then
          Some (adt, 0)
        else
          rely is_int64 (Z.land _hpfar 17592186044400);
          when' _fipa == shiftl_spec (VZ64 (Z.land _hpfar 17592186044400)) (VZ64 8) adt;
          rely is_int64 _fipa;
          when _t'3 == is_addr_in_par_rec_spec (_rec_base, _rec_ofst) (VZ64 _fipa) adt;
          rely is_int _t'3;
          if (_t'3 =? 0) then
            Some (adt, 0)
          else
            when adt == set_rec_run_hpfar_spec (VZ64 _hpfar) adt;
            rely is_int64 (Z.lor 4227858432 63);
            rely is_int64 (Z.land _esr (Z.lor 4227858432 63));
            when adt == set_rec_run_esr_spec (VZ64 (Z.land _esr (Z.lor 4227858432 63))) adt;
            Some (adt, 1)
     end
    .

End SpecLow.
