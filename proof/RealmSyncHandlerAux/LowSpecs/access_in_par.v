Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition access_in_par_spec0 (rec: Pointer) (address: Z64) (esr: Z64) (adt: RData) : option Z :=
    match rec, address, esr with
    | (_rec_base, _rec_ofst), VZ64 _address, VZ64 _esr =>
      rely is_int64 _esr;
      when _t'1 == access_len_spec (VZ64 _esr) adt;
      rely is_int _t'1;
      when' _t'2 == get_rec_par_base_spec (_rec_base, _rec_ofst) adt;
      rely is_int64 _t'2;
      rely is_int64 (_address + _t'1);
      if ((_address + _t'1) >? _t'2) then
        when' _t'4 == get_rec_par_end_spec (_rec_base, _rec_ofst) adt;
        rely is_int64 _t'4;
        let _t'3 := (_address <? _t'4) in
        if _t'3 then
          Some 1
        else
          Some 0
      else
        let _t'3 := 0 in
        Some 0
     end
    .

End SpecLow.
