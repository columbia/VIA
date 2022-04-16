Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition validate_realm_params_spec0  (adt: RData) : option Z64 :=
    when' _base == get_realm_params_par_base_spec  adt;
    rely is_int64 _base;
    when' _size == get_realm_params_par_size_spec  adt;
    rely is_int64 _size;
    rely is_int64 (_base mod 4096);
    if ((_base mod 4096) =? 0) then
      rely is_int64 (_size mod 4096);
      let _t'3 := ((_size mod 4096) =? 0) in
      if _t'3 then
        rely is_int64 (_base + _size);
        let _t'4 := ((_base + _size) >? _base) in
        if _t'4 then
          when' _t'6 == max_ipa_size_spec  adt;
          rely is_int64 _t'6;
          let _t'5 := ((_base + _size) <? _t'6) in
          if _t'5 then
            let _ret := 0 in
            Some (VZ64 _ret)
          else
            let _ret := 1 in
            Some (VZ64 _ret)
        else
          let _t'5 := 0 in
          let _ret := 1 in
          Some (VZ64 _ret)
      else
        let _t'4 := 0 in
        let _t'5 := 0 in
        let _ret := 1 in
        Some (VZ64 _ret)
    else
      let _t'3 := 0 in
      let _t'4 := 0 in
      let _t'5 := 0 in
      let _ret := 1 in
      Some (VZ64 _ret)
    .

End SpecLow.
