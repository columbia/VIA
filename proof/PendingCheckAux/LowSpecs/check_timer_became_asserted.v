Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition check_timer_became_asserted_spec0 (timer: Pointer) (cntx_ctl: Z64) (adt: RData) : option (RData * Z) :=
    match timer, cntx_ctl with
    | (_timer_base, _timer_ofst), VZ64 _cntx_ctl =>
      when _t'5 == get_timer_asserted_spec (_timer_base, _timer_ofst) adt;
      rely is_int _t'5;
      if (negb (_t'5 =? 0)) then
        Some (adt, 0)
      else
        rely is_int64 _cntx_ctl;
        when _t'1 == timer_is_masked_spec (VZ64 _cntx_ctl) adt;
        rely is_int _t'1;
        when adt == set_timer_masked_spec (_timer_base, _timer_ofst) _t'1 adt;
        when _t'2 == get_timer_masked_spec (_timer_base, _timer_ofst) adt;
        rely is_int _t'2;
        if (_t'2 =? 0) then
          when _t'4 == timer_condition_met_spec (VZ64 _cntx_ctl) adt;
          rely is_int _t'4;
          let _t'3 := (_t'4 =? 1) in
          if _t'3 then
            Some (adt, 1)
          else
            Some (adt, 0)
        else
          let _t'3 := 0 in
          Some (adt, 0)
     end
    .

End SpecLow.
