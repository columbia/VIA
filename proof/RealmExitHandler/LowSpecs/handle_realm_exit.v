Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmExitHandlerAux.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition handle_realm_exit_spec0 (rec: Pointer) (exception: Z) (adt: RData) : option (RData * Z) :=
    match rec, exception with
    | (_rec_base, _rec_ofst), _exception =>
      if (_exception =? 0) then
        when adt == set_rec_run_exit_reason_spec (VZ64 0) adt;
        when _t'1, adt == handle_exception_sync_spec (_rec_base, _rec_ofst) adt;
        rely is_int _t'1;
        Some (adt, _t'1)
      else
        if (_exception =? 1) then
          when _t'2, adt == handle_excpetion_irq_lel_spec (_rec_base, _rec_ofst) adt;
          rely is_int _t'2;
          Some (adt, _t'2)
        else
          if (_exception =? 2) then
            when adt == set_rec_run_exit_reason_spec (VZ64 2) adt;
            Some (adt, 0)
          else
            Some (adt, 0)
     end
    .

End SpecLow.
