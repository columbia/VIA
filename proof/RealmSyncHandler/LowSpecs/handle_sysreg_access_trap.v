Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmSyncHandlerAux.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition handle_sysreg_access_trap_spec0 (rec: Pointer) (esr: Z64) (adt: RData) : option RData :=
    match rec, esr with
    | (_rec_base, _rec_ofst), VZ64 _esr =>
      rely is_int64 (Z.land _esr 4227858432);
      rely is_int (Z.land _esr 4227858432);
      when adt == assert_cond_spec (Z.land _esr 4227858432) adt;
      rely is_int64 (Z.land _esr 3275776);
      if ((Z.land _esr 3275776) =? 3145728) then
        rely is_int64 _esr;
        when adt == handle_id_sysreg_trap_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
        Some adt
      else
        rely is_int64 (Z.land _esr 3210264);
        if ((Z.land _esr 3210264) =? 3209216) then
          rely is_int64 _esr;
          when adt == handle_timer_sysreg_trap_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
          Some adt
        else
          rely is_int64 (Z.land _esr 3210256);
          if ((Z.land _esr 3210256) =? 3158032) then
            rely is_int64 _esr;
            when adt == handle_icc_el1_sysreg_trap_spec (_rec_base, _rec_ofst) (VZ64 _esr) adt;
            Some adt
          else
            Some adt
     end
    .

End SpecLow.
