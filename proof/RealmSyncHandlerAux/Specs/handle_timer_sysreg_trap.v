Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmTimerHandler.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition handle_timer_sysreg_trap_spec (rec: Pointer) (esr: Z64) (adt: RData) : option RData :=
    match esr with
    | VZ64 esr =>
      rely is_int64 esr;
      let ec := Z.land esr ESR_EL2_SYSREG_MASK in
      if (ec =? ESR_EL2_SYSREG_TIMER_CNTV_TVAL_EL0)
         || (ec =? ESR_EL2_SYSREG_TIMER_CNTV_CTL_EL0)
         || (ec =? ESR_EL2_SYSREG_TIMER_CNTV_CVAL_EL0)
      then
        if __ESR_EL2_SYSREG_IS_WRITE esr then
          handle_vtimer_sysreg_write_spec rec (VZ64 esr) adt
        else
          handle_vtimer_sysreg_read_spec rec (VZ64 esr) adt
      else
        if (ec =? ESR_EL2_SYSREG_TIMER_CNTP_TVAL_EL0)
           || (ec =? ESR_EL2_SYSREG_TIMER_CNTP_CTL_EL0)
           || (ec =? ESR_EL2_SYSREG_TIMER_CNTP_CVAL_EL0)
        then
          if __ESR_EL2_SYSREG_IS_WRITE esr then
            handle_ptimer_sysreg_write_spec rec (VZ64 esr) adt
          else
            handle_ptimer_sysreg_read_spec rec (VZ64 esr) adt
        else
          Some adt
    end.

End Spec.

