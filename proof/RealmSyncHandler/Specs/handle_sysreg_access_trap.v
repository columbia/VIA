Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmSyncHandlerAux.Spec.
Require Import RealmTimerHandler.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition handle_sysreg_access_trap_spec (rec: Pointer) (esr: Z64) (adt: RData) : option RData :=
    match esr with
    | VZ64 esr =>
      rely is_int64 esr;
      rely (peq (base rec) buffer_loc);
      when gidx == (buffer (priv adt)) @ (offset rec);
      let gn := (gs (share adt)) @ gidx in
      rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
      rely (ref_accessible gn CPU_ID);
      if Z.land esr ESR_EL2_IL_MASK =? 0 then None else
      if (Z.land esr ESR_EL2_SYSREG_ID_MASK) =? ESR_EL2_SYSREG_ID then
        let idreg := Z.land esr ESR_EL2_SYSREG_MASK in
        if __ESR_EL2_SYSREG_IS_WRITE esr then None
        else
          let mask := (if idreg =? ESR_EL2_SYSREG_ID_AA64ISAR1_EL1
                      then HANDLE_ID_SYSREG_MASK else 0) in
          let rt := __ESR_EL2_SYSREG_ISS_RT esr in
          rely is_int rt;
          rely is_int64 (get_reg idreg (cpu_regs (priv adt)));
          let val := Z.land (get_reg idreg (cpu_regs (priv adt))) (U64MAX - mask) in
          rely is_int64 val;
          let g' := gn {grec: (grec gn) {g_regs: set_reg rt val (g_regs (grec gn))}} in
          Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      else
        if (Z.land esr ESR_EL2_SYSREG_TIMERS_MASK) =? ESR_EL2_SYSREG_TIMERS then
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
        else
          if (Z.land esr ESR_EL2_SYSREG_ICC_EL1_MASK) =? ESR_EL2_SYSREG_ICC_EL1 then
            let rt := __ESR_EL2_SYSREG_ISS_RT esr in
            rely is_int rt;
            if __ESR_EL2_SYSREG_IS_WRITE esr then
              Some adt
            else
              let g' := gn {grec: (grec gn) {g_regs: set_reg rt 0 (g_regs (grec gn))}} in
              Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
          else Some adt
    end.

End Spec.

