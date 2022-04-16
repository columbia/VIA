Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition handle_ptimer_sysreg_read_spec (rec: Pointer) (esr: Z64) (adt: RData) : option RData :=
    match esr with
    | VZ64 esr =>
      rely is_int64 esr;
      rely (peq (base rec) buffer_loc);
      rely (offset rec =? SLOT_REC);
      when gidx == (buffer (priv adt)) @ (offset rec);
      rely is_gidx gidx;
      let gn := (gs (share adt)) @ gidx in
      rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
      rely (ref_accessible gn CPU_ID);
      let rt := __ESR_EL2_SYSREG_ISS_RT esr in
      rely is_int rt;
      let ec := Z.land esr ESR_EL2_SYSREG_MASK in
      if ec =? ESR_EL2_SYSREG_TIMER_CNTP_TVAL_EL0 then
        rely is_int64 (r_cntp_tval_el0 (cpu_regs (priv adt)));
        let g' := gn {grec: (grec gn) {g_regs: set_reg rt (r_cntp_tval_el0 (cpu_regs (priv adt)))
                                                       (g_regs (grec gn))}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      else
        if ec =? ESR_EL2_SYSREG_TIMER_CNTP_CTL_EL0 then
          rely is_int64 (r_cntp_ctl_el0 (cpu_regs (priv adt)));
          let cntp_ctl := Z.land (r_cntp_ctl_el0 (cpu_regs (priv adt))) NOT_CNTx_CTL_IMASK in
          let val := (if t_masked (g_ptimer (grec gn)) =? 1
                      then (Z.lor cntp_ctl CNTx_CTL_IMASK)
                      else  cntp_ctl) in
          let g' := gn {grec: (grec gn) {g_regs: set_reg rt val (g_regs (grec gn))}} in
          Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
        else
          if ec =? ESR_EL2_SYSREG_TIMER_CNTP_CVAL_EL0 then
            rely is_int64 (r_cntp_cval_el0 (cpu_regs (priv adt)));
            let g' := gn {grec: (grec gn) {g_regs: set_reg rt (r_cntp_cval_el0 (cpu_regs (priv adt)))
                                                          (g_regs (grec gn))}} in
            Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
          else Some adt
    end.

End Spec.

