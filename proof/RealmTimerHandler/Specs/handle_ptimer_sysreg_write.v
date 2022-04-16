Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition handle_ptimer_sysreg_write_spec (rec: Pointer) (esr: Z64) (adt: RData) : option RData :=
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
      let val := get_reg rt (g_regs (grec gn)) in
      rely is_int64 val;
      rely is_int (t_masked (g_ptimer (grec gn)));
      rely is_int64 (r_cnthctl_el2 (g_regs (grec gn)));
      let cnth' := Z.lor (r_cnthctl_el2 (g_regs (grec gn))) CNTHCTL_EL2_EL1PTEN in
      let ec := Z.land esr ESR_EL2_SYSREG_MASK in
      if ec =? ESR_EL2_SYSREG_TIMER_CNTP_TVAL_EL0 then
        let cntp_ctl := r_cntp_ctl_el0 (cpu_regs (priv adt)) in
        rely is_int64 cntp_ctl;
        match t_masked (g_ptimer (grec gn)) =? 0, __timer_condition_met cntp_ctl with
        | true, true =>
          Some adt {priv: (priv adt) {cpu_regs: (cpu_regs (priv adt)) {r_cntp_tval_el0: val}}}
        | _, _ =>
          let r' := (grec gn) {g_ptimer: (g_ptimer (grec gn)) {t_asserted: 0}}
                                  {g_regs: (g_regs (grec gn)) {r_cnthctl_el2: cnth'}} in
          Some adt {priv: (priv adt) {cpu_regs: (cpu_regs (priv adt)) {r_cntp_tval_el0: val} {r_cnthctl_el2: cnth'}}}
               {share: (share adt) {gs: (gs (share adt)) # gidx == (gn {grec: r'})}}
        end
      else
        if ec =? ESR_EL2_SYSREG_TIMER_CNTP_CTL_EL0 then
          let masked := Z.land val CNTx_CTL_IMASK in
          let cntp_ctl := Z.lor val CNTx_CTL_IMASK in
          match masked =? 0, __timer_condition_met cntp_ctl with
          | true, true =>
            let r' := (grec gn) {g_ptimer: (g_ptimer (grec gn)) {t_masked: Z.land val CNTx_CTL_IMASK}} in
            Some adt {priv: (priv adt) {cpu_regs: (cpu_regs (priv adt)) {r_cntp_ctl_el0: (Z.lor val CNTx_CTL_IMASK)}}}
                {share: (share adt) {gs: (gs (share adt)) # gidx == (gn {grec: r'})}}
          | _, _=>
            let cnth' := Z.lor (r_cnthctl_el2 (g_regs (grec gn))) CNTHCTL_EL2_EL1PTEN in
            let r' := (grec gn) {g_ptimer: (g_ptimer (grec gn)) {t_asserted: 0} {t_masked: Z.land val CNTx_CTL_IMASK}}
                                {g_regs: (g_regs (grec gn)) {r_cnthctl_el2: cnth'}} in
            Some adt {priv: (priv adt) {cpu_regs: (cpu_regs (priv adt)) {r_cntp_ctl_el0: (Z.lor val CNTx_CTL_IMASK)}
                                                                        {r_cnthctl_el2: cnth'}}}
                {share: (share adt) {gs: (gs (share adt)) # gidx == (gn {grec: r'})}}
          end
        else
          if ec =? ESR_EL2_SYSREG_TIMER_CNTP_CVAL_EL0 then
            let cntp_ctl := r_cntp_ctl_el0 (cpu_regs (priv adt)) in
            rely is_int64 cntp_ctl;
            match t_masked (g_ptimer (grec gn)) =? 0, __timer_condition_met cntp_ctl with
            | true, true =>
              Some adt {priv: (priv adt) {cpu_regs: (cpu_regs (priv adt)) {r_cntp_cval_el0: val}}}
            | _, _ =>
              let r' := (grec gn) {g_ptimer: (g_ptimer (grec gn)) {t_asserted: 0}}
                                      {g_regs: (g_regs (grec gn)) {r_cnthctl_el2: cnth'}} in
              Some adt {priv: (priv adt) {cpu_regs: (cpu_regs (priv adt)) {r_cntp_cval_el0: val} {r_cnthctl_el2: cnth'}}}
                  {share: (share adt) {gs: (gs (share adt)) # gidx == (gn {grec: r'})}}
            end
          else
            let cntp_ctl := r_cntp_ctl_el0 (cpu_regs (priv adt)) in
            rely is_int64 cntp_ctl;
            match t_masked (g_ptimer (grec gn)) =? 0, __timer_condition_met cntp_ctl with
            | true, true =>
              Some adt
            | _, _ =>
              let r' := (grec gn) {g_ptimer: (g_ptimer (grec gn)) {t_asserted: 0}}
                                      {g_regs: (g_regs (grec gn)) {r_cnthctl_el2: cnth'}} in
              Some adt {priv: (priv adt) {cpu_regs: (cpu_regs (priv adt)) {r_cnthctl_el2: cnth'}}}
                  {share: (share adt) {gs: (gs (share adt)) # gidx == (gn {grec: r'})}}
            end
    end.

End Spec.

