Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PendingCheckAux.Spec.
Require Import RVIC4.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition check_pending_vtimers_spec (rec: Pointer) (adt: RData) : option RData :=
    let slot := (offset rec) in
    rely (peq (base rec) buffer_loc);
    rely prop_dec (0 <= slot < 16);
    when gidx == (buffer (priv adt)) @ slot;
    let cntv_ctl := r_cntv_ctl_el0 (cpu_regs (priv adt)) in
    rely is_int64 cntv_ctl; rely is_gidx gidx;
    let gn := (gs (share adt)) @ gidx in
    rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
    rely (gtype gn =? GRANULE_STATE_REC);
    rely (g_inited (gro gn));
    rely (ref_accessible gn CPU_ID);
    let cntv_is_masked := (if Z.land cntv_ctl 2 =? 2 then 1 else 0) in
    let vtimer_is_asserted := (t_asserted (g_vtimer (grec gn))) in
    let cntv_condition_met := __timer_condition_met cntv_ctl in
    rely is_int vtimer_is_asserted; rely (g_rec (gro gn) =? gidx);
    if vtimer_is_asserted =? 0 then
      let g' := gn {grec : (grec gn) {g_vtimer : (g_vtimer (grec gn)) {t_masked : cntv_is_masked}}} in
      let adt := adt {share : (share adt) {gs : (gs (share adt)) # gidx == g'}} in
      if (cntv_is_masked =? 0) && cntv_condition_met then
        when adt == query_oracle adt;
        let gn' := (gs (share adt)) @ gidx in
        rely (g_tag (ginfo gn') =? GRANULE_STATE_REC);
        rely (gtype gn' =? GRANULE_STATE_REC);
        rely (ref_accessible gn' CPU_ID);
        rely prop_dec (glock gn' = None);
        let cnthctl := (r_cnthctl_el2 (g_regs (grec gn'))) in
        rely is_int64 cnthctl;
        let idx := INTID_VTIMER_EL1 / 64 in
        let bit := INTID_VTIMER_EL1 mod 64 in
        let bits := (r_pending_bits (g_rvic (gnorm gn'))) @ idx in
        let bits' := Z.lor bits (Z.shiftl 1 bit) in
        let rvic' := (g_rvic (gnorm gn'))
                      {r_pending_bits: (r_pending_bits (g_rvic (gnorm gn'))) # idx == bits'} in
        let r := grec gn' in
        let g' := gn' {gnorm: (gnorm gn') {g_rvic: rvic'}}
                      {grec: r {g_regs: (g_regs r) {r_cnthctl_el2: Z.lor cnthctl CNTHCTL_EL2_EL1TVT}}
                               {g_vtimer: (g_vtimer r) {t_asserted: 1}}} in
        let e := EVT CPU_ID (ACQ gidx) in
        let e' := EVT CPU_ID (REL gidx (g' {glock: Some CPU_ID})) in
        Some adt {log: e' :: e :: log adt}
             {priv: (priv adt) {cpu_regs: (cpu_regs (priv adt))
                                            {r_cntv_ctl_el0: Z.lor cntv_ctl CNTx_CTL_IMASK}
                                            {r_cnthctl_el2: Z.lor cnthctl CNTHCTL_EL2_EL1TVT}}}
            {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      else Some adt
    else Some adt.

End Spec.

