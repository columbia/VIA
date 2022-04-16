Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmExitHandlerAux.Spec.
Require Import RealmSyncHandler.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition handle_realm_exit_spec (rec: Pointer) (exception: Z) (adt: RData) : option (RData * Z) :=
    rely (peq (base rec) buffer_loc);
    when gidx == (buffer (priv adt)) @ (offset rec);
    let gn := (gs (share adt)) @ gidx in
    rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
    rely (ref_accessible gn CPU_ID);
    if exception =? ARM_EXCEPTION_SYNC_LEL then
      let adt := adt {priv: (priv adt) {rec_run: (rec_run (priv adt)) # 0 == 0}} in
      let esr := r_esr_el2 (cpu_regs (priv adt)) in
      rely is_int64 esr;
      let ec := Z.land esr ESR_EL2_EC_MASK in
      if ec =? ESR_EL2_EC_WFX then
        let esr := Z.land esr (Z.lor ESR_EL2_EC_MASK ESR_EL2_WFx_TI_BIT) in
        Some (adt {priv: (priv adt) {rec_run: (rec_run (priv adt)) # 1 == esr}}, 0)
      else
        if ec =? ESR_EL2_EC_HVC then
          let info := Z.land esr (Z.lor ESR_EL2_EC_MASK ESR_EL2_xVC_IMM_MASK) in
          let g' := gn {grec: (grec gn) {g_esr: info}} in
          rely regs_is_int64_dec (g_regs (grec gn));
          Some (adt {priv: (priv adt) {rec_run: (rec_run (priv adt))
                                                # 1 == info # 5 == (r_x0 (g_regs (grec gn)))
                                                # 6 == (r_x1 (g_regs (grec gn))) # 7 == (r_x2 (g_regs (grec gn)))
                                                # 8 == (r_x3 (g_regs (grec gn))) # 9 == (r_x4 (g_regs (grec gn)))
                                                # 10 == (r_x5 (g_regs (grec gn))) # 11 == (r_x6 (g_regs (grec gn)))}}
                    {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}, 0)
        else
          if ec =? ESR_EL2_EC_SMC then
            let pc := r_elr_el2 (cpu_regs (priv adt)) in
            rely is_int64 pc; rely is_int64 (pc + 4);
            let adt' := adt {priv: (priv adt) {cpu_regs: (cpu_regs (priv adt)) {r_elr_el2: (pc + 4)}}} in
            when ret, adt == handle_realm_rsi_spec rec adt';
            rely is_int ret;
            Some (adt, ret)
          else
            if ec =? ESR_EL2_EC_SYSREG then
              when adt == handle_sysreg_access_trap_spec rec (VZ64 esr) adt;
              let pc := r_elr_el2 (cpu_regs (priv adt)) in
              rely is_int64 pc; rely is_int64 (pc + 4);
              Some (adt {priv: (priv adt) {cpu_regs: (cpu_regs (priv adt)) {r_elr_el2: (pc + 4)}}}, 1)
            else
              let adt' := adt {priv: (priv adt) {rec_run: (rec_run (priv adt)) # 1 == 0 # 2 == 0 # 3 == 0}} in
              if ec =? ESR_EL2_EC_INST_ABORT then
                let fsc := Z.land esr ESR_EL2_ABORT_FSC_MASK in
                let fsc_type := Z.land fsc NOT_ESR_EL2_ABORT_FSC_LEVEL_MASK in
                let hpfar := r_hpfar_el2 (cpu_regs (priv adt)) in
                rely is_int64 hpfar;
                if fsc_type =? ESR_EL2_ABORT_FSC_PERMISSION_FAULT then
                  Some (adt', 0)
                else
                  if fsc_type =? ESR_EL2_ABORT_FSC_TRANSLATION_FAULT then
                    let fipa := Z.shiftl (Z.land hpfar HPFAR_EL2_FIPA_MASK) HPFAR_EL2_FIPA_OFFSET in
                    rely is_int64 fipa;
                    let par_base := g_rec_par_base (grec gn) in
                    let par_end := g_rec_par_end (grec gn) in
                    rely is_int64 par_base; rely is_int64 par_end;
                    if (par_base <=? fipa) && (fipa <? par_end) then
                      let esr := Z.land esr (Z.lor ESR_EL2_EC_MASK ESR_EL2_ABORT_FSC_MASK) in
                      Some (adt {priv: (priv adt) {rec_run: (rec_run (priv adt)) # 1 == esr # 3 == hpfar}}, 0)
                    else Some (adt', 0)
                  else Some (adt', 0)
              else
                if ec =? ESR_EL2_EC_DATA_ABORT then
                  when adt == handle_data_abort_spec rec (VZ64 esr) adt;
                  Some (adt, 0)
                else Some (adt', 0)
    else
      if exception =? ARM_EXCEPTION_IRQ_LEL then
        let icc_hppir1_el1 := r_icc_hppir1_el1 (cpu_regs (priv adt)) in
        rely is_int64 icc_hppir1_el1;
        let intid := Z.land icc_hppir1_el1 ICC_HPPIR1_EL1_INTID in
        if (intid =? INTID_VTIMER_EL1) || (intid =? INTID_PTIMER_EL1) then
          Some (adt, 1)
        else
          Some (adt {priv: (priv adt) {rec_run: (rec_run (priv adt)) # 0 == EXIT_REASON_IRQ}}, 0)
      else
        if exception =? ARM_EXCEPTION_FIQ_LEL then
          Some (adt {priv: (priv adt) {rec_run: (rec_run (priv adt)) # 0 == EXIT_REASON_FIQ}}, 0)
        else Some (adt, 0).

End Spec.

