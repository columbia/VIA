Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PSCIAux.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition psci_cpu_on_target_spec (g_target_rec: Pointer) (target_rec: Pointer) (rec: Pointer) (entry_point_address: Z64) (target_cpu: Z64) (adt: RData) : option RData :=
    match entry_point_address, target_cpu with
    | VZ64 ep, VZ64 tc =>
      rely is_int64 ep; rely is_int64 tc;
      rely (peq (base g_target_rec) ginfo_loc);
      rely (peq (base target_rec) buffer_loc);
      rely (peq (base rec) buffer_loc);
      when rec_gidx == ((buffer (priv adt)) @ (offset rec));
      when target_gidx == ((buffer (priv adt)) @ (offset target_rec));
      rely prop_dec (rec_gidx <> target_gidx);
      rely is_gidx target_gidx;
      rely (offset g_target_rec =? target_gidx);
      let gn_rec := (gs (share adt)) @ rec_gidx in
      let gn := (gs (share adt)) @ target_gidx in
      rely (g_tag (ginfo gn_rec) =? GRANULE_STATE_REC);
      rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
      rely prop_dec (glock gn = Some CPU_ID);
      rely (ref_accessible gn CPU_ID);
      rely (ref_accessible gn_rec CPU_ID);
      rely is_int (g_runnable (gnorm gn));
      if g_runnable (gnorm gn) =? 0 then
        let sctlr := r_sctlr_el1 (g_regs (grec gn_rec)) in
        rely is_int64 sctlr;
        let g' := gn {grec : (grec gn) {g_pstate : 965}
                                       {g_pc: ep}
                                       {g_regs : set_reg sctlr_el1 (Z.lor SCTLR_EL1_FLAGS (Z.land sctlr SCTLR_EL1_EE)) (g_regs (grec gn))}}
                     {gnorm: (gnorm gn) {g_runnable: 1}} in
        rely (g_tag (ginfo gn) =? gtype gn);
        let e := EVT CPU_ID (REL target_gidx g') in
        Some adt {log: e :: log adt}
             {priv: (priv adt) {buffer: (buffer (priv adt)) # (offset target_rec) == None} {psci_x0: 0}
                               {psci_forward_psci_call: 1} {psci_forward_x1: tc}}
             {share: (share adt) {gs: (gs (share adt)) # target_gidx == (g' {glock: None})}}
      else
        rely (g_tag (ginfo gn) =? gtype gn);
        let e := EVT CPU_ID (REL target_gidx gn) in
        Some adt {log: e :: log adt}
             {priv: (priv adt) {buffer: (buffer (priv adt)) # (offset target_rec) == None} {psci_x0: PSCI_RETURN_ALREADY_ON}}
             {share: (share adt) {gs: (gs (share adt)) # target_gidx == (gn {glock: None})}}
     end.

End Spec.

