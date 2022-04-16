Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PSCIAux2.Spec.
Require Import PSCIAux.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition psci_cpu_on_spec (rec: Pointer) (target_cpu: Z64) (entry_point_address: Z64) (context_id: Z64) (adt: RData) : option RData :=
    match target_cpu, entry_point_address, context_id with
    | VZ64 tc, VZ64 ep, VZ64 cid =>
      rely is_int64 tc; rely is_int64 ep;
      rely (peq (base rec) buffer_loc);
      rely (offset rec =? SLOT_REC);
      when rec_gidx == ((buffer (priv adt)) @ (offset rec));
      rely is_gidx rec_gidx;
      let gn := (gs (share adt)) @ rec_gidx in
      rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
      rely (gtype gn =? GRANULE_STATE_REC);
      rely (ref_accessible gn CPU_ID);
      rely (g_inited (gro gn));
      let par_base := g_rec_par_base (grec gn) in
      let par_end := g_rec_par_end (grec gn) in
      rely is_int64 par_base; rely is_int64 par_end;
      if (ep <? par_base) || (ep >=? par_end) then
        Some adt {priv: (priv adt) {psci_x0: PSCI_RETURN_INVALID_ADDRESS}}
      else
        let idx1 := __mpidr_to_rec_idx tc in
        let idx2 := g_rec_idx (gro gn) in
        rely is_int idx1; rely is_int idx2;
        if idx1 =? idx2 then
          Some adt {priv: (priv adt) {psci_x0: PSCI_RETURN_ALREADY_ON}}
        else
          when'' target_base, target_offset, adt == psci_lookup_target_spec rec (VZ64 tc) adt;
          if ptr_eq (target_base, target_offset) NULL then
            Some adt {priv: (priv adt) {psci_x0: PSCI_RETURN_INVALID_PARAMS}}
          else
            rely prop_dec ((buffer (priv adt)) @ SLOT_REC_TARGET = None);
            rely (peq target_base ginfo_loc);
            let target_gidx := target_offset in
            rely prop_dec (rec_gidx <> target_gidx);
            rely is_gidx target_gidx;
            let gn_rec := (gs (share adt)) @ rec_gidx in
            let gn := (gs (share adt)) @ target_gidx in
            rely (g_tag (ginfo gn_rec) =? GRANULE_STATE_REC);
            rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
            rely (gtype gn =? GRANULE_STATE_REC);
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

              let e := EVT CPU_ID (REL target_gidx g') in
              Some adt {log: e :: log adt} {priv: (priv adt) {psci_x0: 0} {psci_forward_psci_call: 1} {psci_forward_x1: tc}}
                  {share: (share adt) {gs: (gs (share adt)) # target_gidx == (g' {glock: None})}}
            else
              let e := EVT CPU_ID (REL target_gidx gn) in
              Some adt {log: e :: log adt} {priv: (priv adt) {psci_x0: PSCI_RETURN_ALREADY_ON}}
                  {share: (share adt) {gs: (gs (share adt)) # target_gidx == (gn {glock: None})}}
    end.

End Spec.

