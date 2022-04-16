Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiOps.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition smc_granule_delegate_spec (addr: Z64) (adt: RData) : option (RData * Z64) :=
    match addr with
    | VZ64 addr =>
      rely Z.land (r_scr_el3 (cpu_regs (priv adt))) SCR_WORLD_MASK =? SCR_REALM_WORLD;
      rely prop_dec ((buffer (priv adt)) @ SLOT_DELEGATED = None);
      rely is_int64 addr;
      rely prop_dec (cur_rec (priv adt) = None);
      let gidx := __addr_to_gidx addr in
      if (GRANULE_ALIGNED addr) && (is_gidx gidx) then
        when adt == query_oracle adt;
        let gn := (gs (share adt)) @ gidx in
        rely prop_dec (glock gn = None);
        rely prop_dec ((gpt_lk (share adt)) @ gidx = None);
        rely prop_dec ((gpt (share adt)) @ gidx = false);
        if g_tag (ginfo gn) =? GRANULE_STATE_NS then
          rely prop_dec (gtype gn = GRANULE_STATE_NS);
          let e := EVT CPU_ID (ACQ gidx) in
          let e1 := EVT CPU_ID (ACQ_GPT gidx) in
          let e2 := EVT CPU_ID (REL_GPT gidx true) in
          let g' := gn {ginfo: (ginfo gn) {g_tag: GRANULE_STATE_DELEGATED}}
                      {gnorm: zero_granule_data_normal}
                      {grec: zero_granule_data_rec}
          in
          let regs' := (cpu_regs (priv adt)) {r_x0: 0} {r_x1: addr} {r_esr_el3: ESR_EC_SMC} in
          let e' := EVT CPU_ID (REL gidx (g' {glock: Some CPU_ID})) in
          Some (adt {log: e' :: e2 :: e1 :: e :: (log adt)}
                    {share: (share adt) {gs: (gs (share adt)) # gidx == (g' {gtype: GRANULE_STATE_DELEGATED})}
                                        {gpt: (gpt (share adt)) # gidx == true}}
                    {priv: (priv adt) {cpu_regs: regs'}},
                VZ64 0)
        else
          let e := EVT CPU_ID (ACQ gidx) in
          let e' := EVT CPU_ID (REL gidx (gn {glock: Some CPU_ID})) in
          Some (adt {log: e' :: e :: (log adt)}, VZ64 1)
      else Some (adt, VZ64 1)
    end.

End Spec.

