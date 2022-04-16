Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import BaremoreSMC.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition granule_undelegate_ops_spec (g: Pointer) (addr: Z64) (adt: RData) : option RData :=
    match addr with
    | VZ64 addr =>
      let gidx := offset g in
      rely is_int64 addr;
      rely (peq (base g) ginfo_loc);
      rely (gidx =? __addr_to_gidx addr);
      rely is_gidx gidx;
      rely Z.land (r_scr_el3 (cpu_regs (priv adt))) SCR_WORLD_MASK =? SCR_REALM_WORLD;
      when adt == query_oracle adt;
      let gn := (gs (share adt)) @ gidx in
      rely prop_dec (glock gn = Some CPU_ID);
      rely prop_dec (gtype gn = GRANULE_STATE_DELEGATED);
      rely prop_dec ((gpt_lk (share adt)) @ gidx = None);
      rely prop_dec ((gpt (share adt)) @ gidx = true);
      let e := EVT CPU_ID (ACQ_GPT gidx) in
      let e1 := EVT CPU_ID (REL_GPT gidx false) in
      let g' := gn {ginfo: (ginfo gn) {g_tag: GRANULE_STATE_NS}} in
      let regs' := (cpu_regs (priv adt)) {r_x0: 0} {r_x1: addr} {r_esr_el3: ESR_EC_SMC} in
      let e' := EVT CPU_ID (REL gidx g') in
      Some adt {log: e' :: e1 :: e :: (log adt)}
           {share: (share adt) {gs: (gs (share adt)) # gidx == (g' {gtype: GRANULE_STATE_NS} {glock: None})}
                               {gpt: (gpt (share adt)) # gidx == false}}
           {priv: (priv adt) {cpu_regs: regs'}}
    end.

End Spec.
