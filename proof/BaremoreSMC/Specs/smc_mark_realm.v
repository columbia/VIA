Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import BaremoreHandler.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition smc_mark_realm_spec (addr: Z64) (adt: RData) : option RData :=
    match addr with
    | VZ64 addr =>
      rely is_int64 addr;
      rely (Z.land (r_scr_el3 (cpu_regs (priv adt))) SCR_WORLD_MASK =? SCR_REALM_WORLD);
      let gidx := __addr_to_gidx addr in
      rely is_gidx gidx;
      when adt == query_oracle adt;
      rely prop_dec ((gpt_lk (share adt)) @ gidx = None);
      rely prop_dec ((gpt (share adt)) @ gidx = false);
      let e := EVT CPU_ID (ACQ_GPT gidx) in
      let e' := EVT CPU_ID (REL_GPT gidx true) in
      Some adt {log: e' :: e :: (log adt)} {share: (share adt) {gpt: (gpt (share adt)) # gidx == true}}
           {priv: (priv adt) {cpu_regs: (cpu_regs (priv adt)) {r_x0: 0} {r_x1: addr} {r_esr_el3: ESR_EC_SMC}}}
    end.

End Spec.

