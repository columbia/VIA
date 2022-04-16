Require Import Coqlib.
Require Import Maps.
Require Import GenSem.

Require Import Constants.
Require Import CommonLib.
Require Import RData.
Require Import EventReplay.
Require Import AbsAccessor.Spec.

Open Local Scope Z_scope.

Definition secure_realm_access_mem (rd_gidx: Z) (rec_gidx: Z) (addr: Z) (val: Z) (st: State) :=
  rely ((MEM0_PHYS <=? addr) && (addr <? 4294967296));
  rely is_int64 val;
  rely is_gidx rd_gidx; rely is_gidx rec_gidx;
  let rec := (gs st) @ rec_gidx in
  rely (gtype rec =? GRANULE_STATE_REC);
  rely (g_rd (ginfo rec) =? rd_gidx);
  rely (gcnt rec =? 1);
  let ipa_gidx := __addr_to_gidx addr in
  let data_gidx := (if tlbs st CPU_ID ipa_gidx =? 0 then
                      match rtts st rd_gidx ipa_gidx with
                      | (g, true) => g
                      | _ => 0
                      end
                    else tlbs st CPU_ID ipa_gidx)
  in
  if data_gidx =? 0
  then Some (st, 0)
  else
    rely is_gidx data_gidx;
    let gn := (gs st) @ data_gidx in
    let ofst := addr mod 4096 in
    let read :=
        match (sec_mem ((realms st) @ rd_gidx)) @ addr with
        | Some z => z
        | _ => (g_data (gnorm gn)) @ ofst
        end
    in
    let realm' := ((realms st) @ rd_gidx) {sec_mem: (sec_mem ((realms st) @ rd_gidx)) # addr == (Some val)} in
    Some (st {realms: (realms st) # rd_gidx == realm'}, read).

Definition secure_realm_access_reg (rd_gidx: Z) (rec_gidx: Z) (reg: Z) (val: Z) (adt: RData) :=
  rely is_int64 val;
  rely ((0 <=? reg) && (reg <=? 30));
  rely is_gidx rd_gidx; rely is_gidx rec_gidx;
  let rec := (gs (share adt)) @ rec_gidx in
  rely (gtype rec =? GRANULE_STATE_REC);
  rely (g_rd (ginfo rec) =? rd_gidx);
  rely (gcnt rec =? 1);
  let realm := (realms (share adt)) @ rd_gidx in
  let read := (if get_reg reg ((decl_regs realm) @ rec_gidx) =? 1 then
                 get_reg reg (cpu_regs (priv adt))
               else get_reg reg ((sec_regs realm) @ rec_gidx))
  in
  let realm' := realm {decl_regs: (decl_regs realm) # rec_gidx == (set_reg reg 0 ((decl_regs realm) @ rec_gidx))}
                      {sec_regs: (sec_regs realm) # rec_gidx == (set_reg reg val ((sec_regs realm) @ rec_gidx))}
  in
  Some (adt {share: (share adt) {realms: (realms (share adt)) # rd_gidx == realm'}}, read).

Definition secure_realm_trap (rd_gidx: Z) (rec_gidx: Z) (t: realm_trap_type) (adt: RData) :=
  rely is_gidx rd_gidx; rely is_gidx rec_gidx;
  let rec := (gs (share adt)) @ rec_gidx in
  rely (gtype rec =? GRANULE_STATE_REC);
  rely (g_rd (ginfo rec) =? rd_gidx);
  rely (gcnt rec =? 1);
  let realm := (realms (share adt)) @ rd_gidx in
  let sec := ((sec_regs realm) @ rec_gidx) in
  let decl := ((decl_regs realm) @ rec_gidx) in
  let cpu := (cpu_regs (priv adt)) in
  let esr := r_esr_el2 (cpu_regs (priv adt)) in
  let adt := adt {priv: (priv adt) {mstage: RMM (REALMTRAP t)}} in
  match t with
  | WFX =>
    rely ((Z.land esr ESR_EL2_EC_MASK) =? ESR_EL2_EC_WFX);
    Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_SYNC_LEL}}
  | HVC =>
    rely ((Z.land esr ESR_EL2_EC_MASK) =? ESR_EL2_EC_HVC);
    let realm' := realm {decl_regs: (decl_regs realm) # rec_gidx == (decl {r_x0: 1} {r_x1: 1}
                                                                          {r_x2: 1} {r_x3: 1}
                                                                          {r_x4: 1} {r_x5: 1}
                                                                          {r_x6: 1} {r_x7: 1})} in
    let cpu' := cpu {r_x0: r_x0 sec} {r_x1: r_x1 sec} {r_x2: r_x2 sec}
                    {r_x3: r_x3 sec} {r_x4: r_x4 sec} {r_x5: r_x5 sec}
                    {r_x6: r_x6 sec} {r_x7: r_x7 sec} in
    Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_SYNC_LEL} {cpu_regs: cpu'}}
         {share: (share adt) {realms: (realms (share adt)) # rd_gidx == realm'}}
  | SMC =>
    rely ((Z.land esr ESR_EL2_EC_MASK) =? ESR_EL2_EC_SMC);
    let realm' := realm {decl_regs: (decl_regs realm) # rec_gidx == (decl {r_x0: 1} {r_x1: 1} {r_x2: 1} {r_x3: 1})} in
    let cpu' := cpu {r_x0: r_x0 sec} {r_x1: r_x1 sec} {r_x2: r_x2 sec} {r_x3: r_x3 sec} in
    Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_SYNC_LEL} {cpu_regs: cpu'}}
         {share: (share adt) {realms: (realms (share adt)) # rd_gidx == realm'}}
  | IDREG =>
    rely ((Z.land esr ESR_EL2_EC_MASK) =? ESR_EL2_EC_SYSREG);
    rely ((Z.land esr ESR_EL2_SYSREG_ID_MASK) =? ESR_EL2_SYSREG_ID);
    let rt := __ESR_EL2_SYSREG_ISS_RT esr in
    let realm' := realm {decl_regs: (decl_regs realm) # rec_gidx == (set_reg rt 1 decl)} in
    let cpu' := set_reg rt (get_reg rt sec) cpu in
    Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_SYNC_LEL} {cpu_regs: cpu'}}
         {share: (share adt) {realms: (realms (share adt)) # rd_gidx == realm'}}
  | TIMER =>
    rely ((Z.land esr ESR_EL2_EC_MASK) =? ESR_EL2_EC_SYSREG);
    rely (negb ((Z.land esr ESR_EL2_SYSREG_ID_MASK) =? ESR_EL2_SYSREG_ID));
    rely ((Z.land esr ESR_EL2_SYSREG_TIMERS_MASK) =? ESR_EL2_SYSREG_TIMERS);
    let rt := __ESR_EL2_SYSREG_ISS_RT esr in
    let realm' := realm {decl_regs: (decl_regs realm) # rec_gidx == (set_reg rt 1 decl)} in
    let cpu' := set_reg rt (get_reg rt sec) cpu in
    Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_SYNC_LEL} {cpu_regs: cpu'}}
         {share: (share adt) {realms: (realms (share adt)) # rd_gidx == realm'}}
  | ICC =>
    rely ((Z.land esr ESR_EL2_EC_MASK) =? ESR_EL2_EC_SYSREG);
    rely (negb ((Z.land esr ESR_EL2_SYSREG_TIMERS_MASK) =? ESR_EL2_SYSREG_TIMERS));
    rely (negb ((Z.land esr ESR_EL2_SYSREG_ID_MASK) =? ESR_EL2_SYSREG_ID));
    rely ((Z.land esr ESR_EL2_SYSREG_ID_MASK) =? ESR_EL2_SYSREG_ID);
    let rt := __ESR_EL2_SYSREG_ISS_RT esr in
    let realm' := realm {decl_regs: (decl_regs realm) # rec_gidx == (set_reg rt 1 decl)} in
    let cpu' := set_reg rt (get_reg rt sec) cpu in
    Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_SYNC_LEL} {cpu_regs: cpu'}}
         {share: (share adt) {realms: (realms (share adt)) # rd_gidx == realm'}}
  | DATA_ABORT =>
    rely ((Z.land esr ESR_EL2_EC_MASK) =? ESR_EL2_EC_DATA_ABORT);
    let rt := __esr_srt esr in
    let realm' := realm {decl_regs: (decl_regs realm) # rec_gidx == (set_reg rt 1 decl)} in
    let cpu' := set_reg rt (get_reg rt sec) cpu in
    Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_SYNC_LEL} {cpu_regs: cpu'}}
         {share: (share adt) {realms: (realms (share adt)) # rd_gidx == realm'}}
  | INSTR_ABORT =>
    rely ((Z.land esr ESR_EL2_EC_MASK) =? ESR_EL2_EC_INST_ABORT);
    Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_SYNC_LEL}}
  | IRQ =>
    Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_IRQ_LEL}}
  | FIQ =>
    Some adt {priv: (priv adt) {trap_reason: ARM_EXCEPTION_FIQ_LEL}}
  end.

Definition secure_user_step_spec (adt: RData) : option (RData * Z64) :=
  match mstage (priv adt), cur_rec (priv adt) with
  | REALM rd_gidx rec_gidx, Some cur_rec_gidx =>
    let rd := (gs (share adt)) @ rd_gidx in
    let rec := (gs (share adt)) @ rec_gidx in
    rely (rd_gidx =? g_rd (ginfo rec));
    rely (rec_gidx =? cur_rec_gidx);
    rely prop_dec (g_running (grec rec) = Some CPU_ID);
    match next_realm_step (log adt) with
    | REALM_ACCESS_MEM' addr val =>
      let e := EVT CPU_ID (REALM_ACCESS_MEM rd_gidx rec_gidx addr val) in
      when ret, st' == secure_realm_access_mem rd_gidx rec_gidx addr val (share adt);
      Some (adt {share: st'} {log: e :: log adt}, VZ64 ret)
    | REALM_ACCESS_REG' reg val =>
      when ret, adt == secure_realm_access_reg rd_gidx rec_gidx reg val adt;
      Some (adt, VZ64 ret)
    | REALM_TRAP' t =>
      when adt == secure_realm_trap rd_gidx rec_gidx t adt;
      Some (adt, VZ64 0)
    end
  | _, _ => user_step_spec adt
  end.
