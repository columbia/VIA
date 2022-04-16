Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition realm_ns_step_spec  (adt: RData) : option (RData * Z64) :=
    match mstage (priv adt), cur_rec (priv adt) with
    | REALM rd_gidx rec_gidx, Some cur_rec_gidx =>
      let grd := (gs (share adt)) @ rd_gidx in
      let grec := (gs (share adt)) @ rec_gidx in
      rely (g_rd (ginfo grec) =? rd_gidx);
      rely (rec_gidx =? cur_rec_gidx);
      match next_realm_step (log adt) with
      | REALM_ACCESS_MEM' addr val =>
        let e := EVT CPU_ID (REALM_ACCESS_MEM rd_gidx rec_gidx addr val) in
        when ret, st' == repl_realm_access_mem CPU_ID rd_gidx rec_gidx addr val (share adt);
        rely is_int64 ret;
        Some (adt {log: e :: log adt} {share: st'}, VZ64 ret)
      | REALM_ACCESS_REG' reg val =>
        when ret, adt == access_reg reg val adt;
        rely is_int64 ret;
        Some (adt, VZ64 ret)
      | REALM_TRAP' t =>
        when adt == realm_trap rd_gidx rec_gidx t adt;
        Some (adt, VZ64 0)
      end
    | NS, None =>
      match next_ns_step (log adt) with
      | NS_ACCESS_MEM' addr val =>
        let e := EVT CPU_ID (NS_ACCESS_MEM addr val) in
        when ret, st' == repl_ns_access_mem CPU_ID addr val (share adt);
        rely is_int64 ret;
        Some (adt {log: e :: log adt} {share: st'}, VZ64 ret)
      | NS_ACCESS_REG' reg val =>
        when ret, adt == access_reg reg val adt;
        rely is_int64 ret;
        Some (adt, VZ64 ret)
      | NS_TRAP' =>
        when adt == ns_trap adt;
        Some (adt, VZ64 0)
      end
    | _, _ => None
    end.

End Spec.

