Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition get_realm_params_spec (realm_params_addr: Z64) (adt: RData) : option (RData * Z) :=
    match realm_params_addr with
    | VZ64 addr =>
      rely is_int64 addr;
      let gidx := __addr_to_gidx addr in
      if (GRANULE_ALIGNED addr) && (is_gidx gidx) then
        rely prop_dec ((buffer (priv adt)) @ SLOT_NS = None);
        let e := EVT CPU_ID (COPY_NS gidx READ_REALM_PARAMS) in
        let gn := (gs (share adt)) @ gidx in
        if (g_tag (ginfo gn) =? GRANULE_STATE_NS) then
          let ns_data := g_data (gnorm gn) in
          Some (adt {log: e :: (log adt)} {priv: (priv adt) {realm_params: ns_data}}, 0)
        else
          Some (adt {log: e :: (log adt)}, 1)
      else
        Some (adt, 1)
    end.

End Spec.

