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

  Definition smc_realm_activate_spec (rd_addr: Z64) (adt: RData) : option (RData * Z64) :=
    match rd_addr with
    | VZ64 addr =>
      rely is_int64 addr;
      rely prop_dec (cur_rec (priv adt) = None);
      let gidx := __addr_to_gidx addr in
      if (GRANULE_ALIGNED addr) && (is_gidx gidx) then
        when adt == query_oracle adt;
        let gn := (gs (share adt)) @ gidx in
        rely prop_dec (glock gn = None);
        let e := EVT CPU_ID (ACQ gidx) in
        if g_tag (ginfo gn) =? GRANULE_STATE_RD then
          rely prop_dec (gtype gn = GRANULE_STATE_RD);
          rely prop_dec ((buffer (priv adt)) @ SLOT_RD = None);
          rely is_int (g_realm_state (gnorm gn));
          if g_realm_state (gnorm gn) =? REALM_STATE_NEW then
            if g_measurement_algo (gnorm gn) =? MEASUREMENT_ALGO_SHA256 then
              if measure_finish (g_measurement_ctx (gnorm gn)) =? 0 then
                let g' := gn {gnorm: (gnorm gn) {g_measurement: 0} {g_realm_state: REALM_STATE_ACTIVE}} in
                let e' := EVT CPU_ID (REL gidx (g' {glock: Some CPU_ID})) in
                Some (adt {log: e' :: e :: log adt}
                          {share: (share adt) {gs: (gs (share adt)) # gidx == g'}},
                      VZ64 0)
              else None
            else
              let g' := gn {gnorm: (gnorm gn) {g_realm_state: REALM_STATE_ACTIVE}} in
              let e' := EVT CPU_ID (REL gidx (g' {glock: Some CPU_ID})) in
              Some (adt {log: e' :: e :: log adt}
                        {share: (share adt) {gs: (gs (share adt)) # gidx == g'}},
                    VZ64 0)
          else
            let e' := EVT CPU_ID (REL gidx (gn {glock: Some CPU_ID})) in
            Some (adt {log: e' :: e :: (log adt)}, VZ64 1)
        else
          let e' := EVT CPU_ID (REL gidx (gn {glock: Some CPU_ID})) in
          Some (adt {log: e' :: e :: (log adt)}, VZ64 1)
      else Some (adt, VZ64 1)
    end.

End Spec.

