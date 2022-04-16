Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition realm_activate_ops_spec (rd: Pointer) (adt: RData) : option RData :=
    rely (peq (base rd) buffer_loc);
    when gidx == ((buffer (priv adt)) @ (offset rd));
    let gn := (gs (share adt)) @ gidx in
    rely (g_tag (ginfo gn)) =? GRANULE_STATE_RD;
    rely prop_dec (glock gn = Some CPU_ID);
    if g_measurement_algo (gnorm gn) =? MEASUREMENT_ALGO_SHA256 then
      if measure_finish (g_measurement_ctx (gnorm gn)) =? 0 then
        let g' := gn {gnorm: (gnorm gn) {g_measurement: 0} {g_realm_state: REALM_STATE_ACTIVE}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      else None
    else
      let g' := gn {gnorm: (gnorm gn) {g_realm_state: REALM_STATE_ACTIVE}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}.

End Spec.

