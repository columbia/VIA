Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PSCIAux2.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition psci_affinity_info_spec (rec: Pointer) (target_affinity: Z64) (lowest_affinity_level: Z64) (adt: RData) : option RData :=
    match target_affinity, lowest_affinity_level with
    | VZ64 target, VZ64 lowest =>
      rely is_int64 target; rely is_int64 lowest;
      if lowest =? 0 then
        when'' target_base, target_offset, adt == psci_lookup_target_spec rec (VZ64 target) adt;
        rely is_int target_offset;
        if ptr_eq (target_base, target_offset) NULL then
          Some adt {priv: (priv adt) {psci_x0: PSCI_RETURN_INVALID_PARAMS}}
        else
          rely (peq target_base ginfo_loc);
          let gidx := target_offset in
          rely is_gidx gidx;
          rely prop_dec ((buffer (priv adt)) @ SLOT_REC_TARGET = None);
          let gn := (gs (share adt)) @ gidx in
          rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
          rely prop_dec (glock gn = Some CPU_ID);
          let e := EVT CPU_ID (REL gidx gn) in
          rely (gtype gn =? g_tag (ginfo gn));
          rely is_int (g_runnable (gnorm gn));
          if g_runnable (gnorm gn) =? 1 then
            Some adt {log: e :: log adt} {priv: (priv adt) {psci_x0: 0}}
                 {share: (share adt) {gs: (gs (share adt)) # gidx == (gn {glock: None})}}
          else
            Some adt {log: e :: log adt} {priv: (priv adt) {psci_x0: 1}}
                 {share: (share adt) {gs: (gs (share adt)) # gidx == (gn {glock: None})}}
      else
        Some adt {priv: (priv adt) {psci_x0: PSCI_RETURN_INVALID_PARAMS}}
    end.

End Spec.
