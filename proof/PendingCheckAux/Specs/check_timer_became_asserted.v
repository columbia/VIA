Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition check_timer_became_asserted_spec (timer: Pointer) (cntx_ctl: Z64) (adt: RData) : option (RData * Z) :=
    match cntx_ctl with
    | VZ64 cntx_ctl =>
      rely is_int64 cntx_ctl;
      when gidx == (buffer (priv adt)) @ (offset timer);
      let gn := (gs (share adt)) @ gidx in
      rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
      rely (ref_accessible gn CPU_ID);
      let is_masked := (if Z.land cntx_ctl 2 =? 2 then 1 else 0) in
      if peq (base timer) ptimer_loc then
        let asserted := t_asserted (g_ptimer (grec gn)) in
        rely is_int asserted;
        if asserted =? 0 then
          let g' := gn {grec: (grec gn) {g_ptimer: (g_ptimer (grec gn)) {t_masked: is_masked}}} in
          if (is_masked =? 0) && (__timer_condition_met cntx_ctl) then
            Some (adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}, 1)
          else
            Some (adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}, 0)
        else
          Some (adt, 0)
      else
        if peq (base timer) vtimer_loc then
          let asserted := t_asserted (g_vtimer (grec gn)) in
          rely is_int asserted;
          if asserted =? 0 then
            let g' := gn {grec: (grec gn) {g_vtimer: (g_vtimer (grec gn)) {t_masked: is_masked}}} in
            if (is_masked =? 0) && (__timer_condition_met cntx_ctl) then
              Some (adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}, 1)
            else
              Some (adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}, 0)
          else
            Some (adt, 0)
        else None
    end.

End Spec.

