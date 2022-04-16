Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PSCIAux.Spec.

Local Open Scope Z_scope.

Section Spec.

  Fixpoint system_off_reboot_loop (n: nat) (i: Z) (rec_gidx: Z) (rd_gidx: Z) (idx: Z) (adt: RData) :=
    match n with
    | O => Some (i, adt)
    | S n' =>
      match system_off_reboot_loop n' i rec_gidx rd_gidx idx adt with
      | Some (i, adt) =>
        if i =? idx then
          Some (i + 1, adt)
        else
          when g_target_rec, adt == find_lock_rec_spec (ginfo_loc, rd_gidx) (buffer_loc, SLOT_REC_LIST) (VZ64 i) adt;
          if ptr_eq g_target_rec NULL then
            Some (i + 1, adt)
          else
            rely prop_dec ((buffer (priv adt)) @ SLOT_REC_TARGET = None);
            rely (peq (base g_target_rec) ginfo_loc);
            let gidx := offset g_target_rec in
            rely is_gidx gidx;
            let gn := (gs (share adt)) @ gidx in
            rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
            rely prop_dec (glock gn = Some CPU_ID);
            rely prop_dec (gtype gn = GRANULE_STATE_REC);
            let g' := gn {gnorm: (gnorm gn) {g_runnable: 0}} in
            let e := EVT CPU_ID (REL gidx g') in
            Some (i + 1, adt {log: e :: log adt} {share: (share adt) {gs: (gs (share adt)) # gidx == (g' {glock: None})}})
      | _ => None
      end
    end.

  Definition system_off_reboot_spec (rec: Pointer) (adt: RData) : option RData :=
    rely (peq (base rec) buffer_loc);
    when rec_gidx == ((buffer (priv adt)) @ (offset rec));
    rely is_gidx rec_gidx;
    let gn_rec := (gs (share adt)) @ rec_gidx in
    rely (g_tag (ginfo gn_rec) =? GRANULE_STATE_REC);
    rely (ref_accessible gn_rec CPU_ID);
    rely (gtype gn_rec =? GRANULE_STATE_REC);
    rely (g_inited (gro gn_rec));
    rely (g_rec (gro gn_rec) =? rec_gidx);
    let rd_gidx := g_rec_rd (grec gn_rec) in
    let idx := g_rec_idx (gro gn_rec) in
    let recl_gidx := g_rec_rec_list (grec gn_rec) in
    rely is_gidx rd_gidx; rely is_gidx recl_gidx;
    when adt == query_oracle adt;
    let gn_rec := (gs (share adt)) @ rec_gidx in
    rely (g_tag (ginfo gn_rec) =? GRANULE_STATE_REC);
    rely prop_dec (glock gn_rec = None);
    let gn_rec := (gs (share adt)) @ rec_gidx in
    let gn_rec := gn_rec {gnorm: (gnorm gn_rec) {g_runnable: 0}} in
    let e := EVT CPU_ID (ACQ rec_gidx) in
    rely (gtype gn_rec =? g_tag (ginfo gn_rec));
    let e' := EVT CPU_ID (REL rec_gidx gn_rec {glock: Some CPU_ID}) in
    let adt := adt {log: e' :: e :: log adt} {share: (share adt) {gs: (gs (share adt)) # rec_gidx == (gn_rec {glock: None})}}
                   {priv: (priv adt) {buffer: ((buffer (priv adt)) # SLOT_REC_LIST == (Some recl_gidx))}} in
    match system_off_reboot_loop (Z.to_nat MAX_NUM_RECS) 0 rec_gidx rd_gidx idx adt with
    | Some (i, adt) =>
      Some adt
    | _ => None
    end.

End Spec.
