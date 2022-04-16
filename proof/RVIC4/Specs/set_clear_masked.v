Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RVIC3.Spec.
Require Import AbsAccessor.Spec.
Require Import RVIC2.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition set_clear_masked_spec (rec: Pointer) (target: Z64) (intid: Z64) (masked: Z) (adt: RData) : option RData :=
    match target, intid with
    | VZ64 target, VZ64 intid =>
      rely is_int64 target; rely is_int64 intid; rely is_int masked;
      rely (peq (base rec) buffer_loc);
      when' x0, adt == validate_and_lookup_target_spec rec (VZ64 target) (VZ64 intid) adt;
      let target_rec := target_rec (priv adt) in
      rely prop_dec (0 <= target_rec < 16);
      rely is_int64 x0;
      if x0 =? 0 then
        rely (target_rec =? SLOT_REC_TARGET);
        let idx := intid / 64 in
        let bit := intid mod 64 in
        rely prop_dec (0 <= idx < 512);
        when rec_gidx == ((buffer (priv adt)) @ (offset rec));
        when target_gidx == ((buffer (priv adt)) @ target_rec);
        let gn_rec := (gs (share adt)) @ rec_gidx in
        let gn_target := (gs (share adt)) @ target_gidx in
        rely (gtype gn_rec) =? GRANULE_STATE_REC;
        rely (gtype gn_target) =? GRANULE_STATE_REC;
        rely g_tag (ginfo gn_target) =? GRANULE_STATE_REC;
        rely prop_dec (glock gn_target = Some CPU_ID);
        rely (g_inited (gro gn_rec));
        rely (g_inited (gro gn_target));
        rely is_gidx target_gidx;
        let idx1 := (g_rec_idx (gro gn_target)) in
        let idx2 := (g_rec_idx (gro gn_rec)) in
        rely is_int64 idx1; rely is_int64 idx2;
        rely (g_rec (gro gn_target) =? target_gidx);
        if masked =? 1 then
          let bits := (r_mask_bits (g_rvic (gnorm gn_target))) @ idx in
          let bits' := Z.lor bits (Z.shiftl 1 bit) in
          let rvic' := (g_rvic (gnorm gn_target)) {r_mask_bits: (r_mask_bits (g_rvic (gnorm gn_target))) # idx == bits'} in
          let g' := gn_target {gnorm: (gnorm gn_target) {g_rvic: rvic'}} in
          Some adt {log: EVT CPU_ID (REL target_gidx g') :: log adt} {share: (share adt) {gs: (gs (share adt)) # target_gidx == (g' {glock: None})}}
               {priv: (priv adt) {buffer: (buffer (priv adt)) # target_rec == None} {rvic_x0: x0}}
        else
          let enabled := (r_rvic_enabled (g_rvic (gnorm gn_target))) in
          let pending_bits := (r_pending_bits (g_rvic (gnorm gn_target))) @ idx in
          let mask_bits := (r_mask_bits (g_rvic (gnorm gn_target))) @ idx in
          let not_pending := Z.land pending_bits (Z.shiftl 1 bit) =? 0 in
          let not_masked := Z.land mask_bits (Z.shiftl 1 bit) =? 0 in
          rely is_int enabled;
          let bits' := Z.land mask_bits (Z.lnot (Z.shiftl 1 bit)) in
          let rvic' := (g_rvic (gnorm gn_target)) {r_mask_bits: (r_mask_bits (g_rvic (gnorm gn_target))) # idx == bits'} in
          let g' := gn_target {gnorm: (gnorm gn_target) {g_rvic: rvic'}} in
          Some adt {log: EVT CPU_ID (REL target_gidx g') :: log adt} {share: (share adt) {gs: (gs (share adt)) # target_gidx == (g' {glock: None})}}
                {priv: (priv adt) {buffer: (buffer (priv adt)) # target_rec == None} {rvic_x0: x0}}
      else
        rely (target_rec =? 0);
        Some adt {priv: (priv adt) {rvic_x0: x0}}
    end.

End Spec.

