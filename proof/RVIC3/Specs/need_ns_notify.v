Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RVIC2.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition need_ns_notify_spec (rec: Pointer) (target_rec: Pointer) (intid: Z64) (adt: RData) : option Z :=
    match intid with
    | VZ64 intid =>
      rely is_int64 intid;
      rely (peq (base rec) buffer_loc);
      rely (peq (base target_rec) buffer_loc);
      rely prop_dec (0 <= offset target_rec < 16);
      when rec_gidx == ((buffer (priv adt)) @ (offset rec));
      when target_gidx == ((buffer (priv adt)) @ (offset target_rec));
      let gn_rec := (gs (share adt)) @ rec_gidx in
      let gn_target := (gs (share adt)) @ target_gidx in
      rely (gtype gn_rec) =? GRANULE_STATE_REC;
      rely (gtype gn_target) =? GRANULE_STATE_REC;
      rely (g_inited (gro gn_rec));
      rely (g_inited (gro gn_target));
      let idx1 := (g_rec_idx (gro gn_target)) in
      let idx2 := (g_rec_idx (gro gn_rec)) in
      rely is_int64 idx1; rely is_int64 idx2;
      if idx1 =? idx2 then
        Some 0
      else
        rely (g_tag (ginfo gn_target)) =? GRANULE_STATE_REC;
        rely prop_dec (glock gn_target = Some CPU_ID);
        let enabled := (r_rvic_enabled (g_rvic (gnorm gn_target))) in
        rely is_int enabled;
        if enabled =? 0 then
          Some 0
        else
          let idx := (intid / 64) in
          let bit := (intid mod 64) in
          rely prop_dec (0 <= idx < 512);
          let bits := (r_pending_bits (g_rvic (gnorm gn_target))) @ idx in
          if Z.land bits (Z.shiftl 1 bit) =? 0 then
            Some 0
          else
            let bits := (r_mask_bits (g_rvic (gnorm gn_target))) @ idx in
            if Z.land bits (Z.shiftl 1 bit) =? 0 then
              Some 1
            else
              Some 0
    end.

End Spec.

