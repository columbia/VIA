Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition rvic_clear_flag_spec (intid: Z64) (bitmap: Pointer) (adt: RData) : option RData :=
    match intid with
    | VZ64 intid =>
      rely is_int64 intid;
      let idx := intid / 64 in
      let bit := intid mod 64 in
      let slot := offset bitmap in
      rely prop_dec (0 <= slot < 16);
      rely prop_dec (0 <= idx < 512);
      when gidx == ((buffer (priv adt)) @ slot);
      let gn := (gs (share adt)) @ gidx in
      rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
      rely prop_dec (glock gn = Some CPU_ID);
      if peq (base bitmap) rvic_pending_loc then
        let bits := (r_pending_bits (g_rvic (gnorm gn))) @ idx in
        let bits' := Z.land bits (Z.lnot (Z.shiftl 1 bit)) in
        let rvic' := (g_rvic (gnorm gn)) {r_pending_bits: (r_pending_bits (g_rvic (gnorm gn))) # idx == bits'} in
        let g' := gn {gnorm: (gnorm gn) {g_rvic: rvic'}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      else
        let bits := (r_mask_bits (g_rvic (gnorm gn))) @ idx in
        let bits' := Z.land bits (Z.lnot (Z.shiftl 1 bit)) in
        let rvic' := (g_rvic (gnorm gn)) {r_mask_bits: (r_mask_bits (g_rvic (gnorm gn))) # idx == bits'} in
        let g' := gn {gnorm: (gnorm gn) {g_rvic: rvic'}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    end.

End Spec.

