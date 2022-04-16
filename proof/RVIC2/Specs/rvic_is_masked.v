Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RVIC.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition rvic_is_masked_spec (rvic: Pointer) (intid: Z64) (adt: RData) : option Z :=
    match intid with
    | VZ64 intid =>
      rely is_int64 intid;
      rely (peq (base rvic) rvic_loc);
      let idx := (intid / 64) in
      let bit := (intid mod 64) in
      let slot := offset rvic in
      rely prop_dec (0 <= slot < 16);
      rely prop_dec (0 <= idx < 512);
      when gidx == (buffer (priv adt)) @ slot;
      let gn := (gs (share adt)) @ gidx in
      rely ((g_tag (ginfo gn)) =? GRANULE_STATE_REC);
      rely prop_dec (glock gn = Some CPU_ID);
      let bits := (r_mask_bits (g_rvic (gnorm gn))) @ idx in
      if Z.land bits (Z.shiftl 1 bit) =? 0
      then Some 0 else Some 1
    end.

End Spec.

