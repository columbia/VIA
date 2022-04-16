Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition init_mask_bits m :=
    m # 0 == U64MAX # 1 == U64MAX # 2 == U64MAX # 3 == U64MAX # 4 == U64MAX # 5 == U64MAX # 6 == U64MAX # 7 == U64MAX.

  Definition init_rec_rvic_state_spec (rvic: Pointer) (adt: RData) : option RData :=
    rely (peq (base rvic) rvic_loc);
    when gidx == ((buffer (priv adt)) @ (offset rvic));
    let gn := (gs (share adt)) @ gidx in
    rely (g_tag (ginfo gn)) =? GRANULE_STATE_REC;
    rely prop_dec (glock gn = Some CPU_ID);
    let g' := gn {gnorm: (gnorm gn) {g_rvic: (g_rvic (gnorm gn)) {r_mask_bits: init_mask_bits (r_mask_bits (g_rvic (gnorm gn)))}}} in
    Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}.

End Spec.

