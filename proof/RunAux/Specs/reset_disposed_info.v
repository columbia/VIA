Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition reset_disposed_info_spec (rec: Pointer) (adt: RData) : option RData :=
    rely (peq (base rec) buffer_loc);
    when gidx == (buffer (priv adt)) @ (offset rec);
    let gn := (gs (share adt)) @ gidx in
    rely (ref_accessible gn CPU_ID);
    rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
    let g' := gn {grec: (grec gn) {g_dispose_pending: 0}} in
    Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}.

End Spec.

