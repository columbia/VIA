Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition psci_reset_rec_spec (rec: Pointer) (target_rec: Pointer) (adt: RData) : option RData :=
    rely (peq (base target_rec) buffer_loc);
    rely (peq (base rec) buffer_loc);
    when target_gidx == ((buffer (priv adt)) @ (offset target_rec));
    when rec_gidx == ((buffer (priv adt)) @ (offset rec));
    rely prop_dec (rec_gidx <> target_gidx);
    let gn := (gs (share adt)) @ target_gidx in
    let gn_rec := (gs (share adt)) @ rec_gidx in
    rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
    rely g_tag (ginfo gn_rec) =? GRANULE_STATE_REC;
    rely ref_accessible gn CPU_ID;
    rely ref_accessible gn_rec CPU_ID;
    let sctlr := r_sctlr_el1 (g_regs (grec gn_rec)) in
    rely is_int64 sctlr;
    let g' := gn {grec : (grec gn) {g_pstate: 965} {g_regs: set_reg sctlr_el1 (Z.lor SCTLR_EL1_FLAGS (Z.land sctlr SCTLR_EL1_EE)) (g_regs (grec gn))}} in
    Some adt {share: (share adt) {gs: (gs (share adt)) # target_gidx == g'}}.

End Spec.

