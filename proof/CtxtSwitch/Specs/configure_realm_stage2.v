Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition configure_realm_stage2_spec (rec: Pointer) (adt: RData) : option RData :=
    rely (peq (base rec) buffer_loc);
    when gidx == (buffer (priv adt)) @ (offset rec);
    let gn := (gs (share adt)) @ gidx in
    rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
    rely (ref_accessible gn CPU_ID);
    let comm := g_regs (grec gn) in
    rely (regs_is_int64_dec comm);
    Some adt {priv: (priv adt) {cpu_regs: (cpu_regs (priv adt)) {r_vtcr_el2: (r_vtcr_el2 comm)}
                                                                {r_vttbr_el2: (r_vttbr_el2 comm)}}}.

End Spec.

