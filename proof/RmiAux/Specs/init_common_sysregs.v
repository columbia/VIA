Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition init_common_sysregs_spec (rec: Pointer) (rd: Pointer) (adt: RData) : option RData :=
    rely (peq (base rec) buffer_loc);
    rely (peq (base rd) buffer_loc);
    when rec_gidx == ((buffer (priv adt)) @ (offset rec));
    when rd_gidx == ((buffer (priv adt)) @ (offset rd));
    let g_rd := (gs (share adt)) @ rd_gidx in
    let g_rec := (gs (share adt)) @ rec_gidx in
    rely (g_tag (ginfo g_rd)) =? GRANULE_STATE_RD;
    rely (g_tag (ginfo g_rec)) =? GRANULE_STATE_REC;
    rely prop_dec (glock g_rd = Some CPU_ID);
    rely (ref_accessible g_rec CPU_ID);
    let rtt := g_rtt (gnorm g_rd) in
    rely is_gidx rtt;
    let rtt_addr := __gidx_to_addr rtt in
    let rtt := Z.land rtt_addr VTTBR_ADDR_MASK in
    rely is_int64 rtt_addr;
    let sysregs' := (g_regs (grec g_rec)) {r_hcr_el2 : HCR_FLAGS} {r_vtcr_el2 : VTCR_FLAGS} {r_vttbr_el2: rtt} in
    let g' := g_rec {grec: (grec g_rec) {g_regs: sysregs'}} in
    Some adt {share: (share adt) {gs: (gs (share adt)) # rec_gidx == g'}}.

End Spec.

