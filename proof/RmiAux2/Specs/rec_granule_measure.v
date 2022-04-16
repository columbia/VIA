Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition measure_rec c rec :=
    measure_extend_rec_sysregs
      (measure_extend_rec_pstate
         (measure_extend_rec_regs
            (measure_extend_rec_header c)
            (g_regs rec))
         (g_pstate rec))
      (g_regs rec).

  Definition rec_granule_measure_spec (rd: Pointer) (rec: Pointer) (data_size: Z64) (adt: RData) : option RData :=
    rely (peq (base rd) buffer_loc);
    rely (peq (base rec) buffer_loc);
    when gidx == (buffer (priv adt)) @ (offset rd);
    when rec_gidx == (buffer (priv adt)) @ (offset rec);
    rely is_gidx gidx; rely is_gidx rec_gidx;
    let gn := (gs (share adt)) @ gidx in
    let gn_rec := (gs (share adt)) @ rec_gidx in
    rely (g_tag (ginfo gn) =? GRANULE_STATE_RD);
    rely (g_tag (ginfo gn_rec) =? GRANULE_STATE_REC);
    rely prop_dec (glock gn = Some CPU_ID);
    rely (ref_accessible gn_rec CPU_ID);
    if (g_measurement_algo (gnorm gn)) =? MEASUREMENT_ALGO_SHA256 then
      let g' := gn {gnorm: (gnorm gn) {g_measurement_ctx: measure_rec (g_measurement_ctx (gnorm gn)) (grec gn_rec)}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    else
      Some adt.

End Spec.

