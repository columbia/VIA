Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RunAux.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition complete_hvc_exit_spec (rec: Pointer) (adt: RData) : option RData :=
    rely (peq (base rec) buffer_loc);
    when gidx == (buffer (priv adt)) @ (offset rec);
    let gn := (gs (share adt)) @ gidx in
    rely (ref_accessible gn CPU_ID);
    rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
    let esr := g_esr (grec gn) in
    rely is_int64 esr;
    if (Z.land esr ESR_EL2_EC_MASK) =? ESR_EL2_EC_HVC then
      rely is_int64 ((rec_run (priv adt)) @ 5); rely is_int64 ((rec_run (priv adt)) @ 6);
      rely is_int64 ((rec_run (priv adt)) @ 7); rely is_int64 ((rec_run (priv adt)) @ 8);
      rely is_int64 ((rec_run (priv adt)) @ 9); rely is_int64 ((rec_run (priv adt)) @ 10);
      rely is_int64 ((rec_run (priv adt)) @ 11);
      let g' := gn {grec: (grec gn) {g_regs: (g_regs (grec gn)) {r_x0: ((rec_run (priv adt)) @ 5)} {r_x1: (rec_run (priv adt)) @ 6}
                                                                {r_x2: ((rec_run (priv adt)) @ 7)} {r_x3: (rec_run (priv adt)) @ 8}
                                                                {r_x4: ((rec_run (priv adt)) @ 9)} {r_x5: (rec_run (priv adt)) @ 10}
                                                                {r_x6: ((rec_run (priv adt)) @ 11)}} {g_esr: 0}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    else Some adt.

End Spec.

