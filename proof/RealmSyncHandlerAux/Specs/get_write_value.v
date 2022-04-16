Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition get_write_value_spec (rec: Pointer) (esr: Z64) (adt: RData) : option Z64 :=
    match esr with
    | VZ64 esr =>
      rely is_int64 esr;
      rely (peq (base rec) buffer_loc);
      when gidx == (buffer (priv adt)) @ (offset rec);
      let gn := (gs (share adt)) @ gidx in
      rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
      rely (ref_accessible gn CPU_ID);
      let rt := __esr_srt esr in
      rely is_int rt;
      if rt =? 31 then Some (VZ64 0)
      else
        let val := get_reg rt (g_regs (grec gn)) in
        let mask := __access_mask esr in
        rely is_int64 val; rely is_int64 mask;
        Some (VZ64 (Z.land val mask))
    end.

End Spec.

