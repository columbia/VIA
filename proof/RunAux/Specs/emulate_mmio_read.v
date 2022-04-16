Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition emulate_mmio_read_spec (esr: Z64) (rt: Z) (rec: Pointer) (adt: RData) : option RData :=
    match esr with
    | VZ64 esr =>
      rely is_int64 esr; rely is_int rt;
      rely (peq (base rec) buffer_loc);
      when gidx ==  (buffer (priv adt)) @ (offset rec);
      let gn := (gs (share adt)) @ gidx in
      rely (ref_accessible gn CPU_ID);
      rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
      let read_val := ((rec_run (priv adt)) @ 14) in
      let mask := __access_mask esr in
      rely is_int64 read_val; rely is_int64 mask;
      let val := Z.land read_val mask in
      let extend := __esr_sign_extend esr in
      rely is_int extend;
      if extend =? 0 then
        let g' := gn {grec: (grec gn) {g_regs: set_reg rt val (g_regs (grec gn))}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
      else
        let len := __access_len esr in
        rely is_int len;
        let bitcount := len * 8 in
        rely is_int bitcount; rely is_int (bitcount - 1);
        let mask := Z.shiftl 1 (bitcount - 1) in
        rely is_int64 mask; rely is_int64 (Z.lxor val mask);
        let val := (Z.lxor val mask) - mask in
        rely is_int64 val;
        if __esr_sixty_four esr then
          let g' := gn {grec: (grec gn) {g_regs: set_reg rt val (g_regs (grec gn))}} in
          Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
        else
          let val := Z.land val 4294967295 in
          let g' := gn {grec: (grec gn) {g_regs: set_reg rt val (g_regs (grec gn))}} in
          Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    end.

End Spec.

