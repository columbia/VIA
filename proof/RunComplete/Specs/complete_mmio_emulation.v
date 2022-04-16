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

  Definition complete_mmio_emulation_spec (rec: Pointer) (adt: RData) : option (RData * Z) :=
    rely (peq (base rec) buffer_loc);
    when gidx == (buffer (priv adt)) @ (offset rec);
    let gn := (gs (share adt)) @ gidx in
    rely (ref_accessible gn CPU_ID);
    rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
    let is_emul := (rec_run (priv adt)) @ 13 in
    let read_val := ((rec_run (priv adt)) @ 14) in
    rely is_int64 is_emul; rely is_int64 read_val;
    if is_emul =? 0 then
      Some (adt, 1)
    else
      let esr := g_esr (grec gn) in
      let rt := __esr_srt esr in
      let mask := __access_mask esr in
      rely is_int64 esr; rely is_int rt; rely is_int64 mask;
      if (negb (Z.land esr ESR_EL2_EC_MASK =? ESR_EL2_EC_DATA_ABORT) ||
            (Z.land esr ESR_EL2_ABORT_ISV_BIT =? 0))
      then
        Some (adt, 0)
      else
        rely is_int64 (g_pc (grec gn)); rely is_int64 (g_pc (grec gn) + 4);
        if (negb (__esr_is_write esr)) && (negb (rt =? 31)) then
          let val := Z.land read_val mask in
          let extend := __esr_sign_extend esr in
          rely is_int extend;
          if extend =? 0 then
            let g' := gn {grec: (grec gn) {g_regs: set_reg rt val (g_regs (grec gn))} {g_pc: (g_pc (grec gn)) + 4}} in
            Some (adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}, 1)
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
              let g' := gn {grec: (grec gn) {g_regs: set_reg rt val (g_regs (grec gn))} {g_pc: (g_pc (grec gn)) + 4}} in
              Some (adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}, 1)
            else
              let val := Z.land val 4294967295 in
              let g' := gn {grec: (grec gn) {g_regs: set_reg rt val (g_regs (grec gn))} {g_pc: (g_pc (grec gn)) + 4}} in
              Some (adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}, 1)
        else
          let g' := gn {grec: (grec gn)  {g_pc: (g_pc (grec gn)) + 4}} in
          Some (adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}, 1).

End Spec.

