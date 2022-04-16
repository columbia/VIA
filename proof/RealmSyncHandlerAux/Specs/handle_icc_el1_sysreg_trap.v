Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition handle_icc_el1_sysreg_trap_spec (rec: Pointer) (esr: Z64) (adt: RData) : option RData :=
    match esr with
    | VZ64 esr =>
      rely is_int64 esr;
      rely (peq (base rec) buffer_loc);
      when gidx == (buffer (priv adt)) @ (offset rec);
      let gn := (gs (share adt)) @ gidx in
      rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
      rely (ref_accessible gn CPU_ID);
      let rt := __ESR_EL2_SYSREG_ISS_RT esr in
      rely is_int rt;
      if __ESR_EL2_SYSREG_IS_WRITE esr then
        Some adt
      else
        let g' := gn {grec: (grec gn) {g_regs: set_reg rt 0 (g_regs (grec gn))}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    end.

End Spec.

