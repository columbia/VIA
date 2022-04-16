Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition handle_id_sysreg_trap_spec (rec: Pointer) (esr: Z64) (adt: RData) : option RData :=
    match esr with
    | VZ64 esr =>
      rely is_int64 esr;
      rely (peq (base rec) buffer_loc);
      when gidx == (buffer (priv adt)) @ (offset rec);
      let gn := (gs (share adt)) @ gidx in
      rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
      rely (ref_accessible gn CPU_ID);
      let idreg := Z.land esr ESR_EL2_SYSREG_MASK in
      rely is_int idreg;
      if __ESR_EL2_SYSREG_IS_WRITE esr then None
      else
        let mask := (if idreg =? ESR_EL2_SYSREG_ID_AA64ISAR1_EL1
                      then HANDLE_ID_SYSREG_MASK else 0) in
        let rt := __ESR_EL2_SYSREG_ISS_RT esr in
        rely is_int rt; rely is_int64 (ID_AA64PFR0_EL1 (id_regs (priv adt)));
        let val := Z.land (ID_AA64PFR0_EL1 (id_regs (priv adt))) (U64MAX - mask) in
        let g' := gn {grec: (grec gn) {g_regs: set_reg rt val (g_regs (grec gn))}} in
        Some adt {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    end.

End Spec.

