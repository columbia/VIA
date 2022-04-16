Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition init_rec_sysregs_spec (rec: Pointer) (mpidr: Z64) (adt: RData) : option RData :=
    match mpidr with
    | VZ64 mpidr =>
      rely is_int64 mpidr;
      rely (peq (base rec) buffer_loc);
      when rec_gidx == ((buffer (priv adt)) @ (offset rec));
      let gn := (gs (share adt)) @ rec_gidx in
      rely (g_tag (ginfo gn)) =? GRANULE_STATE_REC;
      rely (ref_accessible gn CPU_ID);
      let sysregs' := (g_regs (grec gn)) {r_pmcr_el0 : PMCR_EL0_RES1}
                                            {r_sctlr_el1: SCTLR_EL1_FLAGS}
                                            {r_mdscr_el1 : MDSCR_EL1_TDCC_BIT}
                                            {r_vmpidr_el2 : mpidr}
                                            {r_cnthctl_el2 : CNTHCTL_EL2_NO_TRAPS} in
      let g' := gn {grec: (grec gn) {g_regs: sysregs'}} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # rec_gidx == g'}}
    end.

End Spec.

