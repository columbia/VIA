Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiAux.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition init_regs r param mpidr rtt :=
    r {g_regs: (g_regs r) {r_x0: (param @ 0)} {r_x1: (param @ 1)} {r_x2: (param @ 2)}
                          {r_x3: (param @ 3)} {r_x4: (param @ 4)} {r_x5: (param @ 5)}
                          {r_x6: (param @ 6)} {r_x7: (param @ 7)}
                          {r_pmcr_el0: PMCR_EL0_RES1} {r_sctlr_el1: SCTLR_EL1_FLAGS} {r_mdscr_el1: MDSCR_EL1_TDCC_BIT}
                          {r_vmpidr_el2: mpidr} {r_cnthctl_el2 : CNTHCTL_EL2_NO_TRAPS}
                          {r_hcr_el2 : HCR_FLAGS} {r_vtcr_el2 : VTCR_FLAGS} {r_vttbr_el2 : rtt}}
      {g_pc: (param @ 8)} {g_pstate: PSTATE_INIT}.

  Definition init_rec_regs_spec (rec: Pointer) (mpidr: Z64) (rd: Pointer) (adt: RData) : option RData :=
    match mpidr with
    | VZ64 mpidr =>
      rely is_int64 mpidr;
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
      let param := rec_params (priv adt) in
      rely prop_dec (forall n, is_int64 (param @ n) = true);
      let g' := g_rec {grec: init_regs (grec g_rec) param mpidr rtt} in
      Some adt {share: (share adt) {gs: (gs (share adt)) # rec_gidx == g'}}
    end.

End Spec.

