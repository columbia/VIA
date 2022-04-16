Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmSyncHandlerAux.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition handle_data_abort_spec (rec: Pointer) (esr: Z64) (adt: RData) : option RData :=
    match esr with
    | VZ64 esr =>
      rely is_int64 esr;
      rely (peq (base rec) buffer_loc);
      when gidx == (buffer (priv adt)) @ (offset rec);
      let gn := (gs (share adt)) @ gidx in
      rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
      rely (ref_accessible gn CPU_ID);
      let far := 0 in
      let hpfar := r_hpfar_el2 (cpu_regs (priv adt)) in
      let spsr := r_spsr_el2 (cpu_regs (priv adt)) in
      rely is_int64 hpfar; rely is_int64 spsr;
      let esr := (if Z.land spsr SPSR_EL2_nRW_AARCH32 =? 0 then esr
                  else (Z.land esr NOT_ESR_EL2_ABORT_ISV_BIT)) in
      let len := __access_len esr in
      rely is_int len;
      let par_base := g_rec_par_base (grec gn) in
      let par_end := g_rec_par_end (grec gn) in
      rely is_int64 par_base; rely is_int64 par_end; rely is_int64 (hpfar + len);
      if (Z.land esr ESR_EL2_ABORT_ISV_BIT =? 0)
         || negb ((hpfar + len >? par_base) && (hpfar <? par_end))
      then
        let esr := Z.land esr (Z.lor ESR_EL2_EC_MASK ESR_EL2_ABORT_FSC_MASK) in
        Some adt {priv: (priv adt) {rec_run: (rec_run (priv adt))
                                               # 1 == esr # 2 == 0 # 3 == hpfar # 4 == 0}}
      else
        let rt := __esr_srt esr in
        rely is_int rt; rely is_int64 (get_reg rt (g_regs (grec gn)));
        rely is_int64 (__access_mask esr);
        let write_val := (if (negb (__esr_is_write esr)) || (rt =? 31) then 0
                          else let val := get_reg rt (g_regs (grec gn)) in
                              let mask := __access_mask esr in Z.land val mask)
        in
        rely is_int64 (r_far_el2 (cpu_regs (priv adt)));
        let far := Z.land (r_far_el2 (cpu_regs (priv adt))) NOT_GRANULE_MASK in
        let g' := gn {grec: (grec gn) {g_esr: esr}} in
        let esr := Z.land esr ESR_ABORT_MASK in
        Some adt {priv: (priv adt) {rec_run: (rec_run (priv adt))
                                               # 1 == esr # 2 == far # 3 == hpfar # 4 == write_val}}
             {share: (share adt) {gs: (gs (share adt)) # gidx == g'}}
    end.

End Spec.

