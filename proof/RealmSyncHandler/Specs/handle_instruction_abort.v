Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition handle_instruction_abort_spec (rec: Pointer) (esr: Z64) (adt: RData) : option (RData * Z) :=
    match esr with
    | VZ64 esr =>
      rely is_int64 esr;
      rely (peq (base rec) buffer_loc);
      when gidx == (buffer (priv adt)) @ (offset rec);
      let gn := (gs (share adt)) @ gidx in
      rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
      rely (ref_accessible gn CPU_ID);
      let fsc := Z.land esr ESR_EL2_ABORT_FSC_MASK in
      let fsc_type := Z.land fsc NOT_ESR_EL2_ABORT_FSC_LEVEL_MASK in
      let hpfar := r_hpfar_el2 (cpu_regs (priv adt)) in
      rely is_int64 hpfar;
      if fsc_type =? ESR_EL2_ABORT_FSC_PERMISSION_FAULT then
        Some (adt, 0)
      else
        if fsc_type =? ESR_EL2_ABORT_FSC_TRANSLATION_FAULT then
          let fipa := Z.shiftl (Z.land hpfar HPFAR_EL2_FIPA_MASK) HPFAR_EL2_FIPA_OFFSET in
          rely is_int64 fipa;
          let par_base := g_rec_par_base (grec gn) in
          let par_end := g_rec_par_end (grec gn) in
          rely is_int64 par_base; rely is_int64 par_end;
          if (par_base <=? fipa) && (fipa <? par_end) then
            let esr := Z.land esr (Z.lor ESR_EL2_EC_MASK ESR_EL2_ABORT_FSC_MASK) in
            Some (adt {priv: (priv adt) {rec_run: (rec_run (priv adt)) # 1 == esr # 3 == hpfar}}, 1)
          else Some (adt, 0)
        else Some (adt, 0)
    end.

End Spec.

