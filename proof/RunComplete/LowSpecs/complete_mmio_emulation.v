Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RunAux.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition complete_mmio_emulation_spec0 (rec: Pointer) (adt: RData) : option (RData * Z) :=
    match rec with
    | (_rec_base, _rec_ofst) =>
      when' _t'7 == get_rec_run_is_emulated_mmio_spec  adt;
      rely is_int64 _t'7;
      if (_t'7 =? 0) then
        Some (adt, 1)
      else
        when' _esr == get_rec_last_run_info_esr_spec (_rec_base, _rec_ofst) adt;
        rely is_int64 _esr;
        when _rt == esr_srt_spec (VZ64 _esr) adt;
        rely is_int _rt;
        rely is_int64 (Z.land _esr 4227858432);
        if (negb ((Z.land _esr 4227858432) =? 2415919104)) then
          let _t'6 := 1 in
          Some (adt, 0)
        else
          rely is_int64 (Z.land _esr 16777216);
          let _t'6 := ((Z.land _esr 16777216) =? 0) in
          if _t'6 then
            Some (adt, 0)
          else
            when _t'3 == esr_is_write_spec (VZ64 _esr) adt;
            rely is_int _t'3;
            if (_t'3 =? 0) then
              let _t'4 := (negb (_rt =? 31)) in
              if _t'4 then
                when adt == emulate_mmio_read_spec (VZ64 _esr) _rt (_rec_base, _rec_ofst) adt;
                when' _t'5 == get_rec_pc_spec (_rec_base, _rec_ofst) adt;
                rely is_int64 _t'5;
                rely is_int64 (_t'5 + 4);
                when adt == set_rec_pc_spec (_rec_base, _rec_ofst) (VZ64 (_t'5 + 4)) adt;
                Some (adt, 1)
              else
                when' _t'5 == get_rec_pc_spec (_rec_base, _rec_ofst) adt;
                rely is_int64 _t'5;
                rely is_int64 (_t'5 + 4);
                when adt == set_rec_pc_spec (_rec_base, _rec_ofst) (VZ64 (_t'5 + 4)) adt;
                Some (adt, 1)
            else
              let _t'4 := 0 in
              when' _t'5 == get_rec_pc_spec (_rec_base, _rec_ofst) adt;
              rely is_int64 _t'5;
              rely is_int64 (_t'5 + 4);
              when adt == set_rec_pc_spec (_rec_base, _rec_ofst) (VZ64 (_t'5 + 4)) adt;
              Some (adt, 1)
     end
    .

End SpecLow.
