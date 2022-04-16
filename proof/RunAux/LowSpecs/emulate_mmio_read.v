Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition emulate_mmio_read_spec0 (esr: Z64) (rt: Z) (rec: Pointer) (adt: RData) : option RData :=
    match esr, rt, rec with
    | VZ64 _esr, _rt, (_rec_base, _rec_ofst) =>
      when' _t'1 == get_rec_run_emulated_read_val_spec  adt;
      rely is_int64 _t'1;
      rely is_int64 _esr;
      when' _t'2 == access_mask_spec (VZ64 _esr) adt;
      rely is_int64 _t'2;
      rely is_int64 (Z.land _t'1 _t'2);
      let _val := (Z.land _t'1 _t'2) in
      when _t'6 == esr_sign_extend_spec (VZ64 _esr) adt;
      rely is_int _t'6;
      if (negb (_t'6 =? 0)) then
        when _t'3 == access_len_spec (VZ64 _esr) adt;
        rely is_int _t'3;
        rely is_int (_t'3 * 8);
        let _bit_count := (_t'3 * 8) in
        rely is_int (_bit_count - 1);
        rely is_int64 (_bit_count - 1);
        when' _mask == shiftl_spec (VZ64 1) (VZ64 (_bit_count - 1)) adt;
        rely is_int64 _mask;
        rely is_int64 (Z.lxor _val _mask);
        rely is_int64 ((Z.lxor _val _mask) - _mask);
        let _val := ((Z.lxor _val _mask) - _mask) in
        when _t'5 == esr_sixty_four_spec (VZ64 _esr) adt;
        rely is_int _t'5;
        if (_t'5 =? 0) then
          rely is_int64 (Z.land _val 4294967295);
          let _val := (Z.land _val 4294967295) in
          rely is_int _rt;
          rely is_int64 _val;
          when adt == set_rec_regs_spec (_rec_base, _rec_ofst) _rt (VZ64 _val) adt;
          Some adt
        else
          rely is_int _rt;
          rely is_int64 _val;
          when adt == set_rec_regs_spec (_rec_base, _rec_ofst) _rt (VZ64 _val) adt;
          Some adt
      else
        rely is_int _rt;
        rely is_int64 _val;
        when adt == set_rec_regs_spec (_rec_base, _rec_ofst) _rt (VZ64 _val) adt;
        Some adt
     end
    .

End SpecLow.
