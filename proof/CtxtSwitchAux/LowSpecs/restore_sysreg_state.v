Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition restore_sysreg_state_spec0 (rec: Pointer) (adt: RData) : option RData :=
    match rec with
    | (_rec_base, _rec_ofst) =>
      when' _t'1 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 38 adt;
      rely is_int64 _t'1;
      when adt == sysreg_write_spec 38 (VZ64 _t'1) adt;
      when' _t'2 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 43 adt;
      rely is_int64 _t'2;
      when adt == sysreg_write_spec 43 (VZ64 _t'2) adt;
      when' _t'3 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 44 adt;
      rely is_int64 _t'3;
      when adt == sysreg_write_spec 44 (VZ64 _t'3) adt;
      when' _t'4 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 45 adt;
      rely is_int64 _t'4;
      when adt == sysreg_write_spec 45 (VZ64 _t'4) adt;
      when' _t'5 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 39 adt;
      rely is_int64 _t'5;
      when adt == sysreg_write_spec 39 (VZ64 _t'5) adt;
      when' _t'6 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 40 adt;
      rely is_int64 _t'6;
      when adt == sysreg_write_spec 40 (VZ64 _t'6) adt;
      when' _t'7 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 41 adt;
      rely is_int64 _t'7;
      when adt == sysreg_write_spec 41 (VZ64 _t'7) adt;
      when' _t'8 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 42 adt;
      rely is_int64 _t'8;
      when adt == sysreg_write_spec 42 (VZ64 _t'8) adt;
      when' _t'9 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 46 adt;
      rely is_int64 _t'9;
      when adt == sysreg_write_spec 46 (VZ64 _t'9) adt;
      when' _t'10 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 47 adt;
      rely is_int64 _t'10;
      when adt == sysreg_write_spec 47 (VZ64 _t'10) adt;
      when' _t'11 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 48 adt;
      rely is_int64 _t'11;
      when adt == sysreg_write_spec 48 (VZ64 _t'11) adt;
      when' _t'12 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 49 adt;
      rely is_int64 _t'12;
      when adt == sysreg_write_spec 49 (VZ64 _t'12) adt;
      when' _t'13 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 50 adt;
      rely is_int64 _t'13;
      when adt == sysreg_write_spec 50 (VZ64 _t'13) adt;
      when' _t'14 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 51 adt;
      rely is_int64 _t'14;
      when adt == sysreg_write_spec 51 (VZ64 _t'14) adt;
      when' _t'15 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 52 adt;
      rely is_int64 _t'15;
      when adt == sysreg_write_spec 52 (VZ64 _t'15) adt;
      when' _t'16 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 53 adt;
      rely is_int64 _t'16;
      when adt == sysreg_write_spec 53 (VZ64 _t'16) adt;
      when' _t'17 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 54 adt;
      rely is_int64 _t'17;
      when adt == sysreg_write_spec 54 (VZ64 _t'17) adt;
      when' _t'18 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 55 adt;
      rely is_int64 _t'18;
      when adt == sysreg_write_spec 55 (VZ64 _t'18) adt;
      when' _t'19 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 56 adt;
      rely is_int64 _t'19;
      when adt == sysreg_write_spec 56 (VZ64 _t'19) adt;
      when' _t'20 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 57 adt;
      rely is_int64 _t'20;
      when adt == sysreg_write_spec 57 (VZ64 _t'20) adt;
      when' _t'21 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 58 adt;
      rely is_int64 _t'21;
      when adt == sysreg_write_spec 58 (VZ64 _t'21) adt;
      when' _t'22 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 59 adt;
      rely is_int64 _t'22;
      when adt == sysreg_write_spec 59 (VZ64 _t'22) adt;
      when' _t'23 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 60 adt;
      rely is_int64 _t'23;
      when adt == sysreg_write_spec 60 (VZ64 _t'23) adt;
      when' _t'24 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 61 adt;
      rely is_int64 _t'24;
      when adt == sysreg_write_spec 61 (VZ64 _t'24) adt;
      when' _t'25 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 62 adt;
      rely is_int64 _t'25;
      when adt == sysreg_write_spec 62 (VZ64 _t'25) adt;
      when' _t'26 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 63 adt;
      rely is_int64 _t'26;
      when adt == sysreg_write_spec 63 (VZ64 _t'26) adt;
      when' _t'27 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 64 adt;
      rely is_int64 _t'27;
      when adt == sysreg_write_spec 64 (VZ64 _t'27) adt;
      when' _t'28 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 65 adt;
      rely is_int64 _t'28;
      when adt == sysreg_write_spec 65 (VZ64 _t'28) adt;
      when' _t'29 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 66 adt;
      rely is_int64 _t'29;
      when adt == sysreg_write_spec 66 (VZ64 _t'29) adt;
      when' _t'30 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 67 adt;
      rely is_int64 _t'30;
      when adt == sysreg_write_spec 67 (VZ64 _t'30) adt;
      when' _t'31 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 68 adt;
      rely is_int64 _t'31;
      when adt == sysreg_write_spec 68 (VZ64 _t'31) adt;
      when' _t'32 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 72 adt;
      rely is_int64 _t'32;
      when adt == sysreg_write_spec 72 (VZ64 _t'32) adt;
      when' _t'33 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 69 adt;
      rely is_int64 _t'33;
      when adt == sysreg_write_spec 69 (VZ64 _t'33) adt;
      when' _t'34 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 70 adt;
      rely is_int64 _t'34;
      when adt == sysreg_write_spec 70 (VZ64 _t'34) adt;
      when' _t'35 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 32 adt;
      rely is_int64 _t'35;
      when adt == sysreg_write_spec 32 (VZ64 _t'35) adt;
      when' _t'36 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 33 adt;
      rely is_int64 _t'36;
      when adt == sysreg_write_spec 33 (VZ64 _t'36) adt;
      when' _t'37 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 35 adt;
      rely is_int64 _t'37;
      when adt == sysreg_write_spec 35 (VZ64 _t'37) adt;
      when' _t'38 == get_rec_sysregs_spec (_rec_base, _rec_ofst) 36 adt;
      rely is_int64 _t'38;
      when adt == sysreg_write_spec 36 (VZ64 _t'38) adt;
      Some adt
     end
    .

End SpecLow.
