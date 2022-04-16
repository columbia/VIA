Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition save_sysreg_state_spec0 (rec: Pointer) (adt: RData) : option RData :=
    match rec with
    | (_rec_base, _rec_ofst) =>
      when' _t'1 == sysreg_read_spec 38 adt;
      rely is_int64 _t'1;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 38 (VZ64 _t'1) adt;
      when' _t'2 == sysreg_read_spec 43 adt;
      rely is_int64 _t'2;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 43 (VZ64 _t'2) adt;
      when' _t'3 == sysreg_read_spec 44 adt;
      rely is_int64 _t'3;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 44 (VZ64 _t'3) adt;
      when' _t'4 == sysreg_read_spec 45 adt;
      rely is_int64 _t'4;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 45 (VZ64 _t'4) adt;
      when' _t'5 == sysreg_read_spec 39 adt;
      rely is_int64 _t'5;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 39 (VZ64 _t'5) adt;
      when' _t'6 == sysreg_read_spec 40 adt;
      rely is_int64 _t'6;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 40 (VZ64 _t'6) adt;
      when' _t'7 == sysreg_read_spec 41 adt;
      rely is_int64 _t'7;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 41 (VZ64 _t'7) adt;
      when' _t'8 == sysreg_read_spec 42 adt;
      rely is_int64 _t'8;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 42 (VZ64 _t'8) adt;
      when' _t'9 == sysreg_read_spec 46 adt;
      rely is_int64 _t'9;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 46 (VZ64 _t'9) adt;
      when' _t'10 == sysreg_read_spec 47 adt;
      rely is_int64 _t'10;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 47 (VZ64 _t'10) adt;
      when' _t'11 == sysreg_read_spec 48 adt;
      rely is_int64 _t'11;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 48 (VZ64 _t'11) adt;
      when' _t'12 == sysreg_read_spec 49 adt;
      rely is_int64 _t'12;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 49 (VZ64 _t'12) adt;
      when' _t'13 == sysreg_read_spec 50 adt;
      rely is_int64 _t'13;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 50 (VZ64 _t'13) adt;
      when' _t'14 == sysreg_read_spec 51 adt;
      rely is_int64 _t'14;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 51 (VZ64 _t'14) adt;
      when' _t'15 == sysreg_read_spec 52 adt;
      rely is_int64 _t'15;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 52 (VZ64 _t'15) adt;
      when' _t'16 == sysreg_read_spec 53 adt;
      rely is_int64 _t'16;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 53 (VZ64 _t'16) adt;
      when' _t'17 == sysreg_read_spec 54 adt;
      rely is_int64 _t'17;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 54 (VZ64 _t'17) adt;
      when' _t'18 == sysreg_read_spec 55 adt;
      rely is_int64 _t'18;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 55 (VZ64 _t'18) adt;
      when' _t'19 == sysreg_read_spec 56 adt;
      rely is_int64 _t'19;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 56 (VZ64 _t'19) adt;
      when' _t'20 == sysreg_read_spec 57 adt;
      rely is_int64 _t'20;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 57 (VZ64 _t'20) adt;
      when' _t'21 == sysreg_read_spec 58 adt;
      rely is_int64 _t'21;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 58 (VZ64 _t'21) adt;
      when' _t'22 == sysreg_read_spec 59 adt;
      rely is_int64 _t'22;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 59 (VZ64 _t'22) adt;
      when' _t'23 == sysreg_read_spec 60 adt;
      rely is_int64 _t'23;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 60 (VZ64 _t'23) adt;
      when' _t'24 == sysreg_read_spec 61 adt;
      rely is_int64 _t'24;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 61 (VZ64 _t'24) adt;
      when' _t'25 == sysreg_read_spec 62 adt;
      rely is_int64 _t'25;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 62 (VZ64 _t'25) adt;
      when' _t'26 == sysreg_read_spec 63 adt;
      rely is_int64 _t'26;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 63 (VZ64 _t'26) adt;
      when' _t'27 == sysreg_read_spec 64 adt;
      rely is_int64 _t'27;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 64 (VZ64 _t'27) adt;
      when' _t'28 == sysreg_read_spec 65 adt;
      rely is_int64 _t'28;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 65 (VZ64 _t'28) adt;
      when' _t'29 == sysreg_read_spec 66 adt;
      rely is_int64 _t'29;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 66 (VZ64 _t'29) adt;
      when' _t'30 == sysreg_read_spec 67 adt;
      rely is_int64 _t'30;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 67 (VZ64 _t'30) adt;
      when' _t'31 == sysreg_read_spec 68 adt;
      rely is_int64 _t'31;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 68 (VZ64 _t'31) adt;
      when' _t'32 == sysreg_read_spec 69 adt;
      rely is_int64 _t'32;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 69 (VZ64 _t'32) adt;
      when' _t'33 == sysreg_read_spec 70 adt;
      rely is_int64 _t'33;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 70 (VZ64 _t'33) adt;
      when' _t'34 == sysreg_read_spec 32 adt;
      rely is_int64 _t'34;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 32 (VZ64 _t'34) adt;
      when' _t'35 == sysreg_read_spec 33 adt;
      rely is_int64 _t'35;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 33 (VZ64 _t'35) adt;
      when' _t'36 == sysreg_read_spec 35 adt;
      rely is_int64 _t'36;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 35 (VZ64 _t'36) adt;
      when' _t'37 == sysreg_read_spec 36 adt;
      rely is_int64 _t'37;
      when adt == set_rec_sysregs_spec (_rec_base, _rec_ofst) 36 (VZ64 _t'37) adt;
      Some adt
     end
    .

End SpecLow.
