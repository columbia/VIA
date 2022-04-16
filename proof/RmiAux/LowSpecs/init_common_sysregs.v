Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition init_common_sysregs_spec0 (rec: Pointer) (rd: Pointer) (adt: RData) : option RData :=
    match rec, rd with
    | (_rec_base, _rec_ofst), (_rd_base, _rd_ofst) =>
      when adt == set_rec_common_sysregs_spec (_rec_base, _rec_ofst) 75 (VZ64 70388072318015) adt;
      when adt == set_rec_common_sysregs_spec (_rec_base, _rec_ofst) 74 (VZ64 3221370256) adt;
      when'' _t'1_base, _t'1_ofst == get_rd_g_rtt_spec (_rd_base, _rd_ofst) adt;
      rely is_int _t'1_ofst;
      when' _t'2 == granule_addr_spec (_t'1_base, _t'1_ofst) adt;
      rely is_int64 _t'2;
      rely is_int64 (Z.land _t'2 281474976710654);
      when adt == set_rec_common_sysregs_spec (_rec_base, _rec_ofst) 73 (VZ64 (Z.land _t'2 281474976710654)) adt;
      Some adt
     end
    .

End SpecLow.
