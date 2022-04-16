Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import TableDataOpsIntro.Spec.
Require Import TableDataOpsRef1.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition table_unmap2_spec0 (g_rd: Pointer) (map_addr: Z64) (level: Z64) (adt: RData) : option (RData * Z64) :=
    match g_rd, map_addr, level with
    | (_g_rd_base, _g_rd_ofst), VZ64 _map_addr, VZ64 _level =>
      rely is_int64 _map_addr;
      rely is_int64 _level;
      when' _t'1, adt == table_unmap1_spec (_g_rd_base, _g_rd_ofst) (VZ64 _map_addr) (VZ64 _level) adt;
      rely is_int64 _t'1;
      Some (adt, (VZ64 _t'1))
     end
    .

End SpecLow.
