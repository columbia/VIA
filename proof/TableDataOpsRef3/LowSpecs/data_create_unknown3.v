Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import TableDataOpsIntro.Spec.
Require Import TableDataOpsRef2.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition data_create_unknown3_spec0 (g_rd: Pointer) (data_addr: Z64) (map_addr: Z64) (g_data: Pointer) (adt: RData) : option (RData * Z64) :=
    match g_rd, data_addr, map_addr, g_data with
    | (_g_rd_base, _g_rd_ofst), VZ64 _data_addr, VZ64 _map_addr, (_g_data_base, _g_data_ofst) =>
      rely is_int64 _data_addr;
      rely is_int64 _map_addr;
      when' _t'1, adt == data_create_unknown2_spec (_g_rd_base, _g_rd_ofst) (VZ64 _data_addr) (VZ64 _map_addr) (_g_data_base, _g_data_ofst) adt;
      rely is_int64 _t'1;
      Some (adt, (VZ64 _t'1))
     end
    .

End SpecLow.
