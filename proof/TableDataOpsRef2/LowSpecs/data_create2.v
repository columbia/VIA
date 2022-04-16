Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import TableDataOpsRef1.Spec.
Require Import TableDataOpsIntro.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition data_create2_spec0 (g_rd: Pointer) (data_addr: Z64) (map_addr: Z64) (g_data: Pointer) (g_src: Pointer) (adt: RData) : option (RData * Z64) :=
    match g_rd, data_addr, map_addr, g_data, g_src with
    | (_g_rd_base, _g_rd_ofst), VZ64 _data_addr, VZ64 _map_addr, (_g_data_base, _g_data_ofst), (_g_src_base, _g_src_ofst) =>
      rely is_int64 _data_addr;
      rely is_int64 _map_addr;
      when' _t'1, adt == data_create1_spec (_g_rd_base, _g_rd_ofst) (VZ64 _data_addr) (VZ64 _map_addr) (_g_data_base, _g_data_ofst) (_g_src_base, _g_src_ofst) adt;
      rely is_int64 _t'1;
      Some (adt, (VZ64 _t'1))
     end
    .

End SpecLow.
