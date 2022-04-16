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

  Definition data_destroy3_spec0 (g_rd: Pointer) (map_addr: Z64) (adt: RData) : option (RData * Z64) :=
    match g_rd, map_addr with
    | (_g_rd_base, _g_rd_ofst), VZ64 _map_addr =>
      rely is_int64 _map_addr;
      when' _t'1, adt == data_destroy2_spec (_g_rd_base, _g_rd_ofst) (VZ64 _map_addr) adt;
      rely is_int64 _t'1;
      Some (adt, (VZ64 _t'1))
     end
    .

End SpecLow.
