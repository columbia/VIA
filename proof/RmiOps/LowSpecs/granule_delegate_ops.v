Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import BaremoreSMC.Spec.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition granule_delegate_ops_spec0 (g: Pointer) (addr: Z64) (adt: RData) : option RData :=
    match g, addr with
    | (_g_base, _g_ofst), VZ64 _addr =>
      rely is_int64 _addr;
      when adt == smc_mark_realm_spec (VZ64 _addr) adt;
      when adt == granule_set_state_spec (_g_base, _g_ofst) 1 adt;
      when adt == granule_memzero_spec (_g_base, _g_ofst) 1 adt;
      when adt == granule_unlock_spec (_g_base, _g_ofst) adt;
      Some adt
     end
    .

End SpecLow.
