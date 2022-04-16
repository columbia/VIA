Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition get_realm_params_spec0 (realm_params_addr: Z64) (adt: RData) : option (RData * Z) :=
    match realm_params_addr with
    | VZ64 _realm_params_addr =>
      rely is_int64 _realm_params_addr;
      when'' _g_realm_params_base, _g_realm_params_ofst == find_granule_spec (VZ64 _realm_params_addr) adt;
      rely is_int _g_realm_params_ofst;
      when _t'3 == is_null_spec (_g_realm_params_base, _g_realm_params_ofst) adt;
      rely is_int _t'3;
      if (_t'3 =? 1) then
        let _ret := 1 in
        Some (adt, _ret)
      else
        when adt == ns_granule_map_spec 0 (_g_realm_params_base, _g_realm_params_ofst) adt;
        when _ret, adt == ns_buffer_read_realm_params_spec 0 adt;
        rely is_int _ret;
        when adt == ns_buffer_unmap_spec 0 adt;
        Some (adt, _ret)
     end
    .

End SpecLow.
