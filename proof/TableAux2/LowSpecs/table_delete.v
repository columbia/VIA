Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import TableAux.Spec.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition table_delete_spec0 (table: Pointer) (g_llt: Pointer) (adt: RData) : option (RData * Z64) :=
    match table, g_llt with
    | (_table_base, _table_ofst), (_g_llt_base, _g_llt_ofst) =>
      when _t'1 == table_has_destroyed_spec (_table_base, _table_ofst) adt;
      rely is_int _t'1;
      if (_t'1 =? 1) then
        let _ipa_state := 3 in
        rely is_int64 (_ipa_state * 72057594037927936);
        rely is_int64 (Z.lor (_ipa_state * 72057594037927936) 0);
        let _new_pgte := (Z.lor (_ipa_state * 72057594037927936) 0) in
        when adt == granule_put_spec (_g_llt_base, _g_llt_ofst) adt;
        Some (adt, (VZ64 _new_pgte))
      else
        let _ipa_state := 0 in
        rely is_int64 (_ipa_state * 72057594037927936);
        rely is_int64 (Z.lor (_ipa_state * 72057594037927936) 0);
        let _new_pgte := (Z.lor (_ipa_state * 72057594037927936) 0) in
        when adt == granule_put_spec (_g_llt_base, _g_llt_ofst) adt;
        Some (adt, (VZ64 _new_pgte))
     end
    .

End SpecLow.
