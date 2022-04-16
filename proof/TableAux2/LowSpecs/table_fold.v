Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import TableAux.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition table_fold_spec0 (table: Pointer) (level: Z64) (g_tbl: Pointer) (adt: RData) : option (RData * Z64) :=
    match table, level, g_tbl with
    | (_table_base, _table_ofst), VZ64 _level, (_g_tbl_base, _g_tbl_ofst) =>
      let _new_pgte := 0 in
      when' _pgte == pgte_read_spec (_table_base, _table_ofst) (VZ64 0) adt;
      rely is_int64 _pgte;
      rely is_int64 (Z.land _pgte 504403158265495552);
      rely is_int64 ((Z.land _pgte 504403158265495552) / 72057594037927936);
      let _ipa_state := ((Z.land _pgte 504403158265495552) / 72057594037927936) in
      rely is_int64 (_level - 1);
      when' _base_pa == entry_to_phys_spec (VZ64 _pgte) (VZ64 (_level - 1)) adt;
      rely is_int64 _base_pa;
      if (negb (_level =? 3)) then
        when adt == assert_cond_spec 0 adt;
        Some (adt, (VZ64 _new_pgte))
      else
        rely is_int64 _level;
        rely is_int64 _ipa_state;
        when _t'3 == table_maps_block_spec (_table_base, _table_ofst) (VZ64 _level) (VZ64 _ipa_state) adt;
        rely is_int _t'3;
        if (_t'3 =? 0) then
          when adt == assert_cond_spec 0 adt;
          Some (adt, (VZ64 _new_pgte))
        else
          rely is_int64 (_ipa_state * 72057594037927936);
          rely is_int64 (Z.lor (_ipa_state * 72057594037927936) _base_pa);
          let _new_pgte := (Z.lor (_ipa_state * 72057594037927936) _base_pa) in
          if (_ipa_state =? 2) then
            rely is_int64 (Z.lor _new_pgte 2009);
            let _new_pgte := (Z.lor _new_pgte 2009) in
            when adt == granule_refcount_dec_spec (_g_tbl_base, _g_tbl_ofst) (VZ64 512) adt;
            Some (adt, (VZ64 _new_pgte))
          else
            rely is_int64 (Z.lor _new_pgte 0);
            let _new_pgte := (Z.lor _new_pgte 0) in
            when adt == granule_refcount_dec_spec (_g_tbl_base, _g_tbl_ofst) (VZ64 512) adt;
            Some (adt, (VZ64 _new_pgte))
     end
    .

End SpecLow.
