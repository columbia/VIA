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

  Definition table_create_init_vacant_spec0 (ipa_state: Z64) (pte: Pointer) (g_llt: Pointer) (adt: RData) : option RData :=
    match ipa_state, pte, g_llt with
    | VZ64 _ipa_state, (_pte_base, _pte_ofst), (_g_llt_base, _g_llt_ofst) =>
      rely is_int64 (_ipa_state * 72057594037927936);
      rely is_int64 (Z.lor (_ipa_state * 72057594037927936) 0);
      when adt == granule_fill_table_spec (_pte_base, _pte_ofst) (VZ64 (Z.lor (_ipa_state * 72057594037927936) 0)) (VZ64 0) adt;
      when adt == granule_get_spec (_g_llt_base, _g_llt_ofst) adt;
      Some adt
     end
    .

End SpecLow.
