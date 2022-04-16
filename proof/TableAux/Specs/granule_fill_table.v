Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Fixpoint fill_table (n: nat) (table: ZMap.t Z) (i: Z) (pte_val: Z) (pte_inc: Z) :=
    match n with
    | O => (table, i, pte_val)
    | S n' =>
      match fill_table n' table i pte_val pte_inc with
      | (table, i, pte_val) =>
        (table # i == pte_val, i + 1, pte_val + pte_inc)
      end
    end.

  Definition granule_fill_table_spec (pte: Pointer) (pte_val: Z64) (pte_inc: Z64) (adt: RData) : option RData :=
    match pte_val, pte_inc with
    | VZ64 pte_val, VZ64 pte_inc =>
      rely is_int64 pte_val; rely is_int64 pte_inc; rely is_int64 (pte_val + pte_inc * PGTES_PER_TABLE);
      rely peq (base pte) buffer_loc;
      when gidx == (buffer (priv adt)) @ (offset pte);
      let gn := (gs (share adt)) @ gidx in
      rely prop_dec (glock gn = Some CPU_ID);
      rely g_tag (ginfo gn) =? GRANULE_STATE_TABLE;
      match fill_table (Z.to_nat PGTES_PER_TABLE) (g_data (gnorm gn)) 0 pte_val pte_inc with
      | (data', i', pte_val') =>
        let g' := gn {gnorm : (gnorm gn) {g_data : data'}} in
        Some adt {share : (share adt) {gs : (gs (share adt)) # gidx == g'}}
      end
    end.

End Spec.

