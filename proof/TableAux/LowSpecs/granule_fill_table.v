Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Fixpoint granule_fill_table_loop0 n i pte pte_val pte_inc adt :=
    match n with
    | O => Some (i, pte_val, adt)
    | S n' =>
      match granule_fill_table_loop0 n' i pte pte_val pte_inc adt with
      | Some (i, pte_val, adt) =>
        rely is_int64 i; rely is_int64 pte_val;
        when adt == pgte_write_spec pte (VZ64 i) (VZ64 pte_val) adt;
        Some (i + 1, pte_val + pte_inc, adt)
      | _ => None
      end
    end.

  Definition granule_fill_table_spec0 (pte: Pointer) (pte_val: Z64) (pte_inc: Z64) (adt: RData) : option RData :=
    match pte_val, pte_inc with
    | VZ64 pte_val, VZ64 pte_inc =>
      rely is_int64 pte_val; rely is_int64 pte_inc;
      match granule_fill_table_loop0 (Z.to_nat PGTES_PER_TABLE) 0 pte pte_val pte_inc adt with
      | Some (i, pte_val, adt) =>
        rely is_int64 i; rely is_int64 pte_val;
        Some adt
      | _ => None
      end
    end.

End SpecLow.
