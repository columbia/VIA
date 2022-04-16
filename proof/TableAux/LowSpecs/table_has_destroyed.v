Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Fixpoint table_has_destroyed_loop0 n i ret table adt :=
    match n with
    | O => Some (i, ret)
    | S n' =>
      match table_has_destroyed_loop0 n' i ret table adt with
      | Some (i, ret) =>
        rely is_int i; rely is_int ret;
        when' pgte == pgte_read_spec table (VZ64 i) adt;
        rely is_int64 pgte;
        if PTE_TO_IPA_STATE pgte =? IPA_STATE_DESTROYED then
          Some (i + 1, 1)
        else
          Some (i + 1, ret)
      | _ => None
      end
    end.

  Definition table_has_destroyed_spec0 (table: Pointer) (adt: RData) : option Z :=
    match table_has_destroyed_loop0 (Z.to_nat PGTES_PER_TABLE) 0 0  table adt with
    | Some (i, ret) =>
      rely is_int i; rely is_int ret;
      Some ret
    | _ => None
    end.

End SpecLow.
