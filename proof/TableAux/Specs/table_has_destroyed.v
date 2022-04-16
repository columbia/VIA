Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition table_has_destroyed_spec (table: Pointer) (adt: RData) : option Z :=
    rely peq (base table) buffer_loc;
    when gidx == (buffer (priv adt)) @ (offset table);
    let gn := (gs (share adt)) @ gidx in
    rely prop_dec (glock gn = Some CPU_ID);
    rely g_tag (ginfo gn) =? GRANULE_STATE_TABLE;
    rely prop_dec (forall i, is_int64 ((g_data (gnorm gn)) @ i) = true);
    Some (if prop_dec (exists i, 0 <= i < PGTES_PER_TABLE /\ PTE_TO_IPA_STATE ((g_data (gnorm gn)) @ i) = IPA_STATE_DESTROYED) then 1 else 0).

End Spec.

