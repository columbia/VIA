Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition table_maps_block_spec (table: Pointer) (level: Z64) (ipa_state: Z64) (adt: RData) : option Z :=
    match level, ipa_state with
    | VZ64 level, VZ64 ipa_state =>
      rely is_int64 level; rely is_int64 ipa_state; rely (level >? 0);
      rely peq (base table) buffer_loc;
      when gidx == (buffer (priv adt)) @ (offset table);
      let gn := (gs (share adt)) @ gidx in
      rely prop_dec (glock gn = Some CPU_ID);
      rely g_tag (ginfo gn) =? GRANULE_STATE_TABLE;
      rely prop_dec (forall i, is_int64 ((g_data (gnorm gn)) @ i) = true);
      let pgte := (g_data (gnorm gn)) @ 0 in
      let base_pa := __entry_to_phys pgte level in
      rely is_int64 base_pa; rely is_int64 (base_pa + PGTES_PER_TABLE * GRANULE_SIZE);
      if __addr_is_level_aligned base_pa (level - 1) then
        Some (if prop_dec (forall i (Hi: 0 <= i < PGTES_PER_TABLE),
                        let e := (g_data (gnorm gn)) @ i in
                        let pa := __entry_to_phys e level in
                        PTE_TO_IPA_STATE e = ipa_state /\ pa = base_pa + i * GRANULE_SIZE)
              then 1 else 0)
      else Some 0
    end.

End Spec.
