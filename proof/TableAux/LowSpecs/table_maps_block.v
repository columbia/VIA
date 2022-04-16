Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Fixpoint table_maps_block_loop0 n i ret table base_pa level ipa_state adt :=
    match n with
    | O => Some (i, ret)
    | S n' =>
      match table_maps_block_loop0 n' i ret table base_pa level ipa_state adt with
      | Some (i, ret) =>
        rely is_int64 i; rely is_int ret;
        when' pgte == pgte_read_spec table (VZ64 i) adt;
        rely is_int64 pgte;
        let expected_pa := base_pa + i * GRANULE_SIZE in
        rely is_int64 expected_pa;
        if PTE_TO_IPA_STATE pgte =? ipa_state then
          when' phys == entry_to_phys_spec (VZ64 pgte) (VZ64 level) adt;
          rely is_int64 phys;
          if phys =? expected_pa then
            Some (i + 1, ret)
          else
            Some (i + 1, 0)
        else Some (i + 1, 0)
      | _ => None
      end
    end.

  Definition table_maps_block_spec0 (table: Pointer) (level: Z64) (ipa_state: Z64) (adt: RData) : option Z :=
    match level, ipa_state with
    | VZ64 level, VZ64 ipa_state =>
      rely is_int64 level; rely is_int64 ipa_state;
      when' pgte == pgte_read_spec table (VZ64 0) adt;
      rely is_int64 pgte;
      when' base_pa == entry_to_phys_spec (VZ64 pgte) (VZ64 level) adt;
      rely is_int64 base_pa; rely is_int64 (level - 1);
      when aligned == addr_is_level_aligned_spec (VZ64 base_pa) (VZ64 (level - 1)) adt;
      rely is_int aligned;
      if aligned =? 0 then Some 0 else
        match table_maps_block_loop0 (Z.to_nat PGTES_PER_TABLE) 0 1 table base_pa level ipa_state adt with
        | Some (i, ret) =>
          rely is_int64 i; rely is_int ret;
          Some ret
        | _ => None
        end
    end.

End SpecLow.
