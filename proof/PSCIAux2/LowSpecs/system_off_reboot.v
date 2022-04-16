Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PSCIAux.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Fixpoint system_off_reboot_loop0 (n: nat) (i: Z) (idx: Z) (g_rd: Pointer) (rec_list: Pointer) (adt: RData) :=
    match n with
    | O => Some (adt, i)
    | S n' =>
      match system_off_reboot_loop0 n' i idx g_rd rec_list adt with
      | Some (adt, i) =>
        rely is_int64 i;
        if i =? idx then
          Some (adt, i + 1)
        else
          when g_target_rec, adt == find_lock_rec_spec g_rd rec_list (VZ64 i) adt;
          when null == is_null_spec g_target_rec adt;
          rely is_int null;
          if null =? 0 then
            when t_rec, adt == granule_map_spec g_target_rec SLOT_REC_TARGET adt;
            when adt == set_rec_runnable_spec t_rec 0 adt;
            when adt == buffer_unmap_spec t_rec adt;
            when adt == granule_unlock_spec g_target_rec adt;
            Some (adt, i + 1)
        else Some (adt, i + 1)
      | _ => None
      end
    end.

  Definition system_off_reboot_spec0 (rec: Pointer) (adt: RData) : option RData :=
    when g_rec == get_rec_g_rec_spec rec adt;
	  when g_rd == get_rec_g_rd_spec rec adt;
	  when' idx == get_rec_rec_idx_spec rec adt;
    when g == get_rec_g_rec_list_spec rec adt;
    when adt == granule_lock_spec g_rec adt;
	  when adt == set_rec_runnable_spec rec 0 adt;
	  when adt == granule_unlock_spec g_rec adt;
    when rec_list, adt == granule_map_spec g SLOT_REC_LIST adt;
    match system_off_reboot_loop0 (Z.to_nat MAX_NUM_RECS) 0 idx g_rd rec_list adt with
    | Some (adt, i) =>
      rely is_int64 i;
      Some adt
    | _ => None
    end.


End SpecLow.
