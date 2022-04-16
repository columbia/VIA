Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RVIC2.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition need_ns_notify_spec0 (rec: Pointer) (target_rec: Pointer) (intid: Z64) (adt: RData) : option Z :=
    match rec, target_rec, intid with
    | (_rec_base, _rec_ofst), (_target_rec_base, _target_rec_ofst), VZ64 _intid =>
      when' _idx1 == get_rec_rec_idx_spec (_target_rec_base, _target_rec_ofst) adt;
      rely is_int64 _idx1;
      when' _idx2 == get_rec_rec_idx_spec (_rec_base, _rec_ofst) adt;
      rely is_int64 _idx2;
      if (_idx1 =? _idx2) then
        Some 0
      else
        when _enabled == get_rec_rvic_enabled_spec (_target_rec_base, _target_rec_ofst) adt;
        rely is_int _enabled;
        if (_enabled =? 0) then
          Some 0
        else
          when'' _rvic_base, _rvic_ofst == get_rec_rvic_spec (_target_rec_base, _target_rec_ofst) adt;
          rely is_int _rvic_ofst;
          rely is_int64 _intid;
          when _pending == rvic_is_pending_spec (_rvic_base, _rvic_ofst) (VZ64 _intid) adt;
          rely is_int _pending;
          if (_pending =? 0) then
            Some 0
          else
            when _masked == rvic_is_masked_spec (_rvic_base, _rvic_ofst) (VZ64 _intid) adt;
            rely is_int _masked;
            if (_masked =? 1) then
              Some 0
            else
              Some 1
     end
    .

End SpecLow.
