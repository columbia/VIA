Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition valid_realm_params base size :=
    (GRANULE_ALIGNED base) && (GRANULE_ALIGNED size) && (base + size >? base) && (base + size <? IPA_SIZE).

  Definition validate_realm_params_spec  (adt: RData) : option Z64 :=
    let base := ((realm_params (priv adt)) @ 0) in
    let size := ((realm_params (priv adt)) @ 1) in
    rely is_int64 base; rely is_int64 size; rely is_int64 (base + size);
    if valid_realm_params base size then
      Some (VZ64 0)
    else
      Some (VZ64 1).

End Spec.

