Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition invalidate_pages_in_block_spec (addr: Z64) (adt: RData) : option RData :=
    match addr with
    | VZ64 addr =>
      rely is_int64 addr; rely (GRANULE_ALIGNED addr);
      let ipa_gidx := __addr_to_gidx addr in
      let tlb' := fun cpu gidx => if (gidx >=? ipa_gidx) && (gidx <? ipa_gidx + 512) then -1 else (tlbs (share adt)) cpu gidx in
      Some adt {share: (share adt) {tlbs: tlb'}}
    end.

End Spec.

