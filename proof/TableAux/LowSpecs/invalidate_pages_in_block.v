Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition invalidate_pages_in_block_spec0 (addr: Z64) (adt: RData) : option RData :=
    match addr with
    | VZ64 _addr =>
      when adt == barrier_spec  adt;
      rely is_int64 _addr;
      when adt == stage2_tlbi_ipa_spec (VZ64 _addr) (VZ64 2097152) adt;
      Some adt
     end
    .

End SpecLow.
