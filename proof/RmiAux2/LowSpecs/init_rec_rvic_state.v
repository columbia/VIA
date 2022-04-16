Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Fixpoint init_rec_rvic_state_loop0 (n: nat) (i: Z) (rec: Pointer) (adt: RData) :=
    match n with
    | O => Some (adt, i)
    | S n' =>
      match init_rec_rvic_state_loop0 n' i rec adt with
      | Some (adt, i) =>
        rely is_int i;
        when adt == set_rvic_mask_bits_spec rec i (VZ64 U64MAX) adt;
        Some (adt, i + 1)
      | _ => None
      end
    end.

  Definition init_rec_rvic_state_spec0 (rec: Pointer) (adt: RData) : option RData :=
    match init_rec_rvic_state_loop0 (Z.to_nat 8) 0 rec adt with
    | Some (adt, i) =>
      rely is_int i;
      Some adt
    | _ => None
    end.

End SpecLow.
