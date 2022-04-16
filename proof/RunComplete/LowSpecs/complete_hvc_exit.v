Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RunAux.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Fixpoint complete_hvc_exit_loop0 (n: nat) (i: Z) rec_base rec_ofst adt :=
    match n with
    | O => Some (i, adt)
    | S n' =>
        match complete_hvc_exit_loop0 n' i rec_base rec_ofst adt with
        | Some (i, adt) =>
          rely is_int i;
          when' gpr == get_rec_run_gprs_spec i adt;
          rely is_int64 gpr;
          when adt == set_rec_regs_spec (rec_base, rec_ofst) i (VZ64 gpr) adt;
          Some (i + 1, adt)
        | _ => None
        end
    end.

  Definition complete_hvc_exit_spec0 (rec: Pointer) (adt: RData) : option RData :=
    match rec with
    | (rec_base, rec_ofst) =>
      when' esr == get_rec_last_run_info_esr_spec (rec_base, rec_ofst) adt;
      rely is_int64 esr;
      if (Z.land esr ESR_EL2_EC_MASK) =? ESR_EL2_EC_HVC then
        match complete_hvc_exit_loop0 (Z.to_nat REC_RUN_HVC_NR_GPRS) 0 rec_base rec_ofst adt with
        | Some (i, adt) =>
          rely is_int i;
          when adt == reset_last_run_info_spec (rec_base, rec_ofst) adt;
          Some adt
        | _ => None
        end
      else Some adt
    end.

End SpecLow.
