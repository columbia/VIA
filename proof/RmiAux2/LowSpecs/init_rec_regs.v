Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiAux.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Fixpoint init_rec_sysregs_loop0 (n: nat) (i: Z) (rec: Pointer) (adt: RData) :=
    match n with
    | O => Some (i, adt)
    | S n' =>
      match init_rec_sysregs_loop0 n' i rec adt with
      | Some (i, adt) =>
        rely is_int i;
        when' par == get_rec_params_gprs_spec i adt;
        rely is_int64 par;
        when adt == set_rec_regs_spec rec i (VZ64 par) adt;
        Some (i + 1, adt)
      | _ => None
      end
    end.

  Definition init_rec_regs_spec0 (rec: Pointer) (mpidr: Z64) (rd: Pointer) (adt: RData) : option RData :=
    match mpidr with
    | VZ64 mpidr =>
      match init_rec_sysregs_loop0 (Z.to_nat 8) 0 rec adt with
      | Some (i, adt) =>
        rely is_int i;
        when' pc == get_rec_params_pc_spec adt;
        rely is_int64 pc;
        when adt == set_rec_pc_spec rec (VZ64 pc) adt;
        when adt == set_rec_pstate_spec rec (VZ64 965) adt;
        when adt == init_rec_sysregs_spec rec (VZ64 mpidr) adt;
        when adt == init_common_sysregs_spec rec rd adt;
        Some adt
      | _ => None
      end
    end.

End SpecLow.
