Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import CtxtSwitch.Spec.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition rec_run_loop_spec (rec: Pointer) (adt: RData) : option RData :=
    match rec with
    | (_rec_base, _rec_ofst) =>
      when adt == save_ns_state_spec  adt;
      when adt == restore_realm_state_spec (_rec_base, _rec_ofst) adt;
      when adt == configure_realm_stage2_spec (_rec_base, _rec_ofst) adt;
      when adt == restore_hcr_el2_spec (_rec_base, _rec_ofst) adt;
      when adt == run_realm_spec (_rec_base, _rec_ofst) adt;
      Some adt
     end
    .

End Spec.

