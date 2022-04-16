Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition handle_excpetion_irq_lel_spec (rec: Pointer) (adt: RData) : option (RData * Z) :=
    let icc_hppir1_el1 := r_icc_hppir1_el1 (cpu_regs (priv adt)) in
    rely is_int64 icc_hppir1_el1;
    let intid := Z.land icc_hppir1_el1 ICC_HPPIR1_EL1_INTID in
    if (intid =? INTID_VTIMER_EL1) || (intid =? INTID_PTIMER_EL1) then
      Some (adt, 1)
    else
      Some (adt {priv: (priv adt) {rec_run: (rec_run (priv adt)) # 0 == EXIT_REASON_IRQ}}, 0).

End Spec.

