Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition psci_features_spec (rec: Pointer) (psci_func_id: Z) (adt: RData) : option RData :=
	  if (psci_func_id =? SMC32_PSCI_CPU_SUSPEND)
       || (psci_func_id =? SMC64_PSCI_CPU_SUSPEND)
       || (psci_func_id =? SMC32_PSCI_CPU_OFF)
       || (psci_func_id =? SMC32_PSCI_CPU_ON)
       || (psci_func_id =? SMC64_PSCI_CPU_ON)
       || (psci_func_id =? SMC32_PSCI_AFFINITY_INFO)
       || (psci_func_id =? SMC64_PSCI_AFFINITY_INFO)
       || (psci_func_id =? SMC32_PSCI_SYSTEM_OFF)
       || (psci_func_id =? SMC32_PSCI_SYSTEM_RESET)
       || (psci_func_id =? SMC32_PSCI_FEATURES)
    then
      Some adt {priv : (priv adt) {psci_x0 : 0}}
    else
      Some adt {priv : (priv adt) {psci_x0 :  PSCI_RETURN_NOT_SUPPORTED}}.

End Spec.

