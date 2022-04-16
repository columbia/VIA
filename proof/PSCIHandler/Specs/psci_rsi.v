Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import PSCI.Spec.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition psci_rsi_spec (rec: Pointer) (function_id: Z) (arg0: Z64) (arg1: Z64) (arg2: Z64) (adt: RData) : option RData :=
    match arg0, arg1, arg2 with
    | VZ64 _arg0, VZ64 _arg1, VZ64 _arg2 =>
      if (function_id =? SMC32_PSCI_VERSION) then
        psci_version_spec rec adt
      else
        if (function_id =? SMC32_PSCI_CPU_SUSPEND) || (function_id =? SMC64_PSCI_CPU_SUSPEND) then
          rely is_int64 _arg0; rely is_int64 _arg1;
          psci_cpu_suspend_spec rec arg0 arg1 adt
        else
          if (function_id =? SMC32_PSCI_CPU_OFF) then
            psci_cpu_off_spec rec adt
          else
            if (function_id =? SMC32_PSCI_CPU_ON) then
              rely is_int _arg0; rely is_int _arg1; rely is_int _arg2;
              psci_cpu_on_spec rec arg0 arg1 arg2 adt
            else
              if (function_id =? SMC64_PSCI_CPU_ON) then
                rely is_int64 _arg0; rely is_int64 _arg1; rely is_int64 _arg2;
                psci_cpu_on_spec rec arg0 arg1 arg2 adt
              else
                if (function_id =? SMC32_PSCI_AFFINITY_INFO) then
                  rely is_int _arg0; rely is_int _arg1;
                  psci_affinity_info_spec rec arg0 arg1 adt
                else
                  if (function_id =? SMC64_PSCI_AFFINITY_INFO) then
                    rely is_int64 _arg0; rely is_int64 _arg1;
                    psci_affinity_info_spec rec arg0 arg1 adt
                  else
                    if (function_id =? SMC32_PSCI_SYSTEM_OFF) then
                      psci_system_off_spec rec adt
                    else
                      if (function_id =? SMC32_PSCI_SYSTEM_RESET) then
                        psci_system_reset_spec rec adt
                      else
                        if (function_id =? SMC32_PSCI_FEATURES) then
                          rely is_int _arg0;
                          psci_features_spec rec _arg0 adt
                        else
                          Some adt {priv: (priv adt) {psci_x0: PSCI_RETURN_NOT_SUPPORTED} {psci_forward_psci_call: 0}}
    end.

End Spec.

