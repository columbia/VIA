Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RmiSMC.Spec.
Require Import TableDataOpsIntro.Spec.
Require Import TableDataSMC.Spec.
Require Import RunSMC.Spec.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition handle_ns_smc_spec (function_id: Z64) (arg0: Z64) (arg1: Z64) (arg2: Z64) (arg3: Z64) (adt: RData) : option (RData * Z64) :=
    match function_id, arg0, arg1, arg2, arg3 with
    | VZ64 _function_id, VZ64 _arg0, VZ64 _arg1, VZ64 _arg2, VZ64 _arg3 =>
      rely is_int64 _arg0; rely is_int64 _arg1; rely is_int64 _arg2; rely is_int64 _arg3;
      if (_function_id =? 0) then
        Some (adt, (VZ64 1572864))
      else
        if (_function_id =? 1) then
          smc_granule_delegate_spec (VZ64 _arg0) adt
        else
          if (_function_id =? 2) then
            smc_granule_undelegate_spec (VZ64 _arg0) adt
          else
            if (_function_id =? 3) then
              smc_realm_create_spec (VZ64 _arg0) (VZ64 _arg1) adt
            else
              if (_function_id =? 4) then
                smc_realm_destroy_spec (VZ64 _arg0) adt
              else
                if (_function_id =? 5) then
                  smc_realm_activate_spec (VZ64 _arg0) adt
                else
                  if (_function_id =? 6) then
                    smc_rec_create_spec (VZ64 _arg0) (VZ64 _arg1) (VZ64 _arg2) (VZ64 _arg3) adt
                  else
                    if (_function_id =? 7) then
                      smc_rec_destroy_spec (VZ64 _arg0) adt
                    else
                      if (_function_id =? 8) then
                        smc_data_create_spec (VZ64 _arg0) (VZ64 _arg1) (VZ64 _arg2) (VZ64 _arg3) adt
                      else
                        if (_function_id =? 9) then
                         smc_data_destroy_spec (VZ64 _arg0) (VZ64 _arg1) adt
                        else
                          if (_function_id =? 10) then
                            smc_rtt_create_spec (VZ64 _arg0) (VZ64 _arg1) (VZ64 _arg2) (VZ64 _arg3) adt
                          else
                            if (_function_id =? 11) then
                              smc_rtt_destroy_spec (VZ64 _arg0) (VZ64 _arg1) (VZ64 _arg2) (VZ64 _arg3) adt
                            else
                              if (_function_id =? 13) then
                                smc_rtt_map_spec (VZ64 _arg0) (VZ64 _arg1) (VZ64 _arg2) adt
                              else
                                if (_function_id =? 14) then
                                  smc_rtt_unmap_spec (VZ64 _arg0) (VZ64 _arg1) (VZ64 _arg2) adt
                                else None
     end.

End Spec.

