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

Section SpecLow.

  Definition handle_ns_smc_spec0 (function_id: Z64) (arg0: Z64) (arg1: Z64) (arg2: Z64) (arg3: Z64) (adt: RData) : option (RData * Z64) :=
    match function_id, arg0, arg1, arg2, arg3 with
    | VZ64 _function_id, VZ64 _arg0, VZ64 _arg1, VZ64 _arg2, VZ64 _arg3 =>
      if (_function_id =? 0) then
        Some (adt, (VZ64 1572864))
      else
        if (_function_id =? 1) then
          rely is_int64 _arg0;
          when' _t'1, adt == smc_granule_delegate_spec (VZ64 _arg0) adt;
          rely is_int64 _t'1;
          Some (adt, (VZ64 _t'1))
        else
          if (_function_id =? 2) then
            rely is_int64 _arg0;
            when' _t'2, adt == smc_granule_undelegate_spec (VZ64 _arg0) adt;
            rely is_int64 _t'2;
            Some (adt, (VZ64 _t'2))
          else
            if (_function_id =? 3) then
              rely is_int64 _arg0;
              rely is_int64 _arg1;
              when' _t'3, adt == smc_realm_create_spec (VZ64 _arg0) (VZ64 _arg1) adt;
              rely is_int64 _t'3;
              Some (adt, (VZ64 _t'3))
            else
              if (_function_id =? 4) then
                rely is_int64 _arg0;
                when' _t'4, adt == smc_realm_destroy_spec (VZ64 _arg0) adt;
                rely is_int64 _t'4;
                Some (adt, (VZ64 _t'4))
              else
                if (_function_id =? 5) then
                  rely is_int64 _arg0;
                  when' _t'5, adt == smc_realm_activate_spec (VZ64 _arg0) adt;
                  rely is_int64 _t'5;
                  Some (adt, (VZ64 _t'5))
                else
                  if (_function_id =? 6) then
                    rely is_int64 _arg0;
                    rely is_int64 _arg1;
                    rely is_int64 _arg2;
                    rely is_int64 _arg3;
                    when' _t'6, adt == smc_rec_create_spec (VZ64 _arg0) (VZ64 _arg1) (VZ64 _arg2) (VZ64 _arg3) adt;
                    rely is_int64 _t'6;
                    Some (adt, (VZ64 _t'6))
                  else
                    if (_function_id =? 7) then
                      rely is_int64 _arg0;
                      when' _t'7, adt == smc_rec_destroy_spec (VZ64 _arg0) adt;
                      rely is_int64 _t'7;
                      Some (adt, (VZ64 _t'7))
                    else
                      if (_function_id =? 8) then
                        rely is_int64 _arg0;
                        rely is_int64 _arg1;
                        rely is_int64 _arg2;
                        rely is_int64 _arg3;
                        when' _t'8, adt == smc_data_create_spec (VZ64 _arg0) (VZ64 _arg1) (VZ64 _arg2) (VZ64 _arg3) adt;
                        rely is_int64 _t'8;
                        Some (adt, (VZ64 _t'8))
                      else
                        if (_function_id =? 9) then
                          rely is_int64 _arg0;
                          rely is_int64 _arg1;
                          when' _t'9, adt == smc_data_destroy_spec (VZ64 _arg0) (VZ64 _arg1) adt;
                          rely is_int64 _t'9;
                          Some (adt, (VZ64 _t'9))
                        else
                          if (_function_id =? 10) then
                            rely is_int64 _arg0;
                            rely is_int64 _arg1;
                            rely is_int64 _arg2;
                            rely is_int64 _arg3;
                            when' _t'10, adt == smc_rtt_create_spec (VZ64 _arg0) (VZ64 _arg1) (VZ64 _arg2) (VZ64 _arg3) adt;
                            rely is_int64 _t'10;
                            Some (adt, (VZ64 _t'10))
                          else
                            if (_function_id =? 11) then
                              rely is_int64 _arg0;
                              rely is_int64 _arg1;
                              rely is_int64 _arg2;
                              rely is_int64 _arg3;
                              when' _t'11, adt == smc_rtt_destroy_spec (VZ64 _arg0) (VZ64 _arg1) (VZ64 _arg2) (VZ64 _arg3) adt;
                              rely is_int64 _t'11;
                              Some (adt, (VZ64 _t'11))
                            else
                              if (_function_id =? 12) then
                                rely is_int64 _arg0;
                                rely is_int64 _arg1;
                                when' _t'12, adt == smc_rec_run_spec (VZ64 _arg0) (VZ64 _arg1) adt;
                                rely is_int64 _t'12;
                                Some (adt, (VZ64 _t'12))
                              else
                                if (_function_id =? 13) then
                                  rely is_int64 _arg0;
                                  rely is_int64 _arg1;
                                  rely is_int64 _arg2;
                                  when' _t'13, adt == smc_rtt_map_spec (VZ64 _arg0) (VZ64 _arg1) (VZ64 _arg2) adt;
                                  rely is_int64 _t'13;
                                  Some (adt, (VZ64 _t'13))
                                else
                                  if (_function_id =? 14) then
                                    rely is_int64 _arg0;
                                    rely is_int64 _arg1;
                                    rely is_int64 _arg2;
                                    when' _t'14, adt == smc_rtt_unmap_spec (VZ64 _arg0) (VZ64 _arg1) (VZ64 _arg2) adt;
                                    rely is_int64 _t'14;
                                    Some (adt, (VZ64 _t'14))
                                  else
                                    when adt == assert_cond_spec 0 adt;
                                    Some (adt, (VZ64 0))
     end
    .

End SpecLow.
