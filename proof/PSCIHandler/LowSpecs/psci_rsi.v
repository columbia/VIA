Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import PSCI.Spec.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition psci_rsi_spec0 (rec: Pointer) (function_id: Z) (arg0: Z64) (arg1: Z64) (arg2: Z64) (adt: RData) : option RData :=
    match rec, function_id, arg0, arg1, arg2 with
    | (_rec_base, _rec_ofst), _function_id, VZ64 _arg0, VZ64 _arg1, VZ64 _arg2 =>
      if (_function_id =? 2214592512) then
        when adt == psci_version_spec (_rec_base, _rec_ofst) adt;
        Some adt
      else
        if (_function_id =? 2214592513) then
          let _t'1 := 1 in
          rely is_int64 _arg0;
          rely is_int64 _arg1;
          when adt == psci_cpu_suspend_spec (_rec_base, _rec_ofst) (VZ64 _arg0) (VZ64 _arg1) adt;
          Some adt
        else
          let _t'1 := (_function_id =? 3288334337) in
          if _t'1 then
            rely is_int64 _arg0;
            rely is_int64 _arg1;
            when adt == psci_cpu_suspend_spec (_rec_base, _rec_ofst) (VZ64 _arg0) (VZ64 _arg1) adt;
            Some adt
          else
            if (_function_id =? 2214592514) then
              when adt == psci_cpu_off_spec (_rec_base, _rec_ofst) adt;
              Some adt
            else
              if (_function_id =? 2214592515) then
                rely is_int _arg0;
                rely is_int64 _arg0;
                let _arg0 := _arg0 in
                rely is_int _arg1;
                rely is_int64 _arg1;
                let _arg1 := _arg1 in
                rely is_int _arg2;
                rely is_int64 _arg2;
                let _arg2 := _arg2 in
                when adt == psci_cpu_on_spec (_rec_base, _rec_ofst) (VZ64 _arg0) (VZ64 _arg1) (VZ64 _arg2) adt;
                Some adt
              else
                if (_function_id =? 3288334339) then
                  rely is_int64 _arg0;
                  rely is_int64 _arg1;
                  rely is_int64 _arg2;
                  when adt == psci_cpu_on_spec (_rec_base, _rec_ofst) (VZ64 _arg0) (VZ64 _arg1) (VZ64 _arg2) adt;
                  Some adt
                else
                  if (_function_id =? 2214592516) then
                    rely is_int _arg0;
                    rely is_int64 _arg0;
                    let _arg0 := _arg0 in
                    rely is_int _arg1;
                    rely is_int64 _arg1;
                    let _arg1 := _arg1 in
                    when adt == psci_affinity_info_spec (_rec_base, _rec_ofst) (VZ64 _arg0) (VZ64 _arg1) adt;
                    Some adt
                  else
                    if (_function_id =? 3288334340) then
                      rely is_int64 _arg0;
                      rely is_int64 _arg1;
                      when adt == psci_affinity_info_spec (_rec_base, _rec_ofst) (VZ64 _arg0) (VZ64 _arg1) adt;
                      Some adt
                    else
                      if (_function_id =? 2214592520) then
                        when adt == psci_system_off_spec (_rec_base, _rec_ofst) adt;
                        Some adt
                      else
                        if (_function_id =? 2214592521) then
                          when adt == psci_system_reset_spec (_rec_base, _rec_ofst) adt;
                          Some adt
                        else
                          if (_function_id =? 2214592522) then
                            rely is_int _arg0;
                            when adt == psci_features_spec (_rec_base, _rec_ofst) _arg0 adt;
                            Some adt
                          else
                            when adt == set_psci_result_x0_spec (VZ64 4294967295) adt;
                            when adt == set_psci_result_forward_psci_call_spec 0 adt;
                            Some adt
     end
    .

End SpecLow.
