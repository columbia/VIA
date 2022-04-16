Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RmiAux.Spec.
Require Import AbsAccessor.Spec.
Require Import RmiOps.Spec.

Local Open Scope Z_scope.

Section SpecLow.

  Definition smc_realm_create_spec0 (rd_addr: Z64) (realm_params_addr: Z64) (adt: RData) : option (RData * Z64) :=
    match rd_addr, realm_params_addr with
    | VZ64 _rd_addr, VZ64 _realm_params_addr =>
      rely is_int64 _realm_params_addr;
      when _t'5, adt == get_realm_params_spec (VZ64 _realm_params_addr) adt;
      rely is_int _t'5;
      if (_t'5 =? 0) then
        when' _t'4 == validate_realm_params_spec  adt;
        rely is_int64 _t'4;
        if (_t'4 =? 0) then
          when' _rtt_addr == get_realm_params_rtt_addr_spec  adt;
          rely is_int64 _rtt_addr;
          when' _rec_list_addr == get_realm_params_rec_list_addr_spec  adt;
          rely is_int64 _rec_list_addr;
          rely is_int64 _rd_addr;
          when _t'3, adt == find_lock_three_delegated_granules_spec (VZ64 _rd_addr) (VZ64 _rtt_addr) (VZ64 _rec_list_addr) adt;
          rely is_int _t'3;
          if (_t'3 =? 0) then
            when adt == realm_create_ops_spec  adt;
            Some (adt, (VZ64 0))
          else
            Some (adt, (VZ64 1))
        else
          Some (adt, (VZ64 1))
      else
        Some (adt, (VZ64 1))
     end
    .

End SpecLow.
