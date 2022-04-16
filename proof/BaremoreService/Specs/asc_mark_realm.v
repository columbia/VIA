Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition asc_mark_realm_spec (addr: Z64) (adt: RData) : option (RData * Z64) :=
    match addr with
    | VZ64 addr =>
      rely is_int64 addr;
      let gidx := __addr_to_gidx addr in
      rely is_int64 (gidx - 1);
      if (1 <=? gidx) && (gidx <=? NR_GRANULES) then
        when adt == query_oracle adt;
        rely prop_dec (((gpt_lk (share adt)) @ gidx) = None);
        let e := EVT CPU_ID (ACQ_GPT gidx) in
        if ((gpt (share adt)) @ gidx) then
          let e' := EVT CPU_ID (REL_GPT gidx true) in
          Some (adt {log: e' :: e :: (log adt)}, VZ64 1)
        else
          let e' := EVT CPU_ID (REL_GPT gidx true) in
          let gpt' := (gpt (share adt)) # gidx == true in
          Some (adt {log: e' :: e :: (log adt)} {share: (share adt) {gpt: gpt'}}, VZ64 0)
      else Some (adt, VZ64 1)
    end.

End Spec.

