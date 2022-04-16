Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition access_in_par_spec (rec: Pointer) (address: Z64) (esr: Z64) (adt: RData) : option Z :=
    match address, esr with
    | VZ64 address, VZ64 esr =>
      rely is_int64 address; rely is_int64 esr;
      rely (peq (base rec) buffer_loc);
      when gidx == (buffer (priv adt)) @ (offset rec);
      let gn := (gs (share adt)) @ gidx in
      rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
      rely (ref_accessible gn CPU_ID);
      let len := __access_len esr in
      let par_base := g_rec_par_base (grec gn) in
      let par_end := g_rec_par_end (grec gn) in
      rely is_int len; rely is_int64 par_base; rely is_int64 par_end;
      rely is_int64 (address + len);
      if (address + len >? par_base) && (address <? par_end) then
        Some 1
      else
        Some 0
    end.

End Spec.

