Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.

Local Open Scope Z_scope.

Section Spec.

  Definition psci_cpu_off_spec (rec: Pointer) (adt: RData) : option RData :=
    rely (peq (base rec) buffer_loc);
    when gidx == ((buffer (priv adt)) @ (offset rec));
    let gn := (gs (share adt)) @ gidx in
    rely g_tag (ginfo gn) =? GRANULE_STATE_REC;
    rely prop_dec (glock gn = Some CPU_ID);
    let g' := gn {gnorm : (gnorm gn) {g_runnable : 0}} in
    Some adt {priv: (priv adt) {psci_forward_psci_call: 1} {psci_x0: PSCI_RETURN_SUCCESS}}
         {share : (share adt) {gs : (gs (share adt)) # gidx == g'}}.

End Spec.

