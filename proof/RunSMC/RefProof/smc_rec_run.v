Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RunComplete.Spec.
Require Import RunAux.Spec.
Require Import RunLoop.Spec.
Require Import RunSMC.Specs.smc_rec_run.
Require Import RunSMC.LowSpecs.smc_rec_run.
Require Import RunSMC.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       find_granule_spec
       is_null_spec
       find_lock_unused_granule_spec
       granule_get_spec
       atomic_granule_get_spec
       granule_unlock_spec
       granule_map_spec
       ns_granule_map_spec
       ns_buffer_read_rec_run_spec
       ns_buffer_unmap_spec
       buffer_unmap_spec
       granule_put_spec
       atomic_granule_put_release_spec
       atomic_granule_put_spec
       granule_lock_spec
       get_rec_runnable_spec
       complete_mmio_emulation_spec
       complete_hvc_exit_spec
       reset_last_run_info_spec
       reset_disposed_info_spec
       rec_run_loop_spec
  .

  Lemma smc_rec_run_spec_exists:
    forall habd habd'  labd rec_addr rec_run_addr res
           (Hspec: smc_rec_run_spec rec_addr rec_run_addr habd = Some (habd', res))
           (Hrel: relate_RData habd labd),
    exists labd', smc_rec_run_spec0 rec_addr rec_run_addr labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    intros. inv Hrel.
    unfold smc_rec_run_spec, smc_rec_run_spec0 in *.
    rewrite Hspec. eexists; split. reflexivity.
    constructor; reflexivity.
  Qed.

End Refine.

