Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RmiAux.Specs.init_common_sysregs.
Require Import RmiAux.LowSpecs.init_common_sysregs.
Require Import RmiAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       set_rec_common_sysregs_spec
       get_rd_g_rtt_spec
       granule_addr_spec
    .

  Lemma init_common_sysregs_spec_exists:
    forall habd habd'  labd rec rd
           (Hspec: init_common_sysregs_spec rec rd habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', init_common_sysregs_spec0 rec rd labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. inv id_rdata. destruct rec, rd.
    unfold init_common_sysregs_spec0, init_common_sysregs_spec in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle;
      extract_prop_dec; repeat destruct_con; repeat destruct_dis; bool_rel; simpl in *;
        repeat (simpl_htarget; grewrite; try solve_ptr_eq; try unfold ref_accessible in *; simpl in *).
    rewrite ZMap.gso.
    repeat (simpl_htarget; grewrite; simpl).
    repeat (solve_bool_range; grewrite).
    repeat simpl_field. repeat simpl_update_reg.
    eexists; (split; [reflexivity| constructor; reflexivity]).
    red; intro T; inv T; srewrite. inv C4.
  Qed.

End Refine.

