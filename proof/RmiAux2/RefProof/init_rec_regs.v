Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import RmiAux.Spec.
Require Import RmiAux2.Specs.init_rec_regs.
Require Import RmiAux2.LowSpecs.init_rec_regs.
Require Import RmiAux2.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       get_rec_params_gprs_spec
       set_rec_regs_spec
       get_rec_params_pc_spec
       set_rec_pc_spec
       set_rec_pstate_spec
       init_rec_sysregs_spec
       init_common_sysregs_spec
    .

  Lemma init_rec_regs_spec_exists:
    forall habd habd'  labd rec mpidr rd
           (Hspec: init_rec_regs_spec rec mpidr rd habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', init_rec_regs_spec0 rec mpidr rd labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. inv id_rdata. destruct rec, rd.
    unfold init_rec_regs_spec0, init_rec_regs_spec in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; extract_prop_dec; simpl in *.
    autounfold; try unfold ref_accessible in *; simpl in *.
    repeat (
        repeat
          match goal with
          | [|-context[ZMap.get ?key (ZMap.set ?key ?val ?map)]] => rewrite ZMap.gss
          | [|-context[ZMap.set ?key ?val2 (ZMap.set ?key ?val ?map)]] => rewrite ZMap.set2
          | |- context [?f (?f ?a ?b) ?bb] => replace (f (f a b) bb) with (f a bb) by reflexivity; simpl
          end;
        try simpl_loop_add; repeat simpl_update_reg; repeat grewrite; try rewrite Prop0; simpl).
    rewrite ZMap.gso. repeat (simpl_htarget; grewrite).
    eexists; split. reflexivity. constructor; reflexivity.
    red; intro T; inv T; bool_rel; srewrite. inv C6.
  Qed.

End Refine.

