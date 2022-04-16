Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiAux.Layer.
Require Import RmiAux2.Code.init_rec_rvic_state.

Require Import RmiAux2.LowSpecs.init_rec_rvic_state.

Local Open Scope Z_scope.

Section CodeProof.

  Context `{real_params: RealParams}.
  Context {memb} `{Hmemx: Mem.MemoryModelX memb}.
  Context `{Hmwd: UseMemWithData memb}.

  Let mem := mwd (cdata RData).

  Context `{Hstencil: Stencil}.
  Context `{make_program_ops: !MakeProgramOps Clight.function type Clight.fundef type}.
  Context `{Hmake_program: !MakeProgram Clight.function type Clight.fundef type}.

  Let L : compatlayer (cdata RData) :=
    _set_rvic_mask_bits ↦ gensem set_rvic_mask_bits_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_set_rvic_mask_bits: block.
    Hypothesis h_set_rvic_mask_bits_s : Genv.find_symbol ge _set_rvic_mask_bits = Some b_set_rvic_mask_bits.
    Hypothesis h_set_rvic_mask_bits_p : Genv.find_funct_ptr ge b_set_rvic_mask_bits
                                        = Some (External (EF_external _set_rvic_mask_bits
                                                         (signature_of_type (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                               (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque set_rvic_mask_bits_spec.

    Lemma init_rec_rvic_state_body_correct:
      forall m d d' env le rvic_base rvic_offset
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrvic: PTree.get _rvic le = Some (Vptr rvic_base (Int.repr rvic_offset)))
             (Hspec: init_rec_rvic_state_spec0 (rvic_base, rvic_offset) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) init_rec_rvic_state_body E0 le' (m, d') Out_normal).
    Proof.
      Local Opaque set_rvic_mask_bits_spec.
      solve_code_proof Hspec init_rec_rvic_state_body; try solve [eexists; solve_proof_low].
      get_loop_body. clear_hyp.
      set (Hloop := C).
      remember (PTree.set _i (Vint (Int.repr 0)) le)  as le_loop.
      remember 8 as num.
      set (P := fun le0 m0 => m0 = (m, d) /\ le0 = le_loop).
      set (Q := fun (le0: temp_env) m0 => m0 = (m, d')).
      set (Inv := fun le0 m0 n => exists i' adt1,
                      init_rec_rvic_state_loop0 (Z.to_nat (num - n)) 0 (rvic_base, rvic_offset) d
                      = Some (adt1, Int.unsigned i') /\ Int.unsigned i' = num - n /\
                      m0 = (m, adt1) /\ 0 <= n /\ n <= num /\ le0 ! _i = Some (Vint i') /\
                      le0 ! _rvic = Some (Vptr rvic_base (Int.repr rvic_offset))).
      assert(loop_succ: forall N, Z.of_nat N <= num -> exists i' adt',
                  init_rec_rvic_state_loop0 (Z.to_nat (num - Z.of_nat N)) 0 (rvic_base, rvic_offset) d
                  = Some (adt', Int.unsigned i')).

      { add_int Hloop z; try somega.
        induction N. rewrite Z.sub_0_r. rewrite Hloop. intros. repeat eexists; reflexivity.
        intros. erewrite loop_ind_sub1 in IHN; try omega.
        rewrite Nat2Z.inj_succ, succ_plus_1 in H.
        assert(Hcc: Z.of_nat N <= num) by omega.
        apply IHN in Hcc. destruct Hcc as (? & ? & Hnext).
        Local Opaque Z.of_nat. simpl in Hnext. clear Heqle_loop.
        simpl_func Hnext; try add_int' z0; repeat eexists; try somega. }
      assert (T: LoopProofSimpleWhile.t (external_calls_ops := CompatExternalCalls.compatlayer_extcall_ops L) cond body ge (PTree.empty _) P Q).
      { apply LoopProofSimpleWhile.make with (W:=Z) (lt:=fun z1 z2 => (0 <= z2 /\ z1 < z2)) (I:=Inv).
        - apply Zwf_well_founded.
        - unfold P, Inv. intros ? ? CC. destruct CC as [CC1 CC2].
          rewrite CC2 in *. exists num.
          replace (num - num) with 0 by omega. simpl. add_int' 0; try somega.
          rewrite Heqnum. rewrite Heqle_loop.
          repeat eexists; first [reflexivity|assumption|solve_proof_low].
        - intros ? ? ? I. unfold Inv in I. destruct I as (? & ? & ? & ? & ? & ? & ? & ? & ?).
          set (Hnow := H).
          rewrite Heqbody, Heqcond in *.
          destruct (n >? 0) eqn:Hn; bool_rel.
          + eexists. eexists. split_and.
            * solve_proof_low.
            * solve_proof_low.
            * intro CC. inversion CC.
            * assert(Hlx: Z.of_nat (Z.to_nat (n-1)) <= num) by (rewrite Z2Nat.id; omega).
              apply loop_succ in Hlx. rewrite Z2Nat.id in Hlx; try omega.
              intro. destruct Hlx as (? & ? & Hnext). duplicate Hnext.
              rewrite loop_nat_sub1 in Hnext; try somega.
              simpl in Hnext. rewrite Hnow in Hnext.
              autounfold in Hnext; repeat simpl_hyp Hnext;
                repeat destruct_con; bool_rel; contra; inversion Hnext.
              rewrite H8, H9 in *; eexists; eexists; split. solve_proof_low.
              exists (n-1); split. split; solve_proof_low.
              solve_proof_low; unfold Inv; repeat eexists; first[eassumption|solve_proof_low].
          + eexists. eexists. split_and.
            * solve_proof_low.
            * solve_proof_low.
            * intro. unfold Q.
              assert (n=0) by omega. clear Heqle_loop. subst.
              sstep. rewrite Hloop in Hnow. inv Hnow.
              split_and; first[reflexivity|solve_proof_low].
            * intro CC. inversion CC. }
        assert (Pre: P le_loop (m, d)) by (split; reflexivity).
        pose proof (LoopProofSimpleWhile.termination _ _ _ _ _ _ T _ (m, d) Pre) as LoopProof.
        destruct LoopProof as (le' & m' & (exec & Post)).
        unfold exec_stmt in exec. rewrite Heqle_loop in exec.
        unfold Q in Post. rewrite Post in exec.
        eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
