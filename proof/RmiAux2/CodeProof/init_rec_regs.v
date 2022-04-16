Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiAux.Spec.
Require Import RmiAux.Layer.
Require Import RmiAux2.Code.init_rec_regs.

Require Import RmiAux2.LowSpecs.init_rec_regs.

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
    _get_rec_params_gprs ↦ gensem get_rec_params_gprs_spec
      ⊕ _set_rec_regs ↦ gensem set_rec_regs_spec
      ⊕ _get_rec_params_pc ↦ gensem get_rec_params_pc_spec
      ⊕ _set_rec_pc ↦ gensem set_rec_pc_spec
      ⊕ _set_rec_pstate ↦ gensem set_rec_pstate_spec
      ⊕ _init_rec_sysregs ↦ gensem init_rec_sysregs_spec
      ⊕ _init_common_sysregs ↦ gensem init_common_sysregs_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_get_rec_params_gprs: block.
    Hypothesis h_get_rec_params_gprs_s : Genv.find_symbol ge _get_rec_params_gprs = Some b_get_rec_params_gprs.
    Hypothesis h_get_rec_params_gprs_p : Genv.find_funct_ptr ge b_get_rec_params_gprs
                                         = Some (External (EF_external _get_rec_params_gprs
                                                          (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                                (Tcons tuint Tnil) tulong cc_default).
    Local Opaque get_rec_params_gprs_spec.

    Variable b_set_rec_regs: block.
    Hypothesis h_set_rec_regs_s : Genv.find_symbol ge _set_rec_regs = Some b_set_rec_regs.
    Hypothesis h_set_rec_regs_p : Genv.find_funct_ptr ge b_set_rec_regs
                                  = Some (External (EF_external _set_rec_regs
                                                   (signature_of_type (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                         (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque set_rec_regs_spec.

    Variable b_get_rec_params_pc: block.
    Hypothesis h_get_rec_params_pc_s : Genv.find_symbol ge _get_rec_params_pc = Some b_get_rec_params_pc.
    Hypothesis h_get_rec_params_pc_p : Genv.find_funct_ptr ge b_get_rec_params_pc
                                       = Some (External (EF_external _get_rec_params_pc
                                                        (signature_of_type Tnil tulong cc_default))
                                              Tnil tulong cc_default).
    Local Opaque get_rec_params_pc_spec.

    Variable b_set_rec_pc: block.
    Hypothesis h_set_rec_pc_s : Genv.find_symbol ge _set_rec_pc = Some b_set_rec_pc.
    Hypothesis h_set_rec_pc_p : Genv.find_funct_ptr ge b_set_rec_pc
                                = Some (External (EF_external _set_rec_pc
                                                 (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                       (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_rec_pc_spec.

    Variable b_set_rec_pstate: block.
    Hypothesis h_set_rec_pstate_s : Genv.find_symbol ge _set_rec_pstate = Some b_set_rec_pstate.
    Hypothesis h_set_rec_pstate_p : Genv.find_funct_ptr ge b_set_rec_pstate
                                    = Some (External (EF_external _set_rec_pstate
                                                     (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                           (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_rec_pstate_spec.

    Variable b_init_rec_sysregs: block.
    Hypothesis h_init_rec_sysregs_s : Genv.find_symbol ge _init_rec_sysregs = Some b_init_rec_sysregs.
    Hypothesis h_init_rec_sysregs_p : Genv.find_funct_ptr ge b_init_rec_sysregs
                                      = Some (External (EF_external _init_rec_sysregs
                                                       (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                             (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque init_rec_sysregs_spec.

    Variable b_init_common_sysregs: block.
    Hypothesis h_init_common_sysregs_s : Genv.find_symbol ge _init_common_sysregs = Some b_init_common_sysregs.
    Hypothesis h_init_common_sysregs_p : Genv.find_funct_ptr ge b_init_common_sysregs
                                         = Some (External (EF_external _init_common_sysregs
                                                          (signature_of_type (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default))
                                                (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque init_common_sysregs_spec.

    Lemma init_rec_regs_body_correct:
      forall m d d' env le rec_base rec_offset mpidr rd_base rd_offset
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTmpidr: PTree.get _mpidr le = Some (Vlong mpidr))
             (HPTrd: PTree.get _rd le = Some (Vptr rd_base (Int.repr rd_offset)))
             (Hspec: init_rec_regs_spec0 (rec_base, rec_offset) (VZ64 (Int64.unsigned mpidr)) (rd_base, rd_offset) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) init_rec_regs_body E0 le' (m, d') Out_normal).
    Proof.
      Local Opaque get_rec_params_gprs_spec set_rec_regs_spec.
      solve_code_proof Hspec init_rec_regs_body; try solve [eexists; solve_proof_low].
      get_loop_body. clear_hyp.
      set (Hloop := C).
      remember (PTree.set _i (Vint (Int.repr 0)) le)  as le_loop.
      remember 8 as num.
      set (P := fun le0 m0 => m0 = (m, d) /\ le0 = le_loop).
      set (Q := fun (le0: temp_env) m0 => m0 = (m, r) /\
                                       le0 ! _rec = Some (Vptr rec_base (Int.repr rec_offset)) /\
                                       le0 ! _mpidr = Some (Vlong mpidr) /\
                                       le0 ! _rd = Some (Vptr rd_base (Int.repr rd_offset))).
      set (Inv := fun le0 m0 n => exists i' adt1,
                      init_rec_sysregs_loop0 (Z.to_nat (num - n)) 0 (rec_base, rec_offset) d
                      = Some (Int.unsigned i', adt1) /\ Int.unsigned i' = num - n /\
                      m0 = (m, adt1) /\ 0 <= n /\ n <= num /\ le0 ! _i = Some (Vint i') /\
                      le0 ! _rec = Some (Vptr rec_base (Int.repr rec_offset)) /\
                      le0 ! _mpidr = Some (Vlong mpidr) /\
                      le0 ! _rd = Some (Vptr rd_base (Int.repr rd_offset))).
      assert(loop_succ: forall N, Z.of_nat N <= num -> exists i' adt',
                  init_rec_sysregs_loop0 (Z.to_nat (num - Z.of_nat N)) 0 (rec_base, rec_offset) d
                  = Some (Int.unsigned i', adt')).
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
        - intros ? ? ? I. unfold Inv in I. destruct I as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?).
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
              rewrite H10, H11 in *; eexists; eexists; split. solve_proof_low.
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
        unfold Q in Post. destruct Post as (Hm' & ? & ? & ?). rewrite Hm' in exec.
        eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
