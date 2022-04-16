Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import RmiSMC.Spec.
Require Import TableDataOpsIntro.Spec.
Require Import TableDataSMC.Spec.
Require Import RunSMC.Spec.
Require Import AbsAccessor.Spec.
Require Import TableDataSMC.Layer.
Require Import SMCHandler.Code.handle_ns_smc.

Require Import SMCHandler.LowSpecs.handle_ns_smc.

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
    _smc_granule_delegate ↦ gensem smc_granule_delegate_spec
      ⊕ _smc_granule_undelegate ↦ gensem smc_granule_undelegate_spec
      ⊕ _smc_realm_create ↦ gensem smc_realm_create_spec
      ⊕ _smc_realm_destroy ↦ gensem smc_realm_destroy_spec
      ⊕ _smc_realm_activate ↦ gensem smc_realm_activate_spec
      ⊕ _smc_rec_create ↦ gensem smc_rec_create_spec
      ⊕ _smc_rec_destroy ↦ gensem smc_rec_destroy_spec
      ⊕ _data_create ↦ gensem data_create_spec
      ⊕ _smc_data_create ↦ gensem smc_data_create_spec
      ⊕ _data_destroy ↦ gensem data_destroy_spec
      ⊕ _smc_data_destroy ↦ gensem smc_data_destroy_spec
      ⊕ _smc_rtt_create ↦ gensem smc_rtt_create_spec
      ⊕ _smc_rtt_destroy ↦ gensem smc_rtt_destroy_spec
      ⊕ _smc_rec_run ↦ gensem smc_rec_run_spec
      ⊕ _smc_rtt_map ↦ gensem smc_rtt_map_spec
      ⊕ _smc_rtt_unmap ↦ gensem smc_rtt_unmap_spec
      ⊕ _assert_cond ↦ gensem assert_cond_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_smc_granule_delegate: block.
    Hypothesis h_smc_granule_delegate_s : Genv.find_symbol ge _smc_granule_delegate = Some b_smc_granule_delegate.
    Hypothesis h_smc_granule_delegate_p : Genv.find_funct_ptr ge b_smc_granule_delegate
                                          = Some (External (EF_external _smc_granule_delegate
                                                           (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                                 (Tcons tulong Tnil) tulong cc_default).
    Local Opaque smc_granule_delegate_spec.

    Variable b_smc_granule_undelegate: block.
    Hypothesis h_smc_granule_undelegate_s : Genv.find_symbol ge _smc_granule_undelegate = Some b_smc_granule_undelegate.
    Hypothesis h_smc_granule_undelegate_p : Genv.find_funct_ptr ge b_smc_granule_undelegate
                                            = Some (External (EF_external _smc_granule_undelegate
                                                             (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                                   (Tcons tulong Tnil) tulong cc_default).
    Local Opaque smc_granule_undelegate_spec.

    Variable b_smc_realm_create: block.
    Hypothesis h_smc_realm_create_s : Genv.find_symbol ge _smc_realm_create = Some b_smc_realm_create.
    Hypothesis h_smc_realm_create_p : Genv.find_funct_ptr ge b_smc_realm_create
                                      = Some (External (EF_external _smc_realm_create
                                                       (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
                                             (Tcons tulong (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque smc_realm_create_spec.

    Variable b_smc_realm_destroy: block.
    Hypothesis h_smc_realm_destroy_s : Genv.find_symbol ge _smc_realm_destroy = Some b_smc_realm_destroy.
    Hypothesis h_smc_realm_destroy_p : Genv.find_funct_ptr ge b_smc_realm_destroy
                                       = Some (External (EF_external _smc_realm_destroy
                                                        (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                              (Tcons tulong Tnil) tulong cc_default).
    Local Opaque smc_realm_destroy_spec.

    Variable b_smc_realm_activate: block.
    Hypothesis h_smc_realm_activate_s : Genv.find_symbol ge _smc_realm_activate = Some b_smc_realm_activate.
    Hypothesis h_smc_realm_activate_p : Genv.find_funct_ptr ge b_smc_realm_activate
                                        = Some (External (EF_external _smc_realm_activate
                                                         (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                               (Tcons tulong Tnil) tulong cc_default).
    Local Opaque smc_realm_activate_spec.

    Variable b_smc_rec_create: block.
    Hypothesis h_smc_rec_create_s : Genv.find_symbol ge _smc_rec_create = Some b_smc_rec_create.
    Hypothesis h_smc_rec_create_p : Genv.find_funct_ptr ge b_smc_rec_create
                                    = Some (External (EF_external _smc_rec_create
                                                     (signature_of_type (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tulong cc_default))
                                           (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tulong cc_default).
    Local Opaque smc_rec_create_spec.

    Variable b_smc_rec_destroy: block.
    Hypothesis h_smc_rec_destroy_s : Genv.find_symbol ge _smc_rec_destroy = Some b_smc_rec_destroy.
    Hypothesis h_smc_rec_destroy_p : Genv.find_funct_ptr ge b_smc_rec_destroy
                                     = Some (External (EF_external _smc_rec_destroy
                                                      (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                            (Tcons tulong Tnil) tulong cc_default).
    Local Opaque smc_rec_destroy_spec.

    Variable b_data_create: block.
    Hypothesis h_data_create_s : Genv.find_symbol ge _data_create = Some b_data_create.
    Hypothesis h_data_create_p : Genv.find_funct_ptr ge b_data_create
                                 = Some (External (EF_external _data_create
                                                  (signature_of_type (Tcons Tptr (Tcons tulong (Tcons tulong (Tcons Tptr (Tcons Tptr Tnil))))) tulong cc_default))
                                        (Tcons Tptr (Tcons tulong (Tcons tulong (Tcons Tptr (Tcons Tptr Tnil))))) tulong cc_default).
    Local Opaque data_create_spec.

    Variable b_smc_data_create: block.
    Hypothesis h_smc_data_create_s : Genv.find_symbol ge _smc_data_create = Some b_smc_data_create.
    Hypothesis h_smc_data_create_p : Genv.find_funct_ptr ge b_smc_data_create
                                     = Some (External (EF_external _smc_data_create
                                                      (signature_of_type (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tulong cc_default))
                                            (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tulong cc_default).
    Local Opaque smc_data_create_spec.

    Variable b_data_destroy: block.
    Hypothesis h_data_destroy_s : Genv.find_symbol ge _data_destroy = Some b_data_destroy.
    Hypothesis h_data_destroy_p : Genv.find_funct_ptr ge b_data_destroy
                                  = Some (External (EF_external _data_destroy
                                                   (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tulong cc_default))
                                         (Tcons Tptr (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque data_destroy_spec.

    Variable b_smc_data_destroy: block.
    Hypothesis h_smc_data_destroy_s : Genv.find_symbol ge _smc_data_destroy = Some b_smc_data_destroy.
    Hypothesis h_smc_data_destroy_p : Genv.find_funct_ptr ge b_smc_data_destroy
                                      = Some (External (EF_external _smc_data_destroy
                                                       (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
                                             (Tcons tulong (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque smc_data_destroy_spec.

    Variable b_smc_rtt_create: block.
    Hypothesis h_smc_rtt_create_s : Genv.find_symbol ge _smc_rtt_create = Some b_smc_rtt_create.
    Hypothesis h_smc_rtt_create_p : Genv.find_funct_ptr ge b_smc_rtt_create
                                    = Some (External (EF_external _smc_rtt_create
                                                     (signature_of_type (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tulong cc_default))
                                           (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tulong cc_default).
    Local Opaque smc_rtt_create_spec.

    Variable b_smc_rtt_destroy: block.
    Hypothesis h_smc_rtt_destroy_s : Genv.find_symbol ge _smc_rtt_destroy = Some b_smc_rtt_destroy.
    Hypothesis h_smc_rtt_destroy_p : Genv.find_funct_ptr ge b_smc_rtt_destroy
                                     = Some (External (EF_external _smc_rtt_destroy
                                                      (signature_of_type (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tulong cc_default))
                                            (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tulong cc_default).
    Local Opaque smc_rtt_destroy_spec.

    Variable b_smc_rec_run: block.
    Hypothesis h_smc_rec_run_s : Genv.find_symbol ge _smc_rec_run = Some b_smc_rec_run.
    Hypothesis h_smc_rec_run_p : Genv.find_funct_ptr ge b_smc_rec_run
                                 = Some (External (EF_external _smc_rec_run
                                                  (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
                                        (Tcons tulong (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque smc_rec_run_spec.

    Variable b_smc_rtt_map: block.
    Hypothesis h_smc_rtt_map_s : Genv.find_symbol ge _smc_rtt_map = Some b_smc_rtt_map.
    Hypothesis h_smc_rtt_map_p : Genv.find_funct_ptr ge b_smc_rtt_map
                                 = Some (External (EF_external _smc_rtt_map
                                                  (signature_of_type (Tcons tulong (Tcons tulong (Tcons tulong Tnil))) tulong cc_default))
                                        (Tcons tulong (Tcons tulong (Tcons tulong Tnil))) tulong cc_default).
    Local Opaque smc_rtt_map_spec.

    Variable b_smc_rtt_unmap: block.
    Hypothesis h_smc_rtt_unmap_s : Genv.find_symbol ge _smc_rtt_unmap = Some b_smc_rtt_unmap.
    Hypothesis h_smc_rtt_unmap_p : Genv.find_funct_ptr ge b_smc_rtt_unmap
                                   = Some (External (EF_external _smc_rtt_unmap
                                                    (signature_of_type (Tcons tulong (Tcons tulong (Tcons tulong Tnil))) tulong cc_default))
                                          (Tcons tulong (Tcons tulong (Tcons tulong Tnil))) tulong cc_default).
    Local Opaque smc_rtt_unmap_spec.

    Variable b_assert_cond: block.
    Hypothesis h_assert_cond_s : Genv.find_symbol ge _assert_cond = Some b_assert_cond.
    Hypothesis h_assert_cond_p : Genv.find_funct_ptr ge b_assert_cond
                                 = Some (External (EF_external _assert_cond
                                                  (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                        (Tcons tuint Tnil) tvoid cc_default).
    Local Opaque assert_cond_spec.

    Lemma handle_ns_smc_body_correct:
      forall m d d' env le function_id arg0 arg1 arg2 arg3 res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTfunction_id: PTree.get _function_id le = Some (Vlong function_id))
             (HPTarg0: PTree.get _arg0 le = Some (Vlong arg0))
             (HPTarg1: PTree.get _arg1 le = Some (Vlong arg1))
             (HPTarg2: PTree.get _arg2 le = Some (Vlong arg2))
             (HPTarg3: PTree.get _arg3 le = Some (Vlong arg3))
             (Hspec: handle_ns_smc_spec0 (VZ64 (Int64.unsigned function_id)) (VZ64 (Int64.unsigned arg0)) (VZ64 (Int64.unsigned arg1)) (VZ64 (Int64.unsigned arg2)) (VZ64 (Int64.unsigned arg3)) d = Some (d', VZ64 (Int64.unsigned res))),
           exists le', (exec_stmt ge env le ((m, d): mem) handle_ns_smc_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
    Proof.
      solve_code_proof Hspec handle_ns_smc_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
