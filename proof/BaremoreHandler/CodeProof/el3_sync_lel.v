Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import BaremoreService.Spec.
Require Import BaremoreService.Layer.
Require Import BaremoreHandler.Code.el3_sync_lel.

Require Import BaremoreHandler.LowSpecs.el3_sync_lel.

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
    _baremore_enter ↦ gensem baremore_enter_spec
      ⊕ _get_monitor_call_arg ↦ gensem get_monitor_call_arg_spec
      ⊕ _asc_mark_realm ↦ gensem asc_mark_realm_spec
      ⊕ _baremore_return_rmm ↦ gensem baremore_return_rmm_spec
      ⊕ _asc_mark_nonsecure ↦ gensem asc_mark_nonsecure_spec
      ⊕ _baremore_to_ns ↦ gensem baremore_to_ns_spec
      ⊕ _baremore_to_rmm ↦ gensem baremore_to_rmm_spec
      ⊕ _assert_cond ↦ gensem assert_cond_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_baremore_enter: block.
    Hypothesis h_baremore_enter_s : Genv.find_symbol ge _baremore_enter = Some b_baremore_enter.
    Hypothesis h_baremore_enter_p : Genv.find_funct_ptr ge b_baremore_enter
                                    = Some (External (EF_external _baremore_enter
                                                     (signature_of_type Tnil tuint cc_default))
                                           Tnil tuint cc_default).
    Local Opaque baremore_enter_spec.

    Variable b_get_monitor_call_arg: block.
    Hypothesis h_get_monitor_call_arg_s : Genv.find_symbol ge _get_monitor_call_arg = Some b_get_monitor_call_arg.
    Hypothesis h_get_monitor_call_arg_p : Genv.find_funct_ptr ge b_get_monitor_call_arg
                                          = Some (External (EF_external _get_monitor_call_arg
                                                           (signature_of_type Tnil tulong cc_default))
                                                 Tnil tulong cc_default).
    Local Opaque get_monitor_call_arg_spec.

    Variable b_asc_mark_realm: block.
    Hypothesis h_asc_mark_realm_s : Genv.find_symbol ge _asc_mark_realm = Some b_asc_mark_realm.
    Hypothesis h_asc_mark_realm_p : Genv.find_funct_ptr ge b_asc_mark_realm
                                    = Some (External (EF_external _asc_mark_realm
                                                     (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                           (Tcons tulong Tnil) tulong cc_default).
    Local Opaque asc_mark_realm_spec.

    Variable b_baremore_return_rmm: block.
    Hypothesis h_baremore_return_rmm_s : Genv.find_symbol ge _baremore_return_rmm = Some b_baremore_return_rmm.
    Hypothesis h_baremore_return_rmm_p : Genv.find_funct_ptr ge b_baremore_return_rmm
                                         = Some (External (EF_external _baremore_return_rmm
                                                          (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                                (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque baremore_return_rmm_spec.

    Variable b_asc_mark_nonsecure: block.
    Hypothesis h_asc_mark_nonsecure_s : Genv.find_symbol ge _asc_mark_nonsecure = Some b_asc_mark_nonsecure.
    Hypothesis h_asc_mark_nonsecure_p : Genv.find_funct_ptr ge b_asc_mark_nonsecure
                                        = Some (External (EF_external _asc_mark_nonsecure
                                                         (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                               (Tcons tulong Tnil) tulong cc_default).
    Local Opaque asc_mark_nonsecure_spec.

    Variable b_baremore_to_ns: block.
    Hypothesis h_baremore_to_ns_s : Genv.find_symbol ge _baremore_to_ns = Some b_baremore_to_ns.
    Hypothesis h_baremore_to_ns_p : Genv.find_funct_ptr ge b_baremore_to_ns
                                    = Some (External (EF_external _baremore_to_ns
                                                     (signature_of_type Tnil tvoid cc_default))
                                           Tnil tvoid cc_default).
    Local Opaque baremore_to_ns_spec.

    Variable b_baremore_to_rmm: block.
    Hypothesis h_baremore_to_rmm_s : Genv.find_symbol ge _baremore_to_rmm = Some b_baremore_to_rmm.
    Hypothesis h_baremore_to_rmm_p : Genv.find_funct_ptr ge b_baremore_to_rmm
                                     = Some (External (EF_external _baremore_to_rmm
                                                      (signature_of_type Tnil tvoid cc_default))
                                            Tnil tvoid cc_default).
    Local Opaque baremore_to_rmm_spec.

    Variable b_assert_cond: block.
    Hypothesis h_assert_cond_s : Genv.find_symbol ge _assert_cond = Some b_assert_cond.
    Hypothesis h_assert_cond_p : Genv.find_funct_ptr ge b_assert_cond
                                 = Some (External (EF_external _assert_cond
                                                  (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                        (Tcons tuint Tnil) tvoid cc_default).
    Local Opaque assert_cond_spec.

    Lemma el3_sync_lel_body_correct:
      forall m d d' env le 
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (Hspec: el3_sync_lel_spec0  d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) el3_sync_lel_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec el3_sync_lel_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
