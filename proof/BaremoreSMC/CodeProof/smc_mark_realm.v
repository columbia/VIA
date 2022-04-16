Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import BaremoreHandler.Spec.
Require Import BaremoreHandler.Layer.
Require Import BaremoreSMC.Code.smc_mark_realm.

Require Import BaremoreSMC.LowSpecs.smc_mark_realm.

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
    _set_monitor_call ↦ gensem set_monitor_call_spec
      ⊕ _el3_sync_lel ↦ gensem el3_sync_lel_spec
      ⊕ _get_monitor_call_ret ↦ gensem get_monitor_call_ret_spec
      ⊕ _assert_cond ↦ gensem assert_cond_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_set_monitor_call: block.
    Hypothesis h_set_monitor_call_s : Genv.find_symbol ge _set_monitor_call = Some b_set_monitor_call.
    Hypothesis h_set_monitor_call_p : Genv.find_funct_ptr ge b_set_monitor_call
                                      = Some (External (EF_external _set_monitor_call
                                                       (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                             (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_monitor_call_spec.

    Variable b_el3_sync_lel: block.
    Hypothesis h_el3_sync_lel_s : Genv.find_symbol ge _el3_sync_lel = Some b_el3_sync_lel.
    Hypothesis h_el3_sync_lel_p : Genv.find_funct_ptr ge b_el3_sync_lel
                                  = Some (External (EF_external _el3_sync_lel
                                                   (signature_of_type Tnil tvoid cc_default))
                                         Tnil tvoid cc_default).
    Local Opaque el3_sync_lel_spec.

    Variable b_get_monitor_call_ret: block.
    Hypothesis h_get_monitor_call_ret_s : Genv.find_symbol ge _get_monitor_call_ret = Some b_get_monitor_call_ret.
    Hypothesis h_get_monitor_call_ret_p : Genv.find_funct_ptr ge b_get_monitor_call_ret
                                          = Some (External (EF_external _get_monitor_call_ret
                                                           (signature_of_type Tnil tulong cc_default))
                                                 Tnil tulong cc_default).
    Local Opaque get_monitor_call_ret_spec.

    Variable b_assert_cond: block.
    Hypothesis h_assert_cond_s : Genv.find_symbol ge _assert_cond = Some b_assert_cond.
    Hypothesis h_assert_cond_p : Genv.find_funct_ptr ge b_assert_cond
                                 = Some (External (EF_external _assert_cond
                                                  (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                        (Tcons tuint Tnil) tvoid cc_default).
    Local Opaque assert_cond_spec.

    Lemma smc_mark_realm_body_correct:
      forall m d d' env le addr
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTaddr: PTree.get _addr le = Some (Vlong addr))
             (Hspec: smc_mark_realm_spec0 (VZ64 (Int64.unsigned addr)) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) smc_mark_realm_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec smc_mark_realm_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
