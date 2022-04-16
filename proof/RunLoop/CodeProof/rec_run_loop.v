Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import CtxtSwitch.Spec.
Require Import AbsAccessor.Spec.
Require Import RunComplete.Layer.
Require Import RunLoop.Code.rec_run_loop.

Require Import RunLoop.LowSpecs.rec_run_loop.

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
    _save_ns_state ↦ gensem save_ns_state_spec
      ⊕ _restore_realm_state ↦ gensem restore_realm_state_spec
      ⊕ _configure_realm_stage2 ↦ gensem configure_realm_stage2_spec
      ⊕ _restore_hcr_el2 ↦ gensem restore_hcr_el2_spec
      ⊕ _run_realm ↦ gensem run_realm_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_save_ns_state: block.
    Hypothesis h_save_ns_state_s : Genv.find_symbol ge _save_ns_state = Some b_save_ns_state.
    Hypothesis h_save_ns_state_p : Genv.find_funct_ptr ge b_save_ns_state
                                   = Some (External (EF_external _save_ns_state
                                                    (signature_of_type Tnil tvoid cc_default))
                                          Tnil tvoid cc_default).
    Local Opaque save_ns_state_spec.

    Variable b_restore_realm_state: block.
    Hypothesis h_restore_realm_state_s : Genv.find_symbol ge _restore_realm_state = Some b_restore_realm_state.
    Hypothesis h_restore_realm_state_p : Genv.find_funct_ptr ge b_restore_realm_state
                                         = Some (External (EF_external _restore_realm_state
                                                          (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                                (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque restore_realm_state_spec.

    Variable b_configure_realm_stage2: block.
    Hypothesis h_configure_realm_stage2_s : Genv.find_symbol ge _configure_realm_stage2 = Some b_configure_realm_stage2.
    Hypothesis h_configure_realm_stage2_p : Genv.find_funct_ptr ge b_configure_realm_stage2
                                            = Some (External (EF_external _configure_realm_stage2
                                                             (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                                   (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque configure_realm_stage2_spec.

    Variable b_restore_hcr_el2: block.
    Hypothesis h_restore_hcr_el2_s : Genv.find_symbol ge _restore_hcr_el2 = Some b_restore_hcr_el2.
    Hypothesis h_restore_hcr_el2_p : Genv.find_funct_ptr ge b_restore_hcr_el2
                                     = Some (External (EF_external _restore_hcr_el2
                                                      (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                            (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque restore_hcr_el2_spec.

    Variable b_run_realm: block.
    Hypothesis h_run_realm_s : Genv.find_symbol ge _run_realm = Some b_run_realm.
    Hypothesis h_run_realm_p : Genv.find_funct_ptr ge b_run_realm
                               = Some (External (EF_external _run_realm
                                                (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                      (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque run_realm_spec.

    Lemma rec_run_loop_body_correct:
      forall m d d' env le rec_base rec_offset
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (Hspec: rec_run_loop_spec0 (rec_base, rec_offset) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) rec_run_loop_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec rec_run_loop_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
