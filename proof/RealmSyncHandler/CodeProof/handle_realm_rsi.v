Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PSCIHandler.Spec.
Require Import RealmSyncHandlerAux.Layer.
Require Import RealmSyncHandler.Code.handle_realm_rsi.

Require Import RealmSyncHandler.LowSpecs.handle_realm_rsi.

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
    _get_rec_regs ↦ gensem get_rec_regs_spec
      ⊕ _set_rec_regs ↦ gensem set_rec_regs_spec
      ⊕ _psci_rsi ↦ gensem psci_rsi_spec
      ⊕ _get_psci_result_x0 ↦ gensem get_psci_result_x0_spec
      ⊕ _get_psci_result_x1 ↦ gensem get_psci_result_x1_spec
      ⊕ _get_psci_result_x2 ↦ gensem get_psci_result_x2_spec
      ⊕ _get_psci_result_x3 ↦ gensem get_psci_result_x3_spec
      ⊕ _get_psci_result_forward_psci_call ↦ gensem get_psci_result_forward_psci_call_spec
      ⊕ _set_rec_run_exit_reason ↦ gensem set_rec_run_exit_reason_spec
      ⊕ _set_rec_run_gprs ↦ gensem set_rec_run_gprs_spec
      ⊕ _get_psci_result_forward_x1 ↦ gensem get_psci_result_forward_x1_spec
      ⊕ _get_psci_result_forward_x2 ↦ gensem get_psci_result_forward_x2_spec
      ⊕ _get_psci_result_forward_x3 ↦ gensem get_psci_result_forward_x3_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_get_rec_regs: block.
    Hypothesis h_get_rec_regs_s : Genv.find_symbol ge _get_rec_regs = Some b_get_rec_regs.
    Hypothesis h_get_rec_regs_p : Genv.find_funct_ptr ge b_get_rec_regs
                                  = Some (External (EF_external _get_rec_regs
                                                   (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tulong cc_default))
                                         (Tcons Tptr (Tcons tuint Tnil)) tulong cc_default).
    Local Opaque get_rec_regs_spec.

    Variable b_set_rec_regs: block.
    Hypothesis h_set_rec_regs_s : Genv.find_symbol ge _set_rec_regs = Some b_set_rec_regs.
    Hypothesis h_set_rec_regs_p : Genv.find_funct_ptr ge b_set_rec_regs
                                  = Some (External (EF_external _set_rec_regs
                                                   (signature_of_type (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                         (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque set_rec_regs_spec.

    Variable b_psci_rsi: block.
    Hypothesis h_psci_rsi_s : Genv.find_symbol ge _psci_rsi = Some b_psci_rsi.
    Hypothesis h_psci_rsi_p : Genv.find_funct_ptr ge b_psci_rsi
                              = Some (External (EF_external _psci_rsi
                                               (signature_of_type (Tcons Tptr (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tulong Tnil))))) tvoid cc_default))
                                     (Tcons Tptr (Tcons tuint (Tcons tulong (Tcons tulong (Tcons tulong Tnil))))) tvoid cc_default).
    Local Opaque psci_rsi_spec.

    Variable b_get_psci_result_x0: block.
    Hypothesis h_get_psci_result_x0_s : Genv.find_symbol ge _get_psci_result_x0 = Some b_get_psci_result_x0.
    Hypothesis h_get_psci_result_x0_p : Genv.find_funct_ptr ge b_get_psci_result_x0
                                        = Some (External (EF_external _get_psci_result_x0
                                                         (signature_of_type Tnil tulong cc_default))
                                               Tnil tulong cc_default).
    Local Opaque get_psci_result_x0_spec.

    Variable b_get_psci_result_x1: block.
    Hypothesis h_get_psci_result_x1_s : Genv.find_symbol ge _get_psci_result_x1 = Some b_get_psci_result_x1.
    Hypothesis h_get_psci_result_x1_p : Genv.find_funct_ptr ge b_get_psci_result_x1
                                        = Some (External (EF_external _get_psci_result_x1
                                                         (signature_of_type Tnil tulong cc_default))
                                               Tnil tulong cc_default).
    Local Opaque get_psci_result_x1_spec.

    Variable b_get_psci_result_x2: block.
    Hypothesis h_get_psci_result_x2_s : Genv.find_symbol ge _get_psci_result_x2 = Some b_get_psci_result_x2.
    Hypothesis h_get_psci_result_x2_p : Genv.find_funct_ptr ge b_get_psci_result_x2
                                        = Some (External (EF_external _get_psci_result_x2
                                                         (signature_of_type Tnil tulong cc_default))
                                               Tnil tulong cc_default).
    Local Opaque get_psci_result_x2_spec.

    Variable b_get_psci_result_x3: block.
    Hypothesis h_get_psci_result_x3_s : Genv.find_symbol ge _get_psci_result_x3 = Some b_get_psci_result_x3.
    Hypothesis h_get_psci_result_x3_p : Genv.find_funct_ptr ge b_get_psci_result_x3
                                        = Some (External (EF_external _get_psci_result_x3
                                                         (signature_of_type Tnil tulong cc_default))
                                               Tnil tulong cc_default).
    Local Opaque get_psci_result_x3_spec.

    Variable b_get_psci_result_forward_psci_call: block.
    Hypothesis h_get_psci_result_forward_psci_call_s : Genv.find_symbol ge _get_psci_result_forward_psci_call = Some b_get_psci_result_forward_psci_call.
    Hypothesis h_get_psci_result_forward_psci_call_p : Genv.find_funct_ptr ge b_get_psci_result_forward_psci_call
                                                       = Some (External (EF_external _get_psci_result_forward_psci_call
                                                                        (signature_of_type Tnil tuint cc_default))
                                                              Tnil tuint cc_default).
    Local Opaque get_psci_result_forward_psci_call_spec.

    Variable b_set_rec_run_exit_reason: block.
    Hypothesis h_set_rec_run_exit_reason_s : Genv.find_symbol ge _set_rec_run_exit_reason = Some b_set_rec_run_exit_reason.
    Hypothesis h_set_rec_run_exit_reason_p : Genv.find_funct_ptr ge b_set_rec_run_exit_reason
                                             = Some (External (EF_external _set_rec_run_exit_reason
                                                              (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                                    (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_rec_run_exit_reason_spec.

    Variable b_set_rec_run_gprs: block.
    Hypothesis h_set_rec_run_gprs_s : Genv.find_symbol ge _set_rec_run_gprs = Some b_set_rec_run_gprs.
    Hypothesis h_set_rec_run_gprs_p : Genv.find_funct_ptr ge b_set_rec_run_gprs
                                      = Some (External (EF_external _set_rec_run_gprs
                                                       (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                             (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_rec_run_gprs_spec.

    Variable b_get_psci_result_forward_x1: block.
    Hypothesis h_get_psci_result_forward_x1_s : Genv.find_symbol ge _get_psci_result_forward_x1 = Some b_get_psci_result_forward_x1.
    Hypothesis h_get_psci_result_forward_x1_p : Genv.find_funct_ptr ge b_get_psci_result_forward_x1
                                                = Some (External (EF_external _get_psci_result_forward_x1
                                                                 (signature_of_type Tnil tulong cc_default))
                                                       Tnil tulong cc_default).
    Local Opaque get_psci_result_forward_x1_spec.

    Variable b_get_psci_result_forward_x2: block.
    Hypothesis h_get_psci_result_forward_x2_s : Genv.find_symbol ge _get_psci_result_forward_x2 = Some b_get_psci_result_forward_x2.
    Hypothesis h_get_psci_result_forward_x2_p : Genv.find_funct_ptr ge b_get_psci_result_forward_x2
                                                = Some (External (EF_external _get_psci_result_forward_x2
                                                                 (signature_of_type Tnil tulong cc_default))
                                                       Tnil tulong cc_default).
    Local Opaque get_psci_result_forward_x2_spec.

    Variable b_get_psci_result_forward_x3: block.
    Hypothesis h_get_psci_result_forward_x3_s : Genv.find_symbol ge _get_psci_result_forward_x3 = Some b_get_psci_result_forward_x3.
    Hypothesis h_get_psci_result_forward_x3_p : Genv.find_funct_ptr ge b_get_psci_result_forward_x3
                                                = Some (External (EF_external _get_psci_result_forward_x3
                                                                 (signature_of_type Tnil tulong cc_default))
                                                       Tnil tulong cc_default).
    Local Opaque get_psci_result_forward_x3_spec.

    Lemma handle_realm_rsi_body_correct:
      forall m d d' env le rec_base rec_offset res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (Hspec: handle_realm_rsi_spec0 (rec_base, rec_offset) d = Some (d',Int.unsigned res)),
           exists le', (exec_stmt ge env le ((m, d): mem) handle_realm_rsi_body E0 le' (m, d') (Out_return (Some (Vint res, tuint)))).
    Proof.
      solve_code_proof Hspec handle_realm_rsi_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
