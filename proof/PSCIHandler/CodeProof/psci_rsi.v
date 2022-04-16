Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import PSCI.Spec.
Require Import AbsAccessor.Spec.
Require Import PSCI.Layer.
Require Import PSCIHandler.Code.psci_rsi.

Require Import PSCIHandler.LowSpecs.psci_rsi.

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
    _psci_version ↦ gensem psci_version_spec
      ⊕ _psci_cpu_suspend ↦ gensem psci_cpu_suspend_spec
      ⊕ _psci_cpu_off ↦ gensem psci_cpu_off_spec
      ⊕ _psci_cpu_on ↦ gensem psci_cpu_on_spec
      ⊕ _psci_affinity_info ↦ gensem psci_affinity_info_spec
      ⊕ _psci_system_off ↦ gensem psci_system_off_spec
      ⊕ _psci_system_reset ↦ gensem psci_system_reset_spec
      ⊕ _psci_features ↦ gensem psci_features_spec
      ⊕ _set_psci_result_x0 ↦ gensem set_psci_result_x0_spec
      ⊕ _set_psci_result_forward_psci_call ↦ gensem set_psci_result_forward_psci_call_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_psci_version: block.
    Hypothesis h_psci_version_s : Genv.find_symbol ge _psci_version = Some b_psci_version.
    Hypothesis h_psci_version_p : Genv.find_funct_ptr ge b_psci_version
                                  = Some (External (EF_external _psci_version
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque psci_version_spec.

    Variable b_psci_cpu_suspend: block.
    Hypothesis h_psci_cpu_suspend_s : Genv.find_symbol ge _psci_cpu_suspend = Some b_psci_cpu_suspend.
    Hypothesis h_psci_cpu_suspend_p : Genv.find_funct_ptr ge b_psci_cpu_suspend
                                      = Some (External (EF_external _psci_cpu_suspend
                                                       (signature_of_type (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                             (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque psci_cpu_suspend_spec.

    Variable b_psci_cpu_off: block.
    Hypothesis h_psci_cpu_off_s : Genv.find_symbol ge _psci_cpu_off = Some b_psci_cpu_off.
    Hypothesis h_psci_cpu_off_p : Genv.find_funct_ptr ge b_psci_cpu_off
                                  = Some (External (EF_external _psci_cpu_off
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque psci_cpu_off_spec.

    Variable b_psci_cpu_on: block.
    Hypothesis h_psci_cpu_on_s : Genv.find_symbol ge _psci_cpu_on = Some b_psci_cpu_on.
    Hypothesis h_psci_cpu_on_p : Genv.find_funct_ptr ge b_psci_cpu_on
                                 = Some (External (EF_external _psci_cpu_on
                                                  (signature_of_type (Tcons Tptr (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default))
                                        (Tcons Tptr (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default).
    Local Opaque psci_cpu_on_spec.

    Variable b_psci_affinity_info: block.
    Hypothesis h_psci_affinity_info_s : Genv.find_symbol ge _psci_affinity_info = Some b_psci_affinity_info.
    Hypothesis h_psci_affinity_info_p : Genv.find_funct_ptr ge b_psci_affinity_info
                                        = Some (External (EF_external _psci_affinity_info
                                                         (signature_of_type (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                               (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque psci_affinity_info_spec.

    Variable b_psci_system_off: block.
    Hypothesis h_psci_system_off_s : Genv.find_symbol ge _psci_system_off = Some b_psci_system_off.
    Hypothesis h_psci_system_off_p : Genv.find_funct_ptr ge b_psci_system_off
                                     = Some (External (EF_external _psci_system_off
                                                      (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                            (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque psci_system_off_spec.

    Variable b_psci_system_reset: block.
    Hypothesis h_psci_system_reset_s : Genv.find_symbol ge _psci_system_reset = Some b_psci_system_reset.
    Hypothesis h_psci_system_reset_p : Genv.find_funct_ptr ge b_psci_system_reset
                                       = Some (External (EF_external _psci_system_reset
                                                        (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                              (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque psci_system_reset_spec.

    Variable b_psci_features: block.
    Hypothesis h_psci_features_s : Genv.find_symbol ge _psci_features = Some b_psci_features.
    Hypothesis h_psci_features_p : Genv.find_funct_ptr ge b_psci_features
                                   = Some (External (EF_external _psci_features
                                                    (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                          (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque psci_features_spec.

    Variable b_set_psci_result_x0: block.
    Hypothesis h_set_psci_result_x0_s : Genv.find_symbol ge _set_psci_result_x0 = Some b_set_psci_result_x0.
    Hypothesis h_set_psci_result_x0_p : Genv.find_funct_ptr ge b_set_psci_result_x0
                                        = Some (External (EF_external _set_psci_result_x0
                                                         (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                               (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_psci_result_x0_spec.

    Variable b_set_psci_result_forward_psci_call: block.
    Hypothesis h_set_psci_result_forward_psci_call_s : Genv.find_symbol ge _set_psci_result_forward_psci_call = Some b_set_psci_result_forward_psci_call.
    Hypothesis h_set_psci_result_forward_psci_call_p : Genv.find_funct_ptr ge b_set_psci_result_forward_psci_call
                                                       = Some (External (EF_external _set_psci_result_forward_psci_call
                                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                                              (Tcons tuint Tnil) tvoid cc_default).
    Local Opaque set_psci_result_forward_psci_call_spec.

    Lemma psci_rsi_body_correct:
      forall m d d' env le rec_base rec_offset function_id arg0 arg1 arg2
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTfunction_id: PTree.get _function_id le = Some (Vint function_id))
             (HPTarg0: PTree.get _arg0 le = Some (Vlong arg0))
             (HPTarg1: PTree.get _arg1 le = Some (Vlong arg1))
             (HPTarg2: PTree.get _arg2 le = Some (Vlong arg2))
             (Hspec: psci_rsi_spec0 (rec_base, rec_offset) (Int.unsigned function_id) (VZ64 (Int64.unsigned arg0)) (VZ64 (Int64.unsigned arg1)) (VZ64 (Int64.unsigned arg2)) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) psci_rsi_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec psci_rsi_body; eexists; solve_proof_low;
        repeat (repeat sstep; try big_vcgen;
                match goal with
                | [H: ?a = ?c |- context[zeq ?a ?b]] =>
                    destruct (zeq a b); try omega
                | _ => idtac
                end).
    Qed.

  End BodyProof.

End CodeProof.
