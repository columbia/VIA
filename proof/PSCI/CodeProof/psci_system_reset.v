Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import PSCIAux2.Spec.
Require Import AbsAccessor.Spec.
Require Import PSCIAux2.Layer.
Require Import PSCI.Code.psci_system_reset.

Require Import PSCI.LowSpecs.psci_system_reset.

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
    _system_off_reboot ↦ gensem system_off_reboot_spec
      ⊕ _set_psci_result_forward_psci_call ↦ gensem set_psci_result_forward_psci_call_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_system_off_reboot: block.
    Hypothesis h_system_off_reboot_s : Genv.find_symbol ge _system_off_reboot = Some b_system_off_reboot.
    Hypothesis h_system_off_reboot_p : Genv.find_funct_ptr ge b_system_off_reboot
                                       = Some (External (EF_external _system_off_reboot
                                                        (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                              (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque system_off_reboot_spec.

    Variable b_set_psci_result_forward_psci_call: block.
    Hypothesis h_set_psci_result_forward_psci_call_s : Genv.find_symbol ge _set_psci_result_forward_psci_call = Some b_set_psci_result_forward_psci_call.
    Hypothesis h_set_psci_result_forward_psci_call_p : Genv.find_funct_ptr ge b_set_psci_result_forward_psci_call
                                                       = Some (External (EF_external _set_psci_result_forward_psci_call
                                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                                              (Tcons tuint Tnil) tvoid cc_default).
    Local Opaque set_psci_result_forward_psci_call_spec.

    Lemma psci_system_reset_body_correct:
      forall m d d' env le rec_base rec_offset
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (Hspec: psci_system_reset_spec0 (rec_base, rec_offset) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) psci_system_reset_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec psci_system_reset_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
