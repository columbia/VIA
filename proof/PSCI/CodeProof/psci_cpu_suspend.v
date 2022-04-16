Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PSCIAux2.Layer.
Require Import PSCI.Code.psci_cpu_suspend.

Require Import PSCI.LowSpecs.psci_cpu_suspend.

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
    _set_psci_result_forward_psci_call ↦ gensem set_psci_result_forward_psci_call_spec
      ⊕ _set_psci_result_x0 ↦ gensem set_psci_result_x0_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_set_psci_result_forward_psci_call: block.
    Hypothesis h_set_psci_result_forward_psci_call_s : Genv.find_symbol ge _set_psci_result_forward_psci_call = Some b_set_psci_result_forward_psci_call.
    Hypothesis h_set_psci_result_forward_psci_call_p : Genv.find_funct_ptr ge b_set_psci_result_forward_psci_call
                                                       = Some (External (EF_external _set_psci_result_forward_psci_call
                                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                                              (Tcons tuint Tnil) tvoid cc_default).
    Local Opaque set_psci_result_forward_psci_call_spec.

    Variable b_set_psci_result_x0: block.
    Hypothesis h_set_psci_result_x0_s : Genv.find_symbol ge _set_psci_result_x0 = Some b_set_psci_result_x0.
    Hypothesis h_set_psci_result_x0_p : Genv.find_funct_ptr ge b_set_psci_result_x0
                                        = Some (External (EF_external _set_psci_result_x0
                                                         (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                               (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_psci_result_x0_spec.

    Lemma psci_cpu_suspend_body_correct:
      forall m d d' env le rec_base rec_offset entry_point_address context_id
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTentry_point_address: PTree.get _entry_point_address le = Some (Vlong entry_point_address))
             (HPTcontext_id: PTree.get _context_id le = Some (Vlong context_id))
             (Hspec: psci_cpu_suspend_spec0 (rec_base, rec_offset) (VZ64 (Int64.unsigned entry_point_address)) (VZ64 (Int64.unsigned context_id)) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) psci_cpu_suspend_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec psci_cpu_suspend_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
