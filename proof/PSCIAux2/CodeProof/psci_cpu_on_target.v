Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PSCIAux.Spec.
Require Import PSCIAux.Layer.
Require Import PSCIAux2.Code.psci_cpu_on_target.

Require Import PSCIAux2.LowSpecs.psci_cpu_on_target.

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
    _get_rec_runnable ↦ gensem get_rec_runnable_spec
      ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
      ⊕ _granule_unlock ↦ gensem granule_unlock_spec
      ⊕ _set_psci_result_x0 ↦ gensem set_psci_result_x0_spec
      ⊕ _psci_reset_rec ↦ gensem psci_reset_rec_spec
      ⊕ _set_rec_pc ↦ gensem set_rec_pc_spec
      ⊕ _set_rec_runnable ↦ gensem set_rec_runnable_spec
      ⊕ _set_psci_result_forward_psci_call ↦ gensem set_psci_result_forward_psci_call_spec
      ⊕ _set_psci_result_forward_x1 ↦ gensem set_psci_result_forward_x1_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_get_rec_runnable: block.
    Hypothesis h_get_rec_runnable_s : Genv.find_symbol ge _get_rec_runnable = Some b_get_rec_runnable.
    Hypothesis h_get_rec_runnable_p : Genv.find_funct_ptr ge b_get_rec_runnable
                                      = Some (External (EF_external _get_rec_runnable
                                                       (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                             (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque get_rec_runnable_spec.

    Variable b_buffer_unmap: block.
    Hypothesis h_buffer_unmap_s : Genv.find_symbol ge _buffer_unmap = Some b_buffer_unmap.
    Hypothesis h_buffer_unmap_p : Genv.find_funct_ptr ge b_buffer_unmap
                                  = Some (External (EF_external _buffer_unmap
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque buffer_unmap_spec.

    Variable b_granule_unlock: block.
    Hypothesis h_granule_unlock_s : Genv.find_symbol ge _granule_unlock = Some b_granule_unlock.
    Hypothesis h_granule_unlock_p : Genv.find_funct_ptr ge b_granule_unlock
                                    = Some (External (EF_external _granule_unlock
                                                     (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                           (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_unlock_spec.

    Variable b_set_psci_result_x0: block.
    Hypothesis h_set_psci_result_x0_s : Genv.find_symbol ge _set_psci_result_x0 = Some b_set_psci_result_x0.
    Hypothesis h_set_psci_result_x0_p : Genv.find_funct_ptr ge b_set_psci_result_x0
                                        = Some (External (EF_external _set_psci_result_x0
                                                         (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                               (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_psci_result_x0_spec.

    Variable b_psci_reset_rec: block.
    Hypothesis h_psci_reset_rec_s : Genv.find_symbol ge _psci_reset_rec = Some b_psci_reset_rec.
    Hypothesis h_psci_reset_rec_p : Genv.find_funct_ptr ge b_psci_reset_rec
                                    = Some (External (EF_external _psci_reset_rec
                                                     (signature_of_type (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default))
                                           (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque psci_reset_rec_spec.

    Variable b_set_rec_pc: block.
    Hypothesis h_set_rec_pc_s : Genv.find_symbol ge _set_rec_pc = Some b_set_rec_pc.
    Hypothesis h_set_rec_pc_p : Genv.find_funct_ptr ge b_set_rec_pc
                                = Some (External (EF_external _set_rec_pc
                                                 (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                       (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_rec_pc_spec.

    Variable b_set_rec_runnable: block.
    Hypothesis h_set_rec_runnable_s : Genv.find_symbol ge _set_rec_runnable = Some b_set_rec_runnable.
    Hypothesis h_set_rec_runnable_p : Genv.find_funct_ptr ge b_set_rec_runnable
                                      = Some (External (EF_external _set_rec_runnable
                                                       (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                             (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque set_rec_runnable_spec.

    Variable b_set_psci_result_forward_psci_call: block.
    Hypothesis h_set_psci_result_forward_psci_call_s : Genv.find_symbol ge _set_psci_result_forward_psci_call = Some b_set_psci_result_forward_psci_call.
    Hypothesis h_set_psci_result_forward_psci_call_p : Genv.find_funct_ptr ge b_set_psci_result_forward_psci_call
                                                       = Some (External (EF_external _set_psci_result_forward_psci_call
                                                                        (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                                              (Tcons tuint Tnil) tvoid cc_default).
    Local Opaque set_psci_result_forward_psci_call_spec.

    Variable b_set_psci_result_forward_x1: block.
    Hypothesis h_set_psci_result_forward_x1_s : Genv.find_symbol ge _set_psci_result_forward_x1 = Some b_set_psci_result_forward_x1.
    Hypothesis h_set_psci_result_forward_x1_p : Genv.find_funct_ptr ge b_set_psci_result_forward_x1
                                                = Some (External (EF_external _set_psci_result_forward_x1
                                                                 (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                                       (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_psci_result_forward_x1_spec.

    Lemma psci_cpu_on_target_body_correct:
      forall m d d' env le g_target_rec_base g_target_rec_offset target_rec_base target_rec_offset rec_base rec_offset entry_point_address target_cpu
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTg_target_rec: PTree.get _g_target_rec le = Some (Vptr g_target_rec_base (Int.repr g_target_rec_offset)))
             (HPTtarget_rec: PTree.get _target_rec le = Some (Vptr target_rec_base (Int.repr target_rec_offset)))
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTentry_point_address: PTree.get _entry_point_address le = Some (Vlong entry_point_address))
             (HPTtarget_cpu: PTree.get _target_cpu le = Some (Vlong target_cpu))
             (Hspec: psci_cpu_on_target_spec0 (g_target_rec_base, g_target_rec_offset) (target_rec_base, target_rec_offset) (rec_base, rec_offset) (VZ64 (Int64.unsigned entry_point_address)) (VZ64 (Int64.unsigned target_cpu)) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) psci_cpu_on_target_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec psci_cpu_on_target_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
