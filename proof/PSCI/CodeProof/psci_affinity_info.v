Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PSCIAux2.Spec.
Require Import PSCIAux2.Layer.
Require Import PSCI.Code.psci_affinity_info.

Require Import PSCI.LowSpecs.psci_affinity_info.

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
    _set_psci_result_x0 ↦ gensem set_psci_result_x0_spec
      ⊕ _psci_lookup_target ↦ gensem psci_lookup_target_spec
      ⊕ _is_null ↦ gensem is_null_spec
      ⊕ _granule_map ↦ gensem granule_map_spec
      ⊕ _get_rec_runnable ↦ gensem get_rec_runnable_spec
      ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
      ⊕ _granule_unlock ↦ gensem granule_unlock_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_set_psci_result_x0: block.
    Hypothesis h_set_psci_result_x0_s : Genv.find_symbol ge _set_psci_result_x0 = Some b_set_psci_result_x0.
    Hypothesis h_set_psci_result_x0_p : Genv.find_funct_ptr ge b_set_psci_result_x0
                                        = Some (External (EF_external _set_psci_result_x0
                                                         (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                               (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_psci_result_x0_spec.

    Variable b_psci_lookup_target: block.
    Hypothesis h_psci_lookup_target_s : Genv.find_symbol ge _psci_lookup_target = Some b_psci_lookup_target.
    Hypothesis h_psci_lookup_target_p : Genv.find_funct_ptr ge b_psci_lookup_target
                                        = Some (External (EF_external _psci_lookup_target
                                                         (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) Tptr cc_default))
                                               (Tcons Tptr (Tcons tulong Tnil)) Tptr cc_default).
    Local Opaque psci_lookup_target_spec.

    Variable b_is_null: block.
    Hypothesis h_is_null_s : Genv.find_symbol ge _is_null = Some b_is_null.
    Hypothesis h_is_null_p : Genv.find_funct_ptr ge b_is_null
                             = Some (External (EF_external _is_null
                                              (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                    (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque is_null_spec.

    Variable b_granule_map: block.
    Hypothesis h_granule_map_s : Genv.find_symbol ge _granule_map = Some b_granule_map.
    Hypothesis h_granule_map_p : Genv.find_funct_ptr ge b_granule_map
                                 = Some (External (EF_external _granule_map
                                                  (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default))
                                        (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default).
    Local Opaque granule_map_spec.

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

    Lemma psci_affinity_info_body_correct:
      forall m d d' env le rec_base rec_offset target_affinity lowest_affinity_level
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTtarget_affinity: PTree.get _target_affinity le = Some (Vlong target_affinity))
             (HPTlowest_affinity_level: PTree.get _lowest_affinity_level le = Some (Vlong lowest_affinity_level))
             (Hspec: psci_affinity_info_spec0 (rec_base, rec_offset) (VZ64 (Int64.unsigned target_affinity)) (VZ64 (Int64.unsigned lowest_affinity_level)) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) psci_affinity_info_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec psci_affinity_info_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
