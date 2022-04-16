Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import RVIC3.Spec.
Require Import AbsAccessor.Spec.
Require Import RVIC2.Spec.
Require Import RVIC3.Layer.
Require Import RVIC4.Code.set_clear_masked.

Require Import RVIC4.LowSpecs.set_clear_masked.

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
    _validate_and_lookup_target ↦ gensem validate_and_lookup_target_spec
      ⊕ _get_target_rec ↦ gensem get_target_rec_spec
      ⊕ _set_rvic_result_x0 ↦ gensem set_rvic_result_x0_spec
      ⊕ _get_rec_rvic ↦ gensem get_rec_rvic_spec
      ⊕ _rvic_set_masked ↦ gensem rvic_set_masked_spec
      ⊕ _rvic_is_masked ↦ gensem rvic_is_masked_spec
      ⊕ _need_ns_notify ↦ gensem need_ns_notify_spec
      ⊕ _set_rvic_result_ns_notify ↦ gensem set_rvic_result_ns_notify_spec
      ⊕ _set_rvic_result_target ↦ gensem set_rvic_result_target_spec
      ⊕ _rvic_clear_masked ↦ gensem rvic_clear_masked_spec
      ⊕ _get_rec_g_rec ↦ gensem get_rec_g_rec_spec
      ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
      ⊕ _granule_unlock ↦ gensem granule_unlock_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_validate_and_lookup_target: block.
    Hypothesis h_validate_and_lookup_target_s : Genv.find_symbol ge _validate_and_lookup_target = Some b_validate_and_lookup_target.
    Hypothesis h_validate_and_lookup_target_p : Genv.find_funct_ptr ge b_validate_and_lookup_target
                                                = Some (External (EF_external _validate_and_lookup_target
                                                                 (signature_of_type (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tulong cc_default))
                                                       (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tulong cc_default).
    Local Opaque validate_and_lookup_target_spec.

    Variable b_get_target_rec: block.
    Hypothesis h_get_target_rec_s : Genv.find_symbol ge _get_target_rec = Some b_get_target_rec.
    Hypothesis h_get_target_rec_p : Genv.find_funct_ptr ge b_get_target_rec
                                    = Some (External (EF_external _get_target_rec
                                                     (signature_of_type Tnil Tptr cc_default))
                                           Tnil Tptr cc_default).
    Local Opaque get_target_rec_spec.

    Variable b_set_rvic_result_x0: block.
    Hypothesis h_set_rvic_result_x0_s : Genv.find_symbol ge _set_rvic_result_x0 = Some b_set_rvic_result_x0.
    Hypothesis h_set_rvic_result_x0_p : Genv.find_funct_ptr ge b_set_rvic_result_x0
                                        = Some (External (EF_external _set_rvic_result_x0
                                                         (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                               (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_rvic_result_x0_spec.

    Variable b_get_rec_rvic: block.
    Hypothesis h_get_rec_rvic_s : Genv.find_symbol ge _get_rec_rvic = Some b_get_rec_rvic.
    Hypothesis h_get_rec_rvic_p : Genv.find_funct_ptr ge b_get_rec_rvic
                                  = Some (External (EF_external _get_rec_rvic
                                                   (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                         (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rec_rvic_spec.

    Variable b_rvic_set_masked: block.
    Hypothesis h_rvic_set_masked_s : Genv.find_symbol ge _rvic_set_masked = Some b_rvic_set_masked.
    Hypothesis h_rvic_set_masked_p : Genv.find_funct_ptr ge b_rvic_set_masked
                                     = Some (External (EF_external _rvic_set_masked
                                                      (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                            (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque rvic_set_masked_spec.

    Variable b_rvic_is_masked: block.
    Hypothesis h_rvic_is_masked_s : Genv.find_symbol ge _rvic_is_masked = Some b_rvic_is_masked.
    Hypothesis h_rvic_is_masked_p : Genv.find_funct_ptr ge b_rvic_is_masked
                                    = Some (External (EF_external _rvic_is_masked
                                                     (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tuint cc_default))
                                           (Tcons Tptr (Tcons tulong Tnil)) tuint cc_default).
    Local Opaque rvic_is_masked_spec.

    Variable b_need_ns_notify: block.
    Hypothesis h_need_ns_notify_s : Genv.find_symbol ge _need_ns_notify = Some b_need_ns_notify.
    Hypothesis h_need_ns_notify_p : Genv.find_funct_ptr ge b_need_ns_notify
                                    = Some (External (EF_external _need_ns_notify
                                                     (signature_of_type (Tcons Tptr (Tcons Tptr (Tcons tulong Tnil))) tuint cc_default))
                                           (Tcons Tptr (Tcons Tptr (Tcons tulong Tnil))) tuint cc_default).
    Local Opaque need_ns_notify_spec.

    Variable b_set_rvic_result_ns_notify: block.
    Hypothesis h_set_rvic_result_ns_notify_s : Genv.find_symbol ge _set_rvic_result_ns_notify = Some b_set_rvic_result_ns_notify.
    Hypothesis h_set_rvic_result_ns_notify_p : Genv.find_funct_ptr ge b_set_rvic_result_ns_notify
                                               = Some (External (EF_external _set_rvic_result_ns_notify
                                                                (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                                      (Tcons tuint Tnil) tvoid cc_default).
    Local Opaque set_rvic_result_ns_notify_spec.

    Variable b_set_rvic_result_target: block.
    Hypothesis h_set_rvic_result_target_s : Genv.find_symbol ge _set_rvic_result_target = Some b_set_rvic_result_target.
    Hypothesis h_set_rvic_result_target_p : Genv.find_funct_ptr ge b_set_rvic_result_target
                                            = Some (External (EF_external _set_rvic_result_target
                                                             (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                                   (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_rvic_result_target_spec.

    Variable b_rvic_clear_masked: block.
    Hypothesis h_rvic_clear_masked_s : Genv.find_symbol ge _rvic_clear_masked = Some b_rvic_clear_masked.
    Hypothesis h_rvic_clear_masked_p : Genv.find_funct_ptr ge b_rvic_clear_masked
                                       = Some (External (EF_external _rvic_clear_masked
                                                        (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                              (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque rvic_clear_masked_spec.

    Variable b_get_rec_g_rec: block.
    Hypothesis h_get_rec_g_rec_s : Genv.find_symbol ge _get_rec_g_rec = Some b_get_rec_g_rec.
    Hypothesis h_get_rec_g_rec_p : Genv.find_funct_ptr ge b_get_rec_g_rec
                                   = Some (External (EF_external _get_rec_g_rec
                                                    (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                          (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rec_g_rec_spec.

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

    Lemma set_clear_masked_body_correct:
      forall m d d' env le rec_base rec_offset target intid masked
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTtarget: PTree.get _target le = Some (Vlong target))
             (HPTintid: PTree.get _intid le = Some (Vlong intid))
             (HPTmasked: PTree.get _masked le = Some (Vint masked))
             (Hspec: set_clear_masked_spec0 (rec_base, rec_offset) (VZ64 (Int64.unsigned target)) (VZ64 (Int64.unsigned intid)) (Int.unsigned masked) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) set_clear_masked_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec set_clear_masked_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
