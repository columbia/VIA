Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PSCIAux.Spec.
Require Import RVIC.Layer.
Require Import RVIC2.Code.find_lock_map_target_rec.

Require Import RVIC2.LowSpecs.find_lock_map_target_rec.

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
    _mpidr_to_rec_idx ↦ gensem mpidr_to_rec_idx_spec
      ⊕ _get_rec_rec_idx ↦ gensem get_rec_rec_idx_spec
      ⊕ _get_rec_g_rec ↦ gensem get_rec_g_rec_spec
      ⊕ _granule_lock ↦ gensem granule_lock_spec
      ⊕ _granule_map ↦ gensem granule_map_spec
      ⊕ _set_target_rec ↦ gensem set_target_rec_spec
      ⊕ _get_rec_g_rd ↦ gensem get_rec_g_rd_spec
      ⊕ _get_rec_g_rec_list ↦ gensem get_rec_g_rec_list_spec
      ⊕ _find_lock_rec ↦ gensem find_lock_rec_spec
      ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
      ⊕ _is_null ↦ gensem is_null_spec
      ⊕ _null_ptr ↦ gensem null_ptr_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_mpidr_to_rec_idx: block.
    Hypothesis h_mpidr_to_rec_idx_s : Genv.find_symbol ge _mpidr_to_rec_idx = Some b_mpidr_to_rec_idx.
    Hypothesis h_mpidr_to_rec_idx_p : Genv.find_funct_ptr ge b_mpidr_to_rec_idx
                                      = Some (External (EF_external _mpidr_to_rec_idx
                                                       (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                             (Tcons tulong Tnil) tulong cc_default).
    Local Opaque mpidr_to_rec_idx_spec.

    Variable b_get_rec_rec_idx: block.
    Hypothesis h_get_rec_rec_idx_s : Genv.find_symbol ge _get_rec_rec_idx = Some b_get_rec_rec_idx.
    Hypothesis h_get_rec_rec_idx_p : Genv.find_funct_ptr ge b_get_rec_rec_idx
                                     = Some (External (EF_external _get_rec_rec_idx
                                                      (signature_of_type (Tcons Tptr Tnil) tulong cc_default))
                                            (Tcons Tptr Tnil) tulong cc_default).
    Local Opaque get_rec_rec_idx_spec.

    Variable b_get_rec_g_rec: block.
    Hypothesis h_get_rec_g_rec_s : Genv.find_symbol ge _get_rec_g_rec = Some b_get_rec_g_rec.
    Hypothesis h_get_rec_g_rec_p : Genv.find_funct_ptr ge b_get_rec_g_rec
                                   = Some (External (EF_external _get_rec_g_rec
                                                    (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                          (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rec_g_rec_spec.

    Variable b_granule_lock: block.
    Hypothesis h_granule_lock_s : Genv.find_symbol ge _granule_lock = Some b_granule_lock.
    Hypothesis h_granule_lock_p : Genv.find_funct_ptr ge b_granule_lock
                                  = Some (External (EF_external _granule_lock
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_lock_spec.

    Variable b_granule_map: block.
    Hypothesis h_granule_map_s : Genv.find_symbol ge _granule_map = Some b_granule_map.
    Hypothesis h_granule_map_p : Genv.find_funct_ptr ge b_granule_map
                                 = Some (External (EF_external _granule_map
                                                  (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default))
                                        (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default).
    Local Opaque granule_map_spec.

    Variable b_set_target_rec: block.
    Hypothesis h_set_target_rec_s : Genv.find_symbol ge _set_target_rec = Some b_set_target_rec.
    Hypothesis h_set_target_rec_p : Genv.find_funct_ptr ge b_set_target_rec
                                    = Some (External (EF_external _set_target_rec
                                                     (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                           (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque set_target_rec_spec.

    Variable b_get_rec_g_rd: block.
    Hypothesis h_get_rec_g_rd_s : Genv.find_symbol ge _get_rec_g_rd = Some b_get_rec_g_rd.
    Hypothesis h_get_rec_g_rd_p : Genv.find_funct_ptr ge b_get_rec_g_rd
                                  = Some (External (EF_external _get_rec_g_rd
                                                   (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                         (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rec_g_rd_spec.

    Variable b_get_rec_g_rec_list: block.
    Hypothesis h_get_rec_g_rec_list_s : Genv.find_symbol ge _get_rec_g_rec_list = Some b_get_rec_g_rec_list.
    Hypothesis h_get_rec_g_rec_list_p : Genv.find_funct_ptr ge b_get_rec_g_rec_list
                                        = Some (External (EF_external _get_rec_g_rec_list
                                                         (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                               (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rec_g_rec_list_spec.

    Variable b_find_lock_rec: block.
    Hypothesis h_find_lock_rec_s : Genv.find_symbol ge _find_lock_rec = Some b_find_lock_rec.
    Hypothesis h_find_lock_rec_p : Genv.find_funct_ptr ge b_find_lock_rec
                                   = Some (External (EF_external _find_lock_rec
                                                    (signature_of_type (Tcons Tptr (Tcons Tptr (Tcons tulong Tnil))) Tptr cc_default))
                                          (Tcons Tptr (Tcons Tptr (Tcons tulong Tnil))) Tptr cc_default).
    Local Opaque find_lock_rec_spec.

    Variable b_buffer_unmap: block.
    Hypothesis h_buffer_unmap_s : Genv.find_symbol ge _buffer_unmap = Some b_buffer_unmap.
    Hypothesis h_buffer_unmap_p : Genv.find_funct_ptr ge b_buffer_unmap
                                  = Some (External (EF_external _buffer_unmap
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque buffer_unmap_spec.

    Variable b_is_null: block.
    Hypothesis h_is_null_s : Genv.find_symbol ge _is_null = Some b_is_null.
    Hypothesis h_is_null_p : Genv.find_funct_ptr ge b_is_null
                             = Some (External (EF_external _is_null
                                              (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                    (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque is_null_spec.

    Variable b_null_ptr: block.
    Hypothesis h_null_ptr_s : Genv.find_symbol ge _null_ptr = Some b_null_ptr.
    Hypothesis h_null_ptr_p : Genv.find_funct_ptr ge b_null_ptr
                              = Some (External (EF_external _null_ptr
                                               (signature_of_type Tnil Tptr cc_default))
                                     Tnil Tptr cc_default).
    Local Opaque null_ptr_spec.

    Lemma find_lock_map_target_rec_body_correct:
      forall m d d' env le rec_base rec_offset target
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTtarget: PTree.get _target le = Some (Vlong target))
             (Hspec: find_lock_map_target_rec_spec0 (rec_base, rec_offset) (VZ64 (Int64.unsigned target)) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) find_lock_map_target_rec_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec find_lock_map_target_rec_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
