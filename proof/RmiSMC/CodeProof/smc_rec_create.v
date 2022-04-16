Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiOps.Spec.
Require Import RmiOps.Layer.
Require Import RmiSMC.Code.smc_rec_create.

Require Import RmiSMC.LowSpecs.smc_rec_create.

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
    _find_granule ↦ gensem find_granule_spec
      ⊕ _is_null ↦ gensem is_null_spec
      ⊕ _find_lock_granule ↦ gensem find_lock_granule_spec
      ⊕ _granule_map ↦ gensem granule_map_spec
      ⊕ _ns_granule_map ↦ gensem ns_granule_map_spec
      ⊕ _ns_buffer_read_rec_params ↦ gensem ns_buffer_read_rec_params_spec
      ⊕ _ns_buffer_unmap ↦ gensem ns_buffer_unmap_spec
      ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
      ⊕ _get_rd_g_rec_list ↦ gensem get_rd_g_rec_list_spec
      ⊕ _get_rd_state ↦ gensem get_rd_state_spec
      ⊕ _mpidr_is_valid ↦ gensem mpidr_is_valid_spec
      ⊕ _mpidr_to_rec_idx ↦ gensem mpidr_to_rec_idx_spec
      ⊕ _is_rec_valid ↦ gensem is_rec_valid_spec
      ⊕ _rec_create_ops ↦ gensem rec_create_ops_spec
      ⊕ _granule_unlock ↦ gensem granule_unlock_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_find_granule: block.
    Hypothesis h_find_granule_s : Genv.find_symbol ge _find_granule = Some b_find_granule.
    Hypothesis h_find_granule_p : Genv.find_funct_ptr ge b_find_granule
                                  = Some (External (EF_external _find_granule
                                                   (signature_of_type (Tcons tulong Tnil) Tptr cc_default))
                                         (Tcons tulong Tnil) Tptr cc_default).
    Local Opaque find_granule_spec.

    Variable b_is_null: block.
    Hypothesis h_is_null_s : Genv.find_symbol ge _is_null = Some b_is_null.
    Hypothesis h_is_null_p : Genv.find_funct_ptr ge b_is_null
                             = Some (External (EF_external _is_null
                                              (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                    (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque is_null_spec.

    Variable b_find_lock_granule: block.
    Hypothesis h_find_lock_granule_s : Genv.find_symbol ge _find_lock_granule = Some b_find_lock_granule.
    Hypothesis h_find_lock_granule_p : Genv.find_funct_ptr ge b_find_lock_granule
                                       = Some (External (EF_external _find_lock_granule
                                                        (signature_of_type (Tcons tulong (Tcons tulong Tnil)) Tptr cc_default))
                                              (Tcons tulong (Tcons tulong Tnil)) Tptr cc_default).
    Local Opaque find_lock_granule_spec.

    Variable b_granule_map: block.
    Hypothesis h_granule_map_s : Genv.find_symbol ge _granule_map = Some b_granule_map.
    Hypothesis h_granule_map_p : Genv.find_funct_ptr ge b_granule_map
                                 = Some (External (EF_external _granule_map
                                                  (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default))
                                        (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default).
    Local Opaque granule_map_spec.

    Variable b_ns_granule_map: block.
    Hypothesis h_ns_granule_map_s : Genv.find_symbol ge _ns_granule_map = Some b_ns_granule_map.
    Hypothesis h_ns_granule_map_p : Genv.find_funct_ptr ge b_ns_granule_map
                                    = Some (External (EF_external _ns_granule_map
                                                     (signature_of_type (Tcons tuint (Tcons Tptr Tnil)) tvoid cc_default))
                                           (Tcons tuint (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque ns_granule_map_spec.

    Variable b_ns_buffer_read_rec_params: block.
    Hypothesis h_ns_buffer_read_rec_params_s : Genv.find_symbol ge _ns_buffer_read_rec_params = Some b_ns_buffer_read_rec_params.
    Hypothesis h_ns_buffer_read_rec_params_p : Genv.find_funct_ptr ge b_ns_buffer_read_rec_params
                                               = Some (External (EF_external _ns_buffer_read_rec_params
                                                                (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                                      (Tcons tuint Tnil) tuint cc_default).
    Local Opaque ns_buffer_read_rec_params_spec.

    Variable b_ns_buffer_unmap: block.
    Hypothesis h_ns_buffer_unmap_s : Genv.find_symbol ge _ns_buffer_unmap = Some b_ns_buffer_unmap.
    Hypothesis h_ns_buffer_unmap_p : Genv.find_funct_ptr ge b_ns_buffer_unmap
                                     = Some (External (EF_external _ns_buffer_unmap
                                                      (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                            (Tcons tuint Tnil) tvoid cc_default).
    Local Opaque ns_buffer_unmap_spec.

    Variable b_buffer_unmap: block.
    Hypothesis h_buffer_unmap_s : Genv.find_symbol ge _buffer_unmap = Some b_buffer_unmap.
    Hypothesis h_buffer_unmap_p : Genv.find_funct_ptr ge b_buffer_unmap
                                  = Some (External (EF_external _buffer_unmap
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque buffer_unmap_spec.

    Variable b_get_rd_g_rec_list: block.
    Hypothesis h_get_rd_g_rec_list_s : Genv.find_symbol ge _get_rd_g_rec_list = Some b_get_rd_g_rec_list.
    Hypothesis h_get_rd_g_rec_list_p : Genv.find_funct_ptr ge b_get_rd_g_rec_list
                                       = Some (External (EF_external _get_rd_g_rec_list
                                                        (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                              (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rd_g_rec_list_spec.

    Variable b_get_rd_state: block.
    Hypothesis h_get_rd_state_s : Genv.find_symbol ge _get_rd_state = Some b_get_rd_state.
    Hypothesis h_get_rd_state_p : Genv.find_funct_ptr ge b_get_rd_state
                                  = Some (External (EF_external _get_rd_state
                                                   (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                         (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque get_rd_state_spec.

    Variable b_mpidr_is_valid: block.
    Hypothesis h_mpidr_is_valid_s : Genv.find_symbol ge _mpidr_is_valid = Some b_mpidr_is_valid.
    Hypothesis h_mpidr_is_valid_p : Genv.find_funct_ptr ge b_mpidr_is_valid
                                    = Some (External (EF_external _mpidr_is_valid
                                                     (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                           (Tcons tulong Tnil) tuint cc_default).
    Local Opaque mpidr_is_valid_spec.

    Variable b_mpidr_to_rec_idx: block.
    Hypothesis h_mpidr_to_rec_idx_s : Genv.find_symbol ge _mpidr_to_rec_idx = Some b_mpidr_to_rec_idx.
    Hypothesis h_mpidr_to_rec_idx_p : Genv.find_funct_ptr ge b_mpidr_to_rec_idx
                                      = Some (External (EF_external _mpidr_to_rec_idx
                                                       (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                             (Tcons tulong Tnil) tulong cc_default).
    Local Opaque mpidr_to_rec_idx_spec.

    Variable b_is_rec_valid: block.
    Hypothesis h_is_rec_valid_s : Genv.find_symbol ge _is_rec_valid = Some b_is_rec_valid.
    Hypothesis h_is_rec_valid_p : Genv.find_funct_ptr ge b_is_rec_valid
                                  = Some (External (EF_external _is_rec_valid
                                                   (signature_of_type (Tcons tulong (Tcons Tptr Tnil)) tuint cc_default))
                                         (Tcons tulong (Tcons Tptr Tnil)) tuint cc_default).
    Local Opaque is_rec_valid_spec.

    Variable b_rec_create_ops: block.
    Hypothesis h_rec_create_ops_s : Genv.find_symbol ge _rec_create_ops = Some b_rec_create_ops.
    Hypothesis h_rec_create_ops_p : Genv.find_funct_ptr ge b_rec_create_ops
                                    = Some (External (EF_external _rec_create_ops
                                                     (signature_of_type (Tcons Tptr (Tcons Tptr (Tcons Tptr (Tcons Tptr (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))))))) tvoid cc_default))
                                           (Tcons Tptr (Tcons Tptr (Tcons Tptr (Tcons Tptr (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))))))) tvoid cc_default).
    Local Opaque rec_create_ops_spec.

    Variable b_granule_unlock: block.
    Hypothesis h_granule_unlock_s : Genv.find_symbol ge _granule_unlock = Some b_granule_unlock.
    Hypothesis h_granule_unlock_p : Genv.find_funct_ptr ge b_granule_unlock
                                    = Some (External (EF_external _granule_unlock
                                                     (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                           (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_unlock_spec.

  End BodyProof.

End CodeProof.
