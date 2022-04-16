Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import TableAux.Spec.
Require Import TableAux2.Layer.
Require Import TableWalk.Code.table_walk_lock_unlock.

Require Import TableWalk.LowSpecs.table_walk_lock_unlock.

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
    _granule_map ↦ gensem granule_map_spec
      ⊕ _get_rd_g_rtt ↦ gensem get_rd_g_rtt_spec
      ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
      ⊕ _granule_lock ↦ gensem granule_lock_spec
      ⊕ _is_null ↦ gensem is_null_spec
      ⊕ _addr_to_idx ↦ gensem addr_to_idx_spec
      ⊕ _find_next_level_idx ↦ gensem find_next_level_idx_spec
      ⊕ _granule_unlock ↦ gensem granule_unlock_spec
      ⊕ _set_wi_g_llt ↦ gensem set_wi_g_llt_spec
      ⊕ _set_wi_index ↦ gensem set_wi_index_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_granule_map: block.
    Hypothesis h_granule_map_s : Genv.find_symbol ge _granule_map = Some b_granule_map.
    Hypothesis h_granule_map_p : Genv.find_funct_ptr ge b_granule_map
                                 = Some (External (EF_external _granule_map
                                                  (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default))
                                        (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default).
    Local Opaque granule_map_spec.

    Variable b_get_rd_g_rtt: block.
    Hypothesis h_get_rd_g_rtt_s : Genv.find_symbol ge _get_rd_g_rtt = Some b_get_rd_g_rtt.
    Hypothesis h_get_rd_g_rtt_p : Genv.find_funct_ptr ge b_get_rd_g_rtt
                                  = Some (External (EF_external _get_rd_g_rtt
                                                   (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                         (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rd_g_rtt_spec.

    Variable b_buffer_unmap: block.
    Hypothesis h_buffer_unmap_s : Genv.find_symbol ge _buffer_unmap = Some b_buffer_unmap.
    Hypothesis h_buffer_unmap_p : Genv.find_funct_ptr ge b_buffer_unmap
                                  = Some (External (EF_external _buffer_unmap
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque buffer_unmap_spec.

    Variable b_granule_lock: block.
    Hypothesis h_granule_lock_s : Genv.find_symbol ge _granule_lock = Some b_granule_lock.
    Hypothesis h_granule_lock_p : Genv.find_funct_ptr ge b_granule_lock
                                  = Some (External (EF_external _granule_lock
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_lock_spec.

    Variable b_is_null: block.
    Hypothesis h_is_null_s : Genv.find_symbol ge _is_null = Some b_is_null.
    Hypothesis h_is_null_p : Genv.find_funct_ptr ge b_is_null
                             = Some (External (EF_external _is_null
                                              (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                    (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque is_null_spec.

    Variable b_addr_to_idx: block.
    Hypothesis h_addr_to_idx_s : Genv.find_symbol ge _addr_to_idx = Some b_addr_to_idx.
    Hypothesis h_addr_to_idx_p : Genv.find_funct_ptr ge b_addr_to_idx
                                 = Some (External (EF_external _addr_to_idx
                                                  (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
                                        (Tcons tulong (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque addr_to_idx_spec.

    Variable b_find_next_level_idx: block.
    Hypothesis h_find_next_level_idx_s : Genv.find_symbol ge _find_next_level_idx = Some b_find_next_level_idx.
    Hypothesis h_find_next_level_idx_p : Genv.find_funct_ptr ge b_find_next_level_idx
                                         = Some (External (EF_external _find_next_level_idx
                                                          (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) Tptr cc_default))
                                                (Tcons Tptr (Tcons tulong Tnil)) Tptr cc_default).
    Local Opaque find_next_level_idx_spec.

    Variable b_granule_unlock: block.
    Hypothesis h_granule_unlock_s : Genv.find_symbol ge _granule_unlock = Some b_granule_unlock.
    Hypothesis h_granule_unlock_p : Genv.find_funct_ptr ge b_granule_unlock
                                    = Some (External (EF_external _granule_unlock
                                                     (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                           (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_unlock_spec.

    Variable b_set_wi_g_llt: block.
    Hypothesis h_set_wi_g_llt_s : Genv.find_symbol ge _set_wi_g_llt = Some b_set_wi_g_llt.
    Hypothesis h_set_wi_g_llt_p : Genv.find_funct_ptr ge b_set_wi_g_llt
                                  = Some (External (EF_external _set_wi_g_llt
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque set_wi_g_llt_spec.

    Variable b_set_wi_index: block.
    Hypothesis h_set_wi_index_s : Genv.find_symbol ge _set_wi_index = Some b_set_wi_index.
    Hypothesis h_set_wi_index_p : Genv.find_funct_ptr ge b_set_wi_index
                                  = Some (External (EF_external _set_wi_index
                                                   (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                         (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_wi_index_spec.

  End BodyProof.

End CodeProof.
