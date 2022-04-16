Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import TableAux2.Spec.
Require Import TableAux.Spec.
Require Import TableAux2.Layer.
Require Import TableAux3.Code.table_destroy_aux.

Require Import TableAux3.LowSpecs.table_destroy_aux.

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
      ⊕ _get_g_rtt_refcount ↦ gensem get_g_rtt_refcount_spec
      ⊕ _table_delete ↦ gensem table_delete_spec
      ⊕ _table_fold ↦ gensem table_fold_spec
      ⊕ _pgte_write ↦ gensem pgte_write_spec
      ⊕ _invalidate_page ↦ gensem invalidate_page_spec
      ⊕ _invalidate_pages_in_block ↦ gensem invalidate_pages_in_block_spec
      ⊕ _invalidate_block ↦ gensem invalidate_block_spec
      ⊕ _granule_put ↦ gensem granule_put_spec
      ⊕ _null_ptr ↦ gensem null_ptr_spec
      ⊕ _set_g_rtt_rd ↦ gensem set_g_rtt_rd_spec
      ⊕ _granule_memzero_mapped ↦ gensem granule_memzero_mapped_spec
      ⊕ _granule_memzero ↦ gensem granule_memzero_spec
      ⊕ _granule_set_state ↦ gensem granule_set_state_spec
      ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
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

    Variable b_get_g_rtt_refcount: block.
    Hypothesis h_get_g_rtt_refcount_s : Genv.find_symbol ge _get_g_rtt_refcount = Some b_get_g_rtt_refcount.
    Hypothesis h_get_g_rtt_refcount_p : Genv.find_funct_ptr ge b_get_g_rtt_refcount
                                        = Some (External (EF_external _get_g_rtt_refcount
                                                         (signature_of_type (Tcons Tptr Tnil) tulong cc_default))
                                               (Tcons Tptr Tnil) tulong cc_default).
    Local Opaque get_g_rtt_refcount_spec.

    Variable b_table_delete: block.
    Hypothesis h_table_delete_s : Genv.find_symbol ge _table_delete = Some b_table_delete.
    Hypothesis h_table_delete_p : Genv.find_funct_ptr ge b_table_delete
                                  = Some (External (EF_external _table_delete
                                                   (signature_of_type (Tcons Tptr (Tcons Tptr Tnil)) tulong cc_default))
                                         (Tcons Tptr (Tcons Tptr Tnil)) tulong cc_default).
    Local Opaque table_delete_spec.

    Variable b_table_fold: block.
    Hypothesis h_table_fold_s : Genv.find_symbol ge _table_fold = Some b_table_fold.
    Hypothesis h_table_fold_p : Genv.find_funct_ptr ge b_table_fold
                                = Some (External (EF_external _table_fold
                                                 (signature_of_type (Tcons Tptr (Tcons tulong (Tcons Tptr Tnil))) tulong cc_default))
                                       (Tcons Tptr (Tcons tulong (Tcons Tptr Tnil))) tulong cc_default).
    Local Opaque table_fold_spec.

    Variable b_pgte_write: block.
    Hypothesis h_pgte_write_s : Genv.find_symbol ge _pgte_write = Some b_pgte_write.
    Hypothesis h_pgte_write_p : Genv.find_funct_ptr ge b_pgte_write
                                = Some (External (EF_external _pgte_write
                                                 (signature_of_type (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                       (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque pgte_write_spec.

    Variable b_invalidate_page: block.
    Hypothesis h_invalidate_page_s : Genv.find_symbol ge _invalidate_page = Some b_invalidate_page.
    Hypothesis h_invalidate_page_p : Genv.find_funct_ptr ge b_invalidate_page
                                     = Some (External (EF_external _invalidate_page
                                                      (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                            (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque invalidate_page_spec.

    Variable b_invalidate_pages_in_block: block.
    Hypothesis h_invalidate_pages_in_block_s : Genv.find_symbol ge _invalidate_pages_in_block = Some b_invalidate_pages_in_block.
    Hypothesis h_invalidate_pages_in_block_p : Genv.find_funct_ptr ge b_invalidate_pages_in_block
                                               = Some (External (EF_external _invalidate_pages_in_block
                                                                (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                                      (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque invalidate_pages_in_block_spec.

    Variable b_invalidate_block: block.
    Hypothesis h_invalidate_block_s : Genv.find_symbol ge _invalidate_block = Some b_invalidate_block.
    Hypothesis h_invalidate_block_p : Genv.find_funct_ptr ge b_invalidate_block
                                      = Some (External (EF_external _invalidate_block
                                                       (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                             (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque invalidate_block_spec.

    Variable b_granule_put: block.
    Hypothesis h_granule_put_s : Genv.find_symbol ge _granule_put = Some b_granule_put.
    Hypothesis h_granule_put_p : Genv.find_funct_ptr ge b_granule_put
                                 = Some (External (EF_external _granule_put
                                                  (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                        (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_put_spec.

    Variable b_null_ptr: block.
    Hypothesis h_null_ptr_s : Genv.find_symbol ge _null_ptr = Some b_null_ptr.
    Hypothesis h_null_ptr_p : Genv.find_funct_ptr ge b_null_ptr
                              = Some (External (EF_external _null_ptr
                                               (signature_of_type Tnil Tptr cc_default))
                                     Tnil Tptr cc_default).
    Local Opaque null_ptr_spec.

    Variable b_set_g_rtt_rd: block.
    Hypothesis h_set_g_rtt_rd_s : Genv.find_symbol ge _set_g_rtt_rd = Some b_set_g_rtt_rd.
    Hypothesis h_set_g_rtt_rd_p : Genv.find_funct_ptr ge b_set_g_rtt_rd
                                  = Some (External (EF_external _set_g_rtt_rd
                                                   (signature_of_type (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default))
                                         (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque set_g_rtt_rd_spec.

    Variable b_granule_memzero_mapped: block.
    Hypothesis h_granule_memzero_mapped_s : Genv.find_symbol ge _granule_memzero_mapped = Some b_granule_memzero_mapped.
    Hypothesis h_granule_memzero_mapped_p : Genv.find_funct_ptr ge b_granule_memzero_mapped
                                            = Some (External (EF_external _granule_memzero_mapped
                                                             (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                                   (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_memzero_mapped_spec.

    Variable b_granule_memzero: block.
    Hypothesis h_granule_memzero_s : Genv.find_symbol ge _granule_memzero = Some b_granule_memzero.
    Hypothesis h_granule_memzero_p : Genv.find_funct_ptr ge b_granule_memzero
                                     = Some (External (EF_external _granule_memzero
                                                      (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                            (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque granule_memzero_spec.

    Variable b_granule_set_state: block.
    Hypothesis h_granule_set_state_s : Genv.find_symbol ge _granule_set_state = Some b_granule_set_state.
    Hypothesis h_granule_set_state_p : Genv.find_funct_ptr ge b_granule_set_state
                                       = Some (External (EF_external _granule_set_state
                                                        (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                              (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque granule_set_state_spec.

    Variable b_buffer_unmap: block.
    Hypothesis h_buffer_unmap_s : Genv.find_symbol ge _buffer_unmap = Some b_buffer_unmap.
    Hypothesis h_buffer_unmap_p : Genv.find_funct_ptr ge b_buffer_unmap
                                  = Some (External (EF_external _buffer_unmap
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque buffer_unmap_spec.

    Lemma table_destroy_aux_body_correct:
      forall m d d' env le g_llt_base g_llt_offset g_tbl_base g_tbl_offset ll_table_base ll_table_offset level index map_addr res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTg_llt: PTree.get _g_llt le = Some (Vptr g_llt_base (Int.repr g_llt_offset)))
             (HPTg_tbl: PTree.get _g_tbl le = Some (Vptr g_tbl_base (Int.repr g_tbl_offset)))
             (HPTll_table: PTree.get _ll_table le = Some (Vptr ll_table_base (Int.repr ll_table_offset)))
             (HPTlevel: PTree.get _level le = Some (Vlong level))
             (HPTindex: PTree.get _index le = Some (Vlong index))
             (HPTmap_addr: PTree.get _map_addr le = Some (Vlong map_addr))
             (Hspec: table_destroy_aux_spec0 (g_llt_base, g_llt_offset) (g_tbl_base, g_tbl_offset) (ll_table_base, ll_table_offset) (VZ64 (Int64.unsigned level)) (VZ64 (Int64.unsigned index)) (VZ64 (Int64.unsigned map_addr)) d = Some (d', VZ64 (Int64.unsigned res))),
           exists le', (exec_stmt ge env le ((m, d): mem) table_destroy_aux_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
    Proof.
      solve_code_proof Hspec table_destroy_aux_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
