Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import TableWalk.Spec.
Require Import AbsAccessor.Spec.
Require Import TableAux3.Spec.
Require Import TableWalk.Layer.
Require Import TableDataOpsIntro.Code.table_create.

Require Import TableDataOpsIntro.LowSpecs.table_create.

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
    _table_walk_lock_unlock ↦ gensem table_walk_lock_unlock_spec
      ⊕ _get_wi_g_llt ↦ gensem get_wi_g_llt_spec
      ⊕ _get_wi_index ↦ gensem get_wi_index_spec
      ⊕ _is_null ↦ gensem is_null_spec
      ⊕ _granule_map ↦ gensem granule_map_spec
      ⊕ _pgte_read ↦ gensem pgte_read_spec
      ⊕ _entry_is_table ↦ gensem entry_is_table_spec
      ⊕ _table_create_aux ↦ gensem table_create_aux_spec
      ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
      ⊕ _granule_unlock ↦ gensem granule_unlock_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_table_walk_lock_unlock: block.
    Hypothesis h_table_walk_lock_unlock_s : Genv.find_symbol ge _table_walk_lock_unlock = Some b_table_walk_lock_unlock.
    Hypothesis h_table_walk_lock_unlock_p : Genv.find_funct_ptr ge b_table_walk_lock_unlock
                                            = Some (External (EF_external _table_walk_lock_unlock
                                                             (signature_of_type (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                                   (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque table_walk_lock_unlock_spec.

    Variable b_get_wi_g_llt: block.
    Hypothesis h_get_wi_g_llt_s : Genv.find_symbol ge _get_wi_g_llt = Some b_get_wi_g_llt.
    Hypothesis h_get_wi_g_llt_p : Genv.find_funct_ptr ge b_get_wi_g_llt
                                  = Some (External (EF_external _get_wi_g_llt
                                                   (signature_of_type Tnil Tptr cc_default))
                                         Tnil Tptr cc_default).
    Local Opaque get_wi_g_llt_spec.

    Variable b_get_wi_index: block.
    Hypothesis h_get_wi_index_s : Genv.find_symbol ge _get_wi_index = Some b_get_wi_index.
    Hypothesis h_get_wi_index_p : Genv.find_funct_ptr ge b_get_wi_index
                                  = Some (External (EF_external _get_wi_index
                                                   (signature_of_type Tnil tulong cc_default))
                                         Tnil tulong cc_default).
    Local Opaque get_wi_index_spec.

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

    Variable b_pgte_read: block.
    Hypothesis h_pgte_read_s : Genv.find_symbol ge _pgte_read = Some b_pgte_read.
    Hypothesis h_pgte_read_p : Genv.find_funct_ptr ge b_pgte_read
                               = Some (External (EF_external _pgte_read
                                                (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tulong cc_default))
                                      (Tcons Tptr (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque pgte_read_spec.

    Variable b_entry_is_table: block.
    Hypothesis h_entry_is_table_s : Genv.find_symbol ge _entry_is_table = Some b_entry_is_table.
    Hypothesis h_entry_is_table_p : Genv.find_funct_ptr ge b_entry_is_table
                                    = Some (External (EF_external _entry_is_table
                                                     (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                           (Tcons tulong Tnil) tuint cc_default).
    Local Opaque entry_is_table_spec.

    Variable b_table_create_aux: block.
    Hypothesis h_table_create_aux_s : Genv.find_symbol ge _table_create_aux = Some b_table_create_aux.
    Hypothesis h_table_create_aux_p : Genv.find_funct_ptr ge b_table_create_aux
                                      = Some (External (EF_external _table_create_aux
                                                       (signature_of_type (Tcons Tptr (Tcons Tptr (Tcons Tptr (Tcons tulong (Tcons Tptr (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tulong Tnil))))))))) tvoid cc_default))
                                             (Tcons Tptr (Tcons Tptr (Tcons Tptr (Tcons tulong (Tcons Tptr (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tulong Tnil))))))))) tvoid cc_default).
    Local Opaque table_create_aux_spec.

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

    Lemma table_create_body_correct:
      forall m d d' env le g_rd_base g_rd_offset map_addr level g_rtt_base g_rtt_offset rtt_addr res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTg_rd: PTree.get _g_rd le = Some (Vptr g_rd_base (Int.repr g_rd_offset)))
             (HPTmap_addr: PTree.get _map_addr le = Some (Vlong map_addr))
             (HPTlevel: PTree.get _level le = Some (Vlong level))
             (HPTg_rtt: PTree.get _g_rtt le = Some (Vptr g_rtt_base (Int.repr g_rtt_offset)))
             (HPTrtt_addr: PTree.get _rtt_addr le = Some (Vlong rtt_addr))
             (Hspec: table_create_spec0 (g_rd_base, g_rd_offset) (VZ64 (Int64.unsigned map_addr)) (VZ64 (Int64.unsigned level)) (g_rtt_base, g_rtt_offset) (VZ64 (Int64.unsigned rtt_addr)) d = Some (d', VZ64 (Int64.unsigned res))),
           exists le', (exec_stmt ge env le ((m, d): mem) table_create_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
    Proof.
      solve_code_proof Hspec table_create_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
