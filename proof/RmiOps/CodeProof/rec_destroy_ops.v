Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiAux2.Layer.
Require Import RmiOps.Code.rec_destroy_ops.

Require Import RmiOps.LowSpecs.rec_destroy_ops.

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
    _get_g_rec_rd ↦ gensem get_g_rec_rd_spec
      ⊕ _granule_map ↦ gensem granule_map_spec
      ⊕ _get_rec_g_rec ↦ gensem get_rec_g_rec_spec
      ⊕ _get_rec_g_rec_list ↦ gensem get_rec_g_rec_list_spec
      ⊕ _get_rec_rec_idx ↦ gensem get_rec_rec_idx_spec
      ⊕ _null_ptr ↦ gensem null_ptr_spec
      ⊕ _realm_set_rec_entry ↦ gensem realm_set_rec_entry_spec
      ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
      ⊕ _set_g_rec_rd ↦ gensem set_g_rec_rd_spec
      ⊕ _granule_memzero ↦ gensem granule_memzero_spec
      ⊕ _granule_set_state ↦ gensem granule_set_state_spec
      ⊕ _granule_unlock ↦ gensem granule_unlock_spec
      ⊕ _granule_put ↦ gensem granule_put_spec
      ⊕ _atomic_granule_put_release ↦ gensem atomic_granule_put_release_spec
      ⊕ _atomic_granule_put ↦ gensem atomic_granule_put_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_get_g_rec_rd: block.
    Hypothesis h_get_g_rec_rd_s : Genv.find_symbol ge _get_g_rec_rd = Some b_get_g_rec_rd.
    Hypothesis h_get_g_rec_rd_p : Genv.find_funct_ptr ge b_get_g_rec_rd
                                  = Some (External (EF_external _get_g_rec_rd
                                                   (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                         (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_g_rec_rd_spec.

    Variable b_granule_map: block.
    Hypothesis h_granule_map_s : Genv.find_symbol ge _granule_map = Some b_granule_map.
    Hypothesis h_granule_map_p : Genv.find_funct_ptr ge b_granule_map
                                 = Some (External (EF_external _granule_map
                                                  (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default))
                                        (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default).
    Local Opaque granule_map_spec.

    Variable b_get_rec_g_rec: block.
    Hypothesis h_get_rec_g_rec_s : Genv.find_symbol ge _get_rec_g_rec = Some b_get_rec_g_rec.
    Hypothesis h_get_rec_g_rec_p : Genv.find_funct_ptr ge b_get_rec_g_rec
                                   = Some (External (EF_external _get_rec_g_rec
                                                    (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                          (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rec_g_rec_spec.

    Variable b_get_rec_g_rec_list: block.
    Hypothesis h_get_rec_g_rec_list_s : Genv.find_symbol ge _get_rec_g_rec_list = Some b_get_rec_g_rec_list.
    Hypothesis h_get_rec_g_rec_list_p : Genv.find_funct_ptr ge b_get_rec_g_rec_list
                                        = Some (External (EF_external _get_rec_g_rec_list
                                                         (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                               (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rec_g_rec_list_spec.

    Variable b_get_rec_rec_idx: block.
    Hypothesis h_get_rec_rec_idx_s : Genv.find_symbol ge _get_rec_rec_idx = Some b_get_rec_rec_idx.
    Hypothesis h_get_rec_rec_idx_p : Genv.find_funct_ptr ge b_get_rec_rec_idx
                                     = Some (External (EF_external _get_rec_rec_idx
                                                      (signature_of_type (Tcons Tptr Tnil) tulong cc_default))
                                            (Tcons Tptr Tnil) tulong cc_default).
    Local Opaque get_rec_rec_idx_spec.

    Variable b_null_ptr: block.
    Hypothesis h_null_ptr_s : Genv.find_symbol ge _null_ptr = Some b_null_ptr.
    Hypothesis h_null_ptr_p : Genv.find_funct_ptr ge b_null_ptr
                              = Some (External (EF_external _null_ptr
                                               (signature_of_type Tnil Tptr cc_default))
                                     Tnil Tptr cc_default).
    Local Opaque null_ptr_spec.

    Variable b_realm_set_rec_entry: block.
    Hypothesis h_realm_set_rec_entry_s : Genv.find_symbol ge _realm_set_rec_entry = Some b_realm_set_rec_entry.
    Hypothesis h_realm_set_rec_entry_p : Genv.find_funct_ptr ge b_realm_set_rec_entry
                                         = Some (External (EF_external _realm_set_rec_entry
                                                          (signature_of_type (Tcons tulong (Tcons Tptr (Tcons Tptr Tnil))) tvoid cc_default))
                                                (Tcons tulong (Tcons Tptr (Tcons Tptr Tnil))) tvoid cc_default).
    Local Opaque realm_set_rec_entry_spec.

    Variable b_buffer_unmap: block.
    Hypothesis h_buffer_unmap_s : Genv.find_symbol ge _buffer_unmap = Some b_buffer_unmap.
    Hypothesis h_buffer_unmap_p : Genv.find_funct_ptr ge b_buffer_unmap
                                  = Some (External (EF_external _buffer_unmap
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque buffer_unmap_spec.

    Variable b_set_g_rec_rd: block.
    Hypothesis h_set_g_rec_rd_s : Genv.find_symbol ge _set_g_rec_rd = Some b_set_g_rec_rd.
    Hypothesis h_set_g_rec_rd_p : Genv.find_funct_ptr ge b_set_g_rec_rd
                                  = Some (External (EF_external _set_g_rec_rd
                                                   (signature_of_type (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default))
                                         (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque set_g_rec_rd_spec.

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

    Variable b_granule_unlock: block.
    Hypothesis h_granule_unlock_s : Genv.find_symbol ge _granule_unlock = Some b_granule_unlock.
    Hypothesis h_granule_unlock_p : Genv.find_funct_ptr ge b_granule_unlock
                                    = Some (External (EF_external _granule_unlock
                                                     (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                           (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_unlock_spec.

    Variable b_granule_put: block.
    Hypothesis h_granule_put_s : Genv.find_symbol ge _granule_put = Some b_granule_put.
    Hypothesis h_granule_put_p : Genv.find_funct_ptr ge b_granule_put
                                 = Some (External (EF_external _granule_put
                                                  (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                        (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_put_spec.

    Variable b_atomic_granule_put_release: block.
    Hypothesis h_atomic_granule_put_release_s : Genv.find_symbol ge _atomic_granule_put_release = Some b_atomic_granule_put_release.
    Hypothesis h_atomic_granule_put_release_p : Genv.find_funct_ptr ge b_atomic_granule_put_release
                                                = Some (External (EF_external _atomic_granule_put_release
                                                                 (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                                       (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque atomic_granule_put_release_spec.

    Variable b_atomic_granule_put: block.
    Hypothesis h_atomic_granule_put_s : Genv.find_symbol ge _atomic_granule_put = Some b_atomic_granule_put.
    Hypothesis h_atomic_granule_put_p : Genv.find_funct_ptr ge b_atomic_granule_put
                                        = Some (External (EF_external _atomic_granule_put
                                                         (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                               (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque atomic_granule_put_spec.

    Lemma rec_destroy_ops_body_correct:
      forall m d d' env le g_rec_base g_rec_offset
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTg_rec: PTree.get _g_rec le = Some (Vptr g_rec_base (Int.repr g_rec_offset)))
             (Hspec: rec_destroy_ops_spec0 (g_rec_base, g_rec_offset) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) rec_destroy_ops_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec rec_destroy_ops_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
