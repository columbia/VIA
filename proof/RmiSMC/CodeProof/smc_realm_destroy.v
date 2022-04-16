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
Require Import RmiSMC.Code.smc_realm_destroy.

Require Import RmiSMC.LowSpecs.smc_realm_destroy.

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
    _find_lock_unused_granule ↦ gensem find_lock_unused_granule_spec
      ⊕ _is_null ↦ gensem is_null_spec
      ⊕ _granule_map ↦ gensem granule_map_spec
      ⊕ _get_rd_g_rtt ↦ gensem get_rd_g_rtt_spec
      ⊕ _get_rd_g_rec_list ↦ gensem get_rd_g_rec_list_spec
      ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
      ⊕ _granule_lock ↦ gensem granule_lock_spec
      ⊕ _get_g_rtt_refcount ↦ gensem get_g_rtt_refcount_spec
      ⊕ _granule_unlock ↦ gensem granule_unlock_spec
      ⊕ _realm_destroy_ops ↦ gensem realm_destroy_ops_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_find_lock_unused_granule: block.
    Hypothesis h_find_lock_unused_granule_s : Genv.find_symbol ge _find_lock_unused_granule = Some b_find_lock_unused_granule.
    Hypothesis h_find_lock_unused_granule_p : Genv.find_funct_ptr ge b_find_lock_unused_granule
                                              = Some (External (EF_external _find_lock_unused_granule
                                                               (signature_of_type (Tcons tulong (Tcons tulong Tnil)) Tptr cc_default))
                                                     (Tcons tulong (Tcons tulong Tnil)) Tptr cc_default).
    Local Opaque find_lock_unused_granule_spec.

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

    Variable b_get_rd_g_rtt: block.
    Hypothesis h_get_rd_g_rtt_s : Genv.find_symbol ge _get_rd_g_rtt = Some b_get_rd_g_rtt.
    Hypothesis h_get_rd_g_rtt_p : Genv.find_funct_ptr ge b_get_rd_g_rtt
                                  = Some (External (EF_external _get_rd_g_rtt
                                                   (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                         (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rd_g_rtt_spec.

    Variable b_get_rd_g_rec_list: block.
    Hypothesis h_get_rd_g_rec_list_s : Genv.find_symbol ge _get_rd_g_rec_list = Some b_get_rd_g_rec_list.
    Hypothesis h_get_rd_g_rec_list_p : Genv.find_funct_ptr ge b_get_rd_g_rec_list
                                       = Some (External (EF_external _get_rd_g_rec_list
                                                        (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                              (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rd_g_rec_list_spec.

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

    Variable b_get_g_rtt_refcount: block.
    Hypothesis h_get_g_rtt_refcount_s : Genv.find_symbol ge _get_g_rtt_refcount = Some b_get_g_rtt_refcount.
    Hypothesis h_get_g_rtt_refcount_p : Genv.find_funct_ptr ge b_get_g_rtt_refcount
                                        = Some (External (EF_external _get_g_rtt_refcount
                                                         (signature_of_type (Tcons Tptr Tnil) tulong cc_default))
                                               (Tcons Tptr Tnil) tulong cc_default).
    Local Opaque get_g_rtt_refcount_spec.

    Variable b_granule_unlock: block.
    Hypothesis h_granule_unlock_s : Genv.find_symbol ge _granule_unlock = Some b_granule_unlock.
    Hypothesis h_granule_unlock_p : Genv.find_funct_ptr ge b_granule_unlock
                                    = Some (External (EF_external _granule_unlock
                                                     (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                           (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_unlock_spec.

    Variable b_realm_destroy_ops: block.
    Hypothesis h_realm_destroy_ops_s : Genv.find_symbol ge _realm_destroy_ops = Some b_realm_destroy_ops.
    Hypothesis h_realm_destroy_ops_p : Genv.find_funct_ptr ge b_realm_destroy_ops
                                       = Some (External (EF_external _realm_destroy_ops
                                                        (signature_of_type (Tcons Tptr (Tcons Tptr (Tcons Tptr Tnil))) tvoid cc_default))
                                              (Tcons Tptr (Tcons Tptr (Tcons Tptr Tnil))) tvoid cc_default).
    Local Opaque realm_destroy_ops_spec.

    Lemma smc_realm_destroy_body_correct:
      forall m d d' env le rd_addr res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrd_addr: PTree.get _rd_addr le = Some (Vlong rd_addr))
             (Hspec: smc_realm_destroy_spec0 (VZ64 (Int64.unsigned rd_addr)) d = Some (d', VZ64 (Int64.unsigned res))),
           exists le', (exec_stmt ge env le ((m, d): mem) smc_realm_destroy_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
    Proof.
      solve_code_proof Hspec smc_realm_destroy_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
