Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiAux.Spec.
Require Import RmiAux2.Layer.
Require Import RmiOps.Code.realm_create_ops.

Require Import RmiOps.LowSpecs.realm_create_ops.

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
    _get_locked_granule ↦ gensem get_locked_granule_spec
      ⊕ _set_g_rtt_rd ↦ gensem set_g_rtt_rd_spec
      ⊕ _granule_set_state ↦ gensem granule_set_state_spec
      ⊕ _granule_unlock ↦ gensem granule_unlock_spec
      ⊕ _granule_map ↦ gensem granule_map_spec
      ⊕ _set_rd_state ↦ gensem set_rd_state_spec
      ⊕ _get_realm_params ↦ gensem get_realm_params_spec
      ⊕ _get_realm_params_par_base ↦ gensem get_realm_params_par_base_spec
      ⊕ _get_realm_params_par_size ↦ gensem get_realm_params_par_size_spec
      ⊕ _set_rd_par_base ↦ gensem set_rd_par_base_spec
      ⊕ _set_rd_par_end ↦ gensem set_rd_par_end_spec
      ⊕ _set_rd_g_rtt ↦ gensem set_rd_g_rtt_spec
      ⊕ _set_rd_g_rec_list ↦ gensem set_rd_g_rec_list_spec
      ⊕ _get_realm_params_measurement_algo ↦ gensem get_realm_params_measurement_algo_spec
      ⊕ _set_rd_measurement_algo ↦ gensem set_rd_measurement_algo_spec
      ⊕ _measurement_start ↦ gensem measurement_start_spec
      ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_get_locked_granule: block.
    Hypothesis h_get_locked_granule_s : Genv.find_symbol ge _get_locked_granule = Some b_get_locked_granule.
    Hypothesis h_get_locked_granule_p : Genv.find_funct_ptr ge b_get_locked_granule
                                        = Some (External (EF_external _get_locked_granule
                                                         (signature_of_type (Tcons tuint Tnil) Tptr cc_default))
                                               (Tcons tuint Tnil) Tptr cc_default).
    Local Opaque get_locked_granule_spec.

    Variable b_set_g_rtt_rd: block.
    Hypothesis h_set_g_rtt_rd_s : Genv.find_symbol ge _set_g_rtt_rd = Some b_set_g_rtt_rd.
    Hypothesis h_set_g_rtt_rd_p : Genv.find_funct_ptr ge b_set_g_rtt_rd
                                  = Some (External (EF_external _set_g_rtt_rd
                                                   (signature_of_type (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default))
                                         (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque set_g_rtt_rd_spec.

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

    Variable b_granule_map: block.
    Hypothesis h_granule_map_s : Genv.find_symbol ge _granule_map = Some b_granule_map.
    Hypothesis h_granule_map_p : Genv.find_funct_ptr ge b_granule_map
                                 = Some (External (EF_external _granule_map
                                                  (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default))
                                        (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default).
    Local Opaque granule_map_spec.

    Variable b_set_rd_state: block.
    Hypothesis h_set_rd_state_s : Genv.find_symbol ge _set_rd_state = Some b_set_rd_state.
    Hypothesis h_set_rd_state_p : Genv.find_funct_ptr ge b_set_rd_state
                                  = Some (External (EF_external _set_rd_state
                                                   (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                         (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque set_rd_state_spec.

    Variable b_get_realm_params: block.
    Hypothesis h_get_realm_params_s : Genv.find_symbol ge _get_realm_params = Some b_get_realm_params.
    Hypothesis h_get_realm_params_p : Genv.find_funct_ptr ge b_get_realm_params
                                      = Some (External (EF_external _get_realm_params
                                                       (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                             (Tcons tulong Tnil) tuint cc_default).
    Local Opaque get_realm_params_spec.

    Variable b_get_realm_params_par_base: block.
    Hypothesis h_get_realm_params_par_base_s : Genv.find_symbol ge _get_realm_params_par_base = Some b_get_realm_params_par_base.
    Hypothesis h_get_realm_params_par_base_p : Genv.find_funct_ptr ge b_get_realm_params_par_base
                                               = Some (External (EF_external _get_realm_params_par_base
                                                                (signature_of_type Tnil tulong cc_default))
                                                      Tnil tulong cc_default).
    Local Opaque get_realm_params_par_base_spec.

    Variable b_get_realm_params_par_size: block.
    Hypothesis h_get_realm_params_par_size_s : Genv.find_symbol ge _get_realm_params_par_size = Some b_get_realm_params_par_size.
    Hypothesis h_get_realm_params_par_size_p : Genv.find_funct_ptr ge b_get_realm_params_par_size
                                               = Some (External (EF_external _get_realm_params_par_size
                                                                (signature_of_type Tnil tulong cc_default))
                                                      Tnil tulong cc_default).
    Local Opaque get_realm_params_par_size_spec.

    Variable b_set_rd_par_base: block.
    Hypothesis h_set_rd_par_base_s : Genv.find_symbol ge _set_rd_par_base = Some b_set_rd_par_base.
    Hypothesis h_set_rd_par_base_p : Genv.find_funct_ptr ge b_set_rd_par_base
                                     = Some (External (EF_external _set_rd_par_base
                                                      (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                            (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_rd_par_base_spec.

    Variable b_set_rd_par_end: block.
    Hypothesis h_set_rd_par_end_s : Genv.find_symbol ge _set_rd_par_end = Some b_set_rd_par_end.
    Hypothesis h_set_rd_par_end_p : Genv.find_funct_ptr ge b_set_rd_par_end
                                    = Some (External (EF_external _set_rd_par_end
                                                     (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                           (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_rd_par_end_spec.

    Variable b_set_rd_g_rtt: block.
    Hypothesis h_set_rd_g_rtt_s : Genv.find_symbol ge _set_rd_g_rtt = Some b_set_rd_g_rtt.
    Hypothesis h_set_rd_g_rtt_p : Genv.find_funct_ptr ge b_set_rd_g_rtt
                                  = Some (External (EF_external _set_rd_g_rtt
                                                   (signature_of_type (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default))
                                         (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque set_rd_g_rtt_spec.

    Variable b_set_rd_g_rec_list: block.
    Hypothesis h_set_rd_g_rec_list_s : Genv.find_symbol ge _set_rd_g_rec_list = Some b_set_rd_g_rec_list.
    Hypothesis h_set_rd_g_rec_list_p : Genv.find_funct_ptr ge b_set_rd_g_rec_list
                                       = Some (External (EF_external _set_rd_g_rec_list
                                                        (signature_of_type (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default))
                                              (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque set_rd_g_rec_list_spec.

    Variable b_get_realm_params_measurement_algo: block.
    Hypothesis h_get_realm_params_measurement_algo_s : Genv.find_symbol ge _get_realm_params_measurement_algo = Some b_get_realm_params_measurement_algo.
    Hypothesis h_get_realm_params_measurement_algo_p : Genv.find_funct_ptr ge b_get_realm_params_measurement_algo
                                                       = Some (External (EF_external _get_realm_params_measurement_algo
                                                                        (signature_of_type Tnil tulong cc_default))
                                                              Tnil tulong cc_default).
    Local Opaque get_realm_params_measurement_algo_spec.

    Variable b_set_rd_measurement_algo: block.
    Hypothesis h_set_rd_measurement_algo_s : Genv.find_symbol ge _set_rd_measurement_algo = Some b_set_rd_measurement_algo.
    Hypothesis h_set_rd_measurement_algo_p : Genv.find_funct_ptr ge b_set_rd_measurement_algo
                                             = Some (External (EF_external _set_rd_measurement_algo
                                                              (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                                    (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_rd_measurement_algo_spec.

    Variable b_measurement_start: block.
    Hypothesis h_measurement_start_s : Genv.find_symbol ge _measurement_start = Some b_measurement_start.
    Hypothesis h_measurement_start_p : Genv.find_funct_ptr ge b_measurement_start
                                       = Some (External (EF_external _measurement_start
                                                        (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                              (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque measurement_start_spec.

    Variable b_buffer_unmap: block.
    Hypothesis h_buffer_unmap_s : Genv.find_symbol ge _buffer_unmap = Some b_buffer_unmap.
    Hypothesis h_buffer_unmap_p : Genv.find_funct_ptr ge b_buffer_unmap
                                  = Some (External (EF_external _buffer_unmap
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque buffer_unmap_spec.

    Lemma realm_create_ops_body_correct:
      forall m d d' env le 
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (Hspec: realm_create_ops_spec0  d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) realm_create_ops_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec realm_create_ops_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
