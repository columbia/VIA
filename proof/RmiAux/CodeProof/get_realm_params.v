Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import BaremoreSMC.Layer.
Require Import RmiAux.Code.get_realm_params.

Require Import RmiAux.LowSpecs.get_realm_params.

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
      ⊕ _granule_map ↦ gensem granule_map_spec
      ⊕ _ns_granule_map ↦ gensem ns_granule_map_spec
      ⊕ _ns_buffer_read_realm_params ↦ gensem ns_buffer_read_realm_params_spec
      ⊕ _ns_buffer_unmap ↦ gensem ns_buffer_unmap_spec
      ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
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

    Variable b_ns_buffer_read_realm_params: block.
    Hypothesis h_ns_buffer_read_realm_params_s : Genv.find_symbol ge _ns_buffer_read_realm_params = Some b_ns_buffer_read_realm_params.
    Hypothesis h_ns_buffer_read_realm_params_p : Genv.find_funct_ptr ge b_ns_buffer_read_realm_params
                                                 = Some (External (EF_external _ns_buffer_read_realm_params
                                                                  (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                                        (Tcons tuint Tnil) tuint cc_default).
    Local Opaque ns_buffer_read_realm_params_spec.

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

    Lemma get_realm_params_body_correct:
      forall m d d' env le realm_params_addr res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrealm_params_addr: PTree.get _realm_params_addr le = Some (Vlong realm_params_addr))
             (Hspec: get_realm_params_spec0 (VZ64 (Int64.unsigned realm_params_addr)) d = Some (d',Int.unsigned res)),
           exists le', (exec_stmt ge env le ((m, d): mem) get_realm_params_body E0 le' (m, d') (Out_return (Some (Vint res, tuint)))).
    Proof.
      solve_code_proof Hspec get_realm_params_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
