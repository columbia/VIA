Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import TableDataOpsRef3.Spec.
Require Import TableDataOpsIntro.Spec.
Require Import TableDataOpsRef3.Layer.
Require Import TableDataSMC.Code.smc_data_create.

Require Import TableDataSMC.LowSpecs.smc_data_create.

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
      ⊕ _get_rd_state ↦ gensem get_rd_state_spec
      ⊕ _data_create3 ↦ gensem data_create3_spec
      ⊕ _data_create ↦ gensem data_create_spec
      ⊕ _granule_set_state ↦ gensem granule_set_state_spec
      ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
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

    Variable b_get_rd_state: block.
    Hypothesis h_get_rd_state_s : Genv.find_symbol ge _get_rd_state = Some b_get_rd_state.
    Hypothesis h_get_rd_state_p : Genv.find_funct_ptr ge b_get_rd_state
                                  = Some (External (EF_external _get_rd_state
                                                   (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                         (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque get_rd_state_spec.

    Variable b_data_create3: block.
    Hypothesis h_data_create3_s : Genv.find_symbol ge _data_create3 = Some b_data_create3.
    Hypothesis h_data_create3_p : Genv.find_funct_ptr ge b_data_create3
                                  = Some (External (EF_external _data_create3
                                                   (signature_of_type (Tcons Tptr (Tcons tulong (Tcons tulong (Tcons Tptr (Tcons Tptr Tnil))))) tulong cc_default))
                                         (Tcons Tptr (Tcons tulong (Tcons tulong (Tcons Tptr (Tcons Tptr Tnil))))) tulong cc_default).
    Local Opaque data_create3_spec.

    Variable b_data_create: block.
    Hypothesis h_data_create_s : Genv.find_symbol ge _data_create = Some b_data_create.
    Hypothesis h_data_create_p : Genv.find_funct_ptr ge b_data_create
                                 = Some (External (EF_external _data_create
                                                  (signature_of_type (Tcons Tptr (Tcons tulong (Tcons tulong (Tcons Tptr (Tcons Tptr Tnil))))) tulong cc_default))
                                        (Tcons Tptr (Tcons tulong (Tcons tulong (Tcons Tptr (Tcons Tptr Tnil))))) tulong cc_default).
    Local Opaque data_create_spec.

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

    Variable b_granule_unlock: block.
    Hypothesis h_granule_unlock_s : Genv.find_symbol ge _granule_unlock = Some b_granule_unlock.
    Hypothesis h_granule_unlock_p : Genv.find_funct_ptr ge b_granule_unlock
                                    = Some (External (EF_external _granule_unlock
                                                     (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                           (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_unlock_spec.

  End BodyProof.

End CodeProof.
