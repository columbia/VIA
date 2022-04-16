Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import TableAux2.Spec.
Require Import TableAux2.Layer.
Require Import TableAux3.Code.table_create_aux.

Require Import TableAux3.LowSpecs.table_create_aux.

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
      ⊕ _table_create_init_vacant ↦ gensem table_create_init_vacant_spec
      ⊕ _table_create_init_absent ↦ gensem table_create_init_absent_spec
      ⊕ _table_create_init_present ↦ gensem table_create_init_present_spec
      ⊕ _assert_cond ↦ gensem assert_cond_spec
      ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
      ⊕ _granule_get ↦ gensem granule_get_spec
      ⊕ _granule_set_state ↦ gensem granule_set_state_spec
      ⊕ _set_g_rtt_rd ↦ gensem set_g_rtt_rd_spec
      ⊕ _pgte_write ↦ gensem pgte_write_spec
      ⊕ _link_table ↦ gensem link_table_spec
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

    Variable b_table_create_init_vacant: block.
    Hypothesis h_table_create_init_vacant_s : Genv.find_symbol ge _table_create_init_vacant = Some b_table_create_init_vacant.
    Hypothesis h_table_create_init_vacant_p : Genv.find_funct_ptr ge b_table_create_init_vacant
                                              = Some (External (EF_external _table_create_init_vacant
                                                               (signature_of_type (Tcons tulong (Tcons Tptr (Tcons Tptr Tnil))) tvoid cc_default))
                                                     (Tcons tulong (Tcons Tptr (Tcons Tptr Tnil))) tvoid cc_default).
    Local Opaque table_create_init_vacant_spec.

    Variable b_table_create_init_absent: block.
    Hypothesis h_table_create_init_absent_s : Genv.find_symbol ge _table_create_init_absent = Some b_table_create_init_absent.
    Hypothesis h_table_create_init_absent_p : Genv.find_funct_ptr ge b_table_create_init_absent
                                              = Some (External (EF_external _table_create_init_absent
                                                               (signature_of_type (Tcons tulong (Tcons tulong (Tcons Tptr (Tcons Tptr Tnil)))) tvoid cc_default))
                                                     (Tcons tulong (Tcons tulong (Tcons Tptr (Tcons Tptr Tnil)))) tvoid cc_default).
    Local Opaque table_create_init_absent_spec.

    Variable b_table_create_init_present: block.
    Hypothesis h_table_create_init_present_s : Genv.find_symbol ge _table_create_init_present = Some b_table_create_init_present.
    Hypothesis h_table_create_init_present_p : Genv.find_funct_ptr ge b_table_create_init_present
                                               = Some (External (EF_external _table_create_init_present
                                                                (signature_of_type (Tcons tulong (Tcons Tptr (Tcons tulong (Tcons tulong (Tcons tulong (Tcons Tptr (Tcons Tptr Tnil))))))) tvoid cc_default))
                                                      (Tcons tulong (Tcons Tptr (Tcons tulong (Tcons tulong (Tcons tulong (Tcons Tptr (Tcons Tptr Tnil))))))) tvoid cc_default).
    Local Opaque table_create_init_present_spec.

    Variable b_assert_cond: block.
    Hypothesis h_assert_cond_s : Genv.find_symbol ge _assert_cond = Some b_assert_cond.
    Hypothesis h_assert_cond_p : Genv.find_funct_ptr ge b_assert_cond
                                 = Some (External (EF_external _assert_cond
                                                  (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                        (Tcons tuint Tnil) tvoid cc_default).
    Local Opaque assert_cond_spec.

    Variable b_buffer_unmap: block.
    Hypothesis h_buffer_unmap_s : Genv.find_symbol ge _buffer_unmap = Some b_buffer_unmap.
    Hypothesis h_buffer_unmap_p : Genv.find_funct_ptr ge b_buffer_unmap
                                  = Some (External (EF_external _buffer_unmap
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque buffer_unmap_spec.

    Variable b_granule_get: block.
    Hypothesis h_granule_get_s : Genv.find_symbol ge _granule_get = Some b_granule_get.
    Hypothesis h_granule_get_p : Genv.find_funct_ptr ge b_granule_get
                                 = Some (External (EF_external _granule_get
                                                  (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                        (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_get_spec.

    Variable b_granule_set_state: block.
    Hypothesis h_granule_set_state_s : Genv.find_symbol ge _granule_set_state = Some b_granule_set_state.
    Hypothesis h_granule_set_state_p : Genv.find_funct_ptr ge b_granule_set_state
                                       = Some (External (EF_external _granule_set_state
                                                        (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                              (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque granule_set_state_spec.

    Variable b_set_g_rtt_rd: block.
    Hypothesis h_set_g_rtt_rd_s : Genv.find_symbol ge _set_g_rtt_rd = Some b_set_g_rtt_rd.
    Hypothesis h_set_g_rtt_rd_p : Genv.find_funct_ptr ge b_set_g_rtt_rd
                                  = Some (External (EF_external _set_g_rtt_rd
                                                   (signature_of_type (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default))
                                         (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque set_g_rtt_rd_spec.

    Variable b_pgte_write: block.
    Hypothesis h_pgte_write_s : Genv.find_symbol ge _pgte_write = Some b_pgte_write.
    Hypothesis h_pgte_write_p : Genv.find_funct_ptr ge b_pgte_write
                                = Some (External (EF_external _pgte_write
                                                 (signature_of_type (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                       (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque pgte_write_spec.

    Variable b_link_table: block.
    Hypothesis h_link_table_s : Genv.find_symbol ge _link_table = Some b_link_table.
    Hypothesis h_link_table_p : Genv.find_funct_ptr ge b_link_table
                                = Some (External (EF_external _link_table
                                                 (signature_of_type (Tcons Tptr (Tcons Tptr (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default))
                                       (Tcons Tptr (Tcons Tptr (Tcons tulong (Tcons tulong Tnil)))) tvoid cc_default).
    Local Opaque link_table_spec.

  End BodyProof.

End CodeProof.
