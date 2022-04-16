Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RunSMC.Layer.
Require Import TableAux.Code.find_next_level_idx.

Require Import TableAux.LowSpecs.find_next_level_idx.

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
      ⊕ _pgte_read ↦ gensem pgte_read_spec
      ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
      ⊕ _entry_is_table ↦ gensem entry_is_table_spec
      ⊕ _null_ptr ↦ gensem null_ptr_spec
      ⊕ _find_granule ↦ gensem find_granule_spec
      ⊕ _entry_to_phys ↦ gensem entry_to_phys_spec
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

    Variable b_pgte_read: block.
    Hypothesis h_pgte_read_s : Genv.find_symbol ge _pgte_read = Some b_pgte_read.
    Hypothesis h_pgte_read_p : Genv.find_funct_ptr ge b_pgte_read
                               = Some (External (EF_external _pgte_read
                                                (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tulong cc_default))
                                      (Tcons Tptr (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque pgte_read_spec.

    Variable b_buffer_unmap: block.
    Hypothesis h_buffer_unmap_s : Genv.find_symbol ge _buffer_unmap = Some b_buffer_unmap.
    Hypothesis h_buffer_unmap_p : Genv.find_funct_ptr ge b_buffer_unmap
                                  = Some (External (EF_external _buffer_unmap
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque buffer_unmap_spec.

    Variable b_entry_is_table: block.
    Hypothesis h_entry_is_table_s : Genv.find_symbol ge _entry_is_table = Some b_entry_is_table.
    Hypothesis h_entry_is_table_p : Genv.find_funct_ptr ge b_entry_is_table
                                    = Some (External (EF_external _entry_is_table
                                                     (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                           (Tcons tulong Tnil) tuint cc_default).
    Local Opaque entry_is_table_spec.

    Variable b_null_ptr: block.
    Hypothesis h_null_ptr_s : Genv.find_symbol ge _null_ptr = Some b_null_ptr.
    Hypothesis h_null_ptr_p : Genv.find_funct_ptr ge b_null_ptr
                              = Some (External (EF_external _null_ptr
                                               (signature_of_type Tnil Tptr cc_default))
                                     Tnil Tptr cc_default).
    Local Opaque null_ptr_spec.

    Variable b_find_granule: block.
    Hypothesis h_find_granule_s : Genv.find_symbol ge _find_granule = Some b_find_granule.
    Hypothesis h_find_granule_p : Genv.find_funct_ptr ge b_find_granule
                                  = Some (External (EF_external _find_granule
                                                   (signature_of_type (Tcons tulong Tnil) Tptr cc_default))
                                         (Tcons tulong Tnil) Tptr cc_default).
    Local Opaque find_granule_spec.

    Variable b_entry_to_phys: block.
    Hypothesis h_entry_to_phys_s : Genv.find_symbol ge _entry_to_phys = Some b_entry_to_phys.
    Hypothesis h_entry_to_phys_p : Genv.find_funct_ptr ge b_entry_to_phys
                                   = Some (External (EF_external _entry_to_phys
                                                    (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
                                          (Tcons tulong (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque entry_to_phys_spec.

    Lemma find_next_level_idx_body_correct:
      forall m d d' env le g_tbl_base g_tbl_offset idx res_base res_offset
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTg_tbl: PTree.get _g_tbl le = Some (Vptr g_tbl_base (Int.repr g_tbl_offset)))
             (HPTidx: PTree.get _idx le = Some (Vlong idx))
             (Hspec: find_next_level_idx_spec0 (g_tbl_base, g_tbl_offset) (VZ64 (Int64.unsigned idx)) d = Some (d', (res_base, res_offset))),
           exists le', (exec_stmt ge env le ((m, d): mem) find_next_level_idx_body E0 le' (m, d') (Out_return (Some (Vptr res_base (Int.repr res_offset), Tptr)))).
    Proof.
      solve_code_proof Hspec find_next_level_idx_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
