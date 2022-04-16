Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiAux2.Spec.
Require Import RmiAux2.Layer.
Require Import RmiOps.Code.rec_create_ops.

Require Import RmiOps.LowSpecs.rec_create_ops.

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
    _granule_set_state ↦ gensem granule_set_state_spec
      ⊕ _realm_set_rec_entry ↦ gensem realm_set_rec_entry_spec
      ⊕ _init_rec_read_only ↦ gensem init_rec_read_only_spec
      ⊕ _init_rec_regs ↦ gensem init_rec_regs_spec
      ⊕ _init_rec_rvic_state ↦ gensem init_rec_rvic_state_spec
      ⊕ _get_rec_rvic ↦ gensem get_rec_rvic_spec
      ⊕ _get_rd_par_base ↦ gensem get_rd_par_base_spec
      ⊕ _set_rec_par_base ↦ gensem set_rec_par_base_spec
      ⊕ _get_rd_par_end ↦ gensem get_rd_par_end_spec
      ⊕ _set_rec_par_end ↦ gensem set_rec_par_end_spec
      ⊕ _set_rec_g_rd ↦ gensem set_rec_g_rd_spec
      ⊕ _get_rd_g_rec_list ↦ gensem get_rd_g_rec_list_spec
      ⊕ _set_rec_g_rec_list ↦ gensem set_rec_g_rec_list_spec
      ⊕ _rec_granule_measure ↦ gensem rec_granule_measure_spec
      ⊕ _set_g_rec_rd ↦ gensem set_g_rec_rd_spec
      ⊕ _granule_get ↦ gensem granule_get_spec
      ⊕ _atomic_granule_get ↦ gensem atomic_granule_get_spec
      ⊕ _get_rec_params_flags ↦ gensem get_rec_params_flags_spec
      ⊕ _set_rec_runnable ↦ gensem set_rec_runnable_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_granule_set_state: block.
    Hypothesis h_granule_set_state_s : Genv.find_symbol ge _granule_set_state = Some b_granule_set_state.
    Hypothesis h_granule_set_state_p : Genv.find_funct_ptr ge b_granule_set_state
                                       = Some (External (EF_external _granule_set_state
                                                        (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                              (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque granule_set_state_spec.

    Variable b_realm_set_rec_entry: block.
    Hypothesis h_realm_set_rec_entry_s : Genv.find_symbol ge _realm_set_rec_entry = Some b_realm_set_rec_entry.
    Hypothesis h_realm_set_rec_entry_p : Genv.find_funct_ptr ge b_realm_set_rec_entry
                                         = Some (External (EF_external _realm_set_rec_entry
                                                          (signature_of_type (Tcons tulong (Tcons Tptr (Tcons Tptr Tnil))) tvoid cc_default))
                                                (Tcons tulong (Tcons Tptr (Tcons Tptr Tnil))) tvoid cc_default).
    Local Opaque realm_set_rec_entry_spec.

    Variable b_init_rec_read_only: block.
    Hypothesis h_init_rec_read_only_s : Genv.find_symbol ge _init_rec_read_only = Some b_init_rec_read_only.
    Hypothesis h_init_rec_read_only_p : Genv.find_funct_ptr ge b_init_rec_read_only
                                        = Some (External (EF_external _init_rec_read_only
                                                         (signature_of_type (Tcons Tptr (Tcons Tptr (Tcons tulong Tnil))) tvoid cc_default))
                                               (Tcons Tptr (Tcons Tptr (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque init_rec_read_only_spec.

    Variable b_init_rec_regs: block.
    Hypothesis h_init_rec_regs_s : Genv.find_symbol ge _init_rec_regs = Some b_init_rec_regs.
    Hypothesis h_init_rec_regs_p : Genv.find_funct_ptr ge b_init_rec_regs
                                   = Some (External (EF_external _init_rec_regs
                                                    (signature_of_type (Tcons Tptr (Tcons tulong (Tcons Tptr Tnil))) tvoid cc_default))
                                          (Tcons Tptr (Tcons tulong (Tcons Tptr Tnil))) tvoid cc_default).
    Local Opaque init_rec_regs_spec.

    Variable b_init_rec_rvic_state: block.
    Hypothesis h_init_rec_rvic_state_s : Genv.find_symbol ge _init_rec_rvic_state = Some b_init_rec_rvic_state.
    Hypothesis h_init_rec_rvic_state_p : Genv.find_funct_ptr ge b_init_rec_rvic_state
                                         = Some (External (EF_external _init_rec_rvic_state
                                                          (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                                (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque init_rec_rvic_state_spec.

    Variable b_get_rec_rvic: block.
    Hypothesis h_get_rec_rvic_s : Genv.find_symbol ge _get_rec_rvic = Some b_get_rec_rvic.
    Hypothesis h_get_rec_rvic_p : Genv.find_funct_ptr ge b_get_rec_rvic
                                  = Some (External (EF_external _get_rec_rvic
                                                   (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                         (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rec_rvic_spec.

    Variable b_get_rd_par_base: block.
    Hypothesis h_get_rd_par_base_s : Genv.find_symbol ge _get_rd_par_base = Some b_get_rd_par_base.
    Hypothesis h_get_rd_par_base_p : Genv.find_funct_ptr ge b_get_rd_par_base
                                     = Some (External (EF_external _get_rd_par_base
                                                      (signature_of_type (Tcons Tptr Tnil) tulong cc_default))
                                            (Tcons Tptr Tnil) tulong cc_default).
    Local Opaque get_rd_par_base_spec.

    Variable b_set_rec_par_base: block.
    Hypothesis h_set_rec_par_base_s : Genv.find_symbol ge _set_rec_par_base = Some b_set_rec_par_base.
    Hypothesis h_set_rec_par_base_p : Genv.find_funct_ptr ge b_set_rec_par_base
                                      = Some (External (EF_external _set_rec_par_base
                                                       (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                             (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_rec_par_base_spec.

    Variable b_get_rd_par_end: block.
    Hypothesis h_get_rd_par_end_s : Genv.find_symbol ge _get_rd_par_end = Some b_get_rd_par_end.
    Hypothesis h_get_rd_par_end_p : Genv.find_funct_ptr ge b_get_rd_par_end
                                    = Some (External (EF_external _get_rd_par_end
                                                     (signature_of_type (Tcons Tptr Tnil) tulong cc_default))
                                           (Tcons Tptr Tnil) tulong cc_default).
    Local Opaque get_rd_par_end_spec.

    Variable b_set_rec_par_end: block.
    Hypothesis h_set_rec_par_end_s : Genv.find_symbol ge _set_rec_par_end = Some b_set_rec_par_end.
    Hypothesis h_set_rec_par_end_p : Genv.find_funct_ptr ge b_set_rec_par_end
                                     = Some (External (EF_external _set_rec_par_end
                                                      (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                            (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_rec_par_end_spec.

    Variable b_set_rec_g_rd: block.
    Hypothesis h_set_rec_g_rd_s : Genv.find_symbol ge _set_rec_g_rd = Some b_set_rec_g_rd.
    Hypothesis h_set_rec_g_rd_p : Genv.find_funct_ptr ge b_set_rec_g_rd
                                  = Some (External (EF_external _set_rec_g_rd
                                                   (signature_of_type (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default))
                                         (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque set_rec_g_rd_spec.

    Variable b_get_rd_g_rec_list: block.
    Hypothesis h_get_rd_g_rec_list_s : Genv.find_symbol ge _get_rd_g_rec_list = Some b_get_rd_g_rec_list.
    Hypothesis h_get_rd_g_rec_list_p : Genv.find_funct_ptr ge b_get_rd_g_rec_list
                                       = Some (External (EF_external _get_rd_g_rec_list
                                                        (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                              (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rd_g_rec_list_spec.

    Variable b_set_rec_g_rec_list: block.
    Hypothesis h_set_rec_g_rec_list_s : Genv.find_symbol ge _set_rec_g_rec_list = Some b_set_rec_g_rec_list.
    Hypothesis h_set_rec_g_rec_list_p : Genv.find_funct_ptr ge b_set_rec_g_rec_list
                                        = Some (External (EF_external _set_rec_g_rec_list
                                                         (signature_of_type (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default))
                                               (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque set_rec_g_rec_list_spec.

    Variable b_rec_granule_measure: block.
    Hypothesis h_rec_granule_measure_s : Genv.find_symbol ge _rec_granule_measure = Some b_rec_granule_measure.
    Hypothesis h_rec_granule_measure_p : Genv.find_funct_ptr ge b_rec_granule_measure
                                         = Some (External (EF_external _rec_granule_measure
                                                          (signature_of_type (Tcons Tptr (Tcons Tptr (Tcons tulong Tnil))) tvoid cc_default))
                                                (Tcons Tptr (Tcons Tptr (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque rec_granule_measure_spec.

    Variable b_set_g_rec_rd: block.
    Hypothesis h_set_g_rec_rd_s : Genv.find_symbol ge _set_g_rec_rd = Some b_set_g_rec_rd.
    Hypothesis h_set_g_rec_rd_p : Genv.find_funct_ptr ge b_set_g_rec_rd
                                  = Some (External (EF_external _set_g_rec_rd
                                                   (signature_of_type (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default))
                                         (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque set_g_rec_rd_spec.

    Variable b_granule_get: block.
    Hypothesis h_granule_get_s : Genv.find_symbol ge _granule_get = Some b_granule_get.
    Hypothesis h_granule_get_p : Genv.find_funct_ptr ge b_granule_get
                                 = Some (External (EF_external _granule_get
                                                  (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                        (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_get_spec.

    Variable b_atomic_granule_get: block.
    Hypothesis h_atomic_granule_get_s : Genv.find_symbol ge _atomic_granule_get = Some b_atomic_granule_get.
    Hypothesis h_atomic_granule_get_p : Genv.find_funct_ptr ge b_atomic_granule_get
                                        = Some (External (EF_external _atomic_granule_get
                                                         (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                               (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque atomic_granule_get_spec.

    Variable b_get_rec_params_flags: block.
    Hypothesis h_get_rec_params_flags_s : Genv.find_symbol ge _get_rec_params_flags = Some b_get_rec_params_flags.
    Hypothesis h_get_rec_params_flags_p : Genv.find_funct_ptr ge b_get_rec_params_flags
                                          = Some (External (EF_external _get_rec_params_flags
                                                           (signature_of_type Tnil tulong cc_default))
                                                 Tnil tulong cc_default).
    Local Opaque get_rec_params_flags_spec.

    Variable b_set_rec_runnable: block.
    Hypothesis h_set_rec_runnable_s : Genv.find_symbol ge _set_rec_runnable = Some b_set_rec_runnable.
    Hypothesis h_set_rec_runnable_p : Genv.find_funct_ptr ge b_set_rec_runnable
                                      = Some (External (EF_external _set_rec_runnable
                                                       (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                             (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque set_rec_runnable_spec.

    (* Lemma rec_create_ops_body_correct:
      forall m d d' env le g_rd_base g_rd_offset g_rec_base g_rec_offset rd_base rd_offset rec_list_base rec_list_offset rec_base rec_offset mpidr rec_idx
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTg_rd: PTree.get _g_rd le = Some (Vptr g_rd_base (Int.repr g_rd_offset)))
             (HPTg_rec: PTree.get _g_rec le = Some (Vptr g_rec_base (Int.repr g_rec_offset)))
             (HPTrd: PTree.get _rd le = Some (Vptr rd_base (Int.repr rd_offset)))
             (HPTrec_list: PTree.get _rec_list le = Some (Vptr rec_list_base (Int.repr rec_list_offset)))
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTmpidr: PTree.get _mpidr le = Some (Vlong mpidr))
             (HPTrec_idx: PTree.get _rec_idx le = Some (Vlong rec_idx))
             (Hspec: rec_create_ops_spec0 (g_rd_base, g_rd_offset) (g_rec_base, g_rec_offset) (rd_base, rd_offset) (rec_list_base, rec_list_offset) (rec_base, rec_offset) (VZ64 (Int64.unsigned mpidr)) (VZ64 (Int64.unsigned rec_idx)) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) rec_create_ops_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec rec_create_ops_body; eexists; solve_proof_low.
    Qed. *)

  End BodyProof.

End CodeProof.
