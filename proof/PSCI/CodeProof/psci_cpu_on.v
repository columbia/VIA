Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PSCIAux2.Spec.
Require Import PSCIAux2.Layer.
Require Import PSCI.Code.psci_cpu_on.

Require Import PSCI.LowSpecs.psci_cpu_on.

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
    _get_rec_par_base ↦ gensem get_rec_par_base_spec
      ⊕ _get_rec_par_end ↦ gensem get_rec_par_end_spec
      ⊕ _set_psci_result_x0 ↦ gensem set_psci_result_x0_spec
      ⊕ _mpidr_to_rec_idx ↦ gensem mpidr_to_rec_idx_spec
      ⊕ _get_rec_rec_idx ↦ gensem get_rec_rec_idx_spec
      ⊕ _psci_lookup_target ↦ gensem psci_lookup_target_spec
      ⊕ _is_null ↦ gensem is_null_spec
      ⊕ _granule_map ↦ gensem granule_map_spec
      ⊕ _psci_cpu_on_target ↦ gensem psci_cpu_on_target_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_get_rec_par_base: block.
    Hypothesis h_get_rec_par_base_s : Genv.find_symbol ge _get_rec_par_base = Some b_get_rec_par_base.
    Hypothesis h_get_rec_par_base_p : Genv.find_funct_ptr ge b_get_rec_par_base
                                      = Some (External (EF_external _get_rec_par_base
                                                       (signature_of_type (Tcons Tptr Tnil) tulong cc_default))
                                             (Tcons Tptr Tnil) tulong cc_default).
    Local Opaque get_rec_par_base_spec.

    Variable b_get_rec_par_end: block.
    Hypothesis h_get_rec_par_end_s : Genv.find_symbol ge _get_rec_par_end = Some b_get_rec_par_end.
    Hypothesis h_get_rec_par_end_p : Genv.find_funct_ptr ge b_get_rec_par_end
                                     = Some (External (EF_external _get_rec_par_end
                                                      (signature_of_type (Tcons Tptr Tnil) tulong cc_default))
                                            (Tcons Tptr Tnil) tulong cc_default).
    Local Opaque get_rec_par_end_spec.

    Variable b_set_psci_result_x0: block.
    Hypothesis h_set_psci_result_x0_s : Genv.find_symbol ge _set_psci_result_x0 = Some b_set_psci_result_x0.
    Hypothesis h_set_psci_result_x0_p : Genv.find_funct_ptr ge b_set_psci_result_x0
                                        = Some (External (EF_external _set_psci_result_x0
                                                         (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                               (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_psci_result_x0_spec.

    Variable b_mpidr_to_rec_idx: block.
    Hypothesis h_mpidr_to_rec_idx_s : Genv.find_symbol ge _mpidr_to_rec_idx = Some b_mpidr_to_rec_idx.
    Hypothesis h_mpidr_to_rec_idx_p : Genv.find_funct_ptr ge b_mpidr_to_rec_idx
                                      = Some (External (EF_external _mpidr_to_rec_idx
                                                       (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                             (Tcons tulong Tnil) tulong cc_default).
    Local Opaque mpidr_to_rec_idx_spec.

    Variable b_get_rec_rec_idx: block.
    Hypothesis h_get_rec_rec_idx_s : Genv.find_symbol ge _get_rec_rec_idx = Some b_get_rec_rec_idx.
    Hypothesis h_get_rec_rec_idx_p : Genv.find_funct_ptr ge b_get_rec_rec_idx
                                     = Some (External (EF_external _get_rec_rec_idx
                                                      (signature_of_type (Tcons Tptr Tnil) tulong cc_default))
                                            (Tcons Tptr Tnil) tulong cc_default).
    Local Opaque get_rec_rec_idx_spec.

    Variable b_psci_lookup_target: block.
    Hypothesis h_psci_lookup_target_s : Genv.find_symbol ge _psci_lookup_target = Some b_psci_lookup_target.
    Hypothesis h_psci_lookup_target_p : Genv.find_funct_ptr ge b_psci_lookup_target
                                        = Some (External (EF_external _psci_lookup_target
                                                         (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) Tptr cc_default))
                                               (Tcons Tptr (Tcons tulong Tnil)) Tptr cc_default).
    Local Opaque psci_lookup_target_spec.

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

    Variable b_psci_cpu_on_target: block.
    Hypothesis h_psci_cpu_on_target_s : Genv.find_symbol ge _psci_cpu_on_target = Some b_psci_cpu_on_target.
    Hypothesis h_psci_cpu_on_target_p : Genv.find_funct_ptr ge b_psci_cpu_on_target
                                        = Some (External (EF_external _psci_cpu_on_target
                                                         (signature_of_type (Tcons Tptr (Tcons Tptr (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))))) tvoid cc_default))
                                               (Tcons Tptr (Tcons Tptr (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))))) tvoid cc_default).
    Local Opaque psci_cpu_on_target_spec.

    Lemma psci_cpu_on_body_correct:
      forall m d d' env le rec_base rec_offset target_cpu entry_point_address context_id
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTtarget_cpu: PTree.get _target_cpu le = Some (Vlong target_cpu))
             (HPTentry_point_address: PTree.get _entry_point_address le = Some (Vlong entry_point_address))
             (HPTcontext_id: PTree.get _context_id le = Some (Vlong context_id))
             (Hspec: psci_cpu_on_spec0 (rec_base, rec_offset) (VZ64 (Int64.unsigned target_cpu)) (VZ64 (Int64.unsigned entry_point_address)) (VZ64 (Int64.unsigned context_id)) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) psci_cpu_on_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec psci_cpu_on_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
