Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import AbsAccessor.Layer.
Require Import BaremoreService.Code.asc_mark_nonsecure.

Require Import BaremoreService.LowSpecs.asc_mark_nonsecure.

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
    _addr_to_gidx ↦ gensem addr_to_gidx_spec
      ⊕ _check_granule_idx ↦ gensem check_granule_idx_spec
      ⊕ _find_spinlock ↦ gensem find_spinlock_spec
      ⊕ _spinlock_acquire ↦ gensem spinlock_acquire_spec
      ⊕ _get_pas ↦ gensem get_pas_spec
      ⊕ _set_pas ↦ gensem set_pas_spec
      ⊕ _tlbi_by_pa ↦ gensem tlbi_by_pa_spec
      ⊕ _spinlock_release ↦ gensem spinlock_release_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_addr_to_gidx: block.
    Hypothesis h_addr_to_gidx_s : Genv.find_symbol ge _addr_to_gidx = Some b_addr_to_gidx.
    Hypothesis h_addr_to_gidx_p : Genv.find_funct_ptr ge b_addr_to_gidx
                                  = Some (External (EF_external _addr_to_gidx
                                                   (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                         (Tcons tulong Tnil) tulong cc_default).
    Local Opaque addr_to_gidx_spec.

    Variable b_check_granule_idx: block.
    Hypothesis h_check_granule_idx_s : Genv.find_symbol ge _check_granule_idx = Some b_check_granule_idx.
    Hypothesis h_check_granule_idx_p : Genv.find_funct_ptr ge b_check_granule_idx
                                       = Some (External (EF_external _check_granule_idx
                                                        (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                              (Tcons tulong Tnil) tuint cc_default).
    Local Opaque check_granule_idx_spec.

    Variable b_find_spinlock: block.
    Hypothesis h_find_spinlock_s : Genv.find_symbol ge _find_spinlock = Some b_find_spinlock.
    Hypothesis h_find_spinlock_p : Genv.find_funct_ptr ge b_find_spinlock
                                   = Some (External (EF_external _find_spinlock
                                                    (signature_of_type (Tcons tulong Tnil) Tptr cc_default))
                                          (Tcons tulong Tnil) Tptr cc_default).
    Local Opaque find_spinlock_spec.

    Variable b_spinlock_acquire: block.
    Hypothesis h_spinlock_acquire_s : Genv.find_symbol ge _spinlock_acquire = Some b_spinlock_acquire.
    Hypothesis h_spinlock_acquire_p : Genv.find_funct_ptr ge b_spinlock_acquire
                                      = Some (External (EF_external _spinlock_acquire
                                                       (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                             (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque spinlock_acquire_spec.

    Variable b_get_pas: block.
    Hypothesis h_get_pas_s : Genv.find_symbol ge _get_pas = Some b_get_pas.
    Hypothesis h_get_pas_p : Genv.find_funct_ptr ge b_get_pas
                             = Some (External (EF_external _get_pas
                                              (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                    (Tcons tulong Tnil) tulong cc_default).
    Local Opaque get_pas_spec.

    Variable b_set_pas: block.
    Hypothesis h_set_pas_s : Genv.find_symbol ge _set_pas = Some b_set_pas.
    Hypothesis h_set_pas_p : Genv.find_funct_ptr ge b_set_pas
                             = Some (External (EF_external _set_pas
                                              (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default))
                                    (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_pas_spec.

    Variable b_tlbi_by_pa: block.
    Hypothesis h_tlbi_by_pa_s : Genv.find_symbol ge _tlbi_by_pa = Some b_tlbi_by_pa.
    Hypothesis h_tlbi_by_pa_p : Genv.find_funct_ptr ge b_tlbi_by_pa
                                = Some (External (EF_external _tlbi_by_pa
                                                 (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                       (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque tlbi_by_pa_spec.

    Variable b_spinlock_release: block.
    Hypothesis h_spinlock_release_s : Genv.find_symbol ge _spinlock_release = Some b_spinlock_release.
    Hypothesis h_spinlock_release_p : Genv.find_funct_ptr ge b_spinlock_release
                                      = Some (External (EF_external _spinlock_release
                                                       (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                             (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque spinlock_release_spec.

    Lemma asc_mark_nonsecure_body_correct:
      forall m d d' env le addr res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTaddr: PTree.get _addr le = Some (Vlong addr))
             (Hspec: asc_mark_nonsecure_spec0 (VZ64 (Int64.unsigned addr)) d = Some (d', VZ64 (Int64.unsigned res))),
           exists le', (exec_stmt ge env le ((m, d): mem) asc_mark_nonsecure_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
    Proof.
      solve_code_proof Hspec asc_mark_nonsecure_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
