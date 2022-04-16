Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PendingCheckAux.Spec.
Require Import RVIC4.Spec.
Require Import PendingCheckAux.Layer.
Require Import PendingCheck.Code.check_pending_ptimers.

Require Import PendingCheck.LowSpecs.check_pending_ptimers.

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
    _get_rec_g_rec ↦ gensem get_rec_g_rec_spec
      ⊕ _sysreg_read ↦ gensem sysreg_read_spec
      ⊕ _check_timer_became_asserted ↦ gensem check_timer_became_asserted_spec
      ⊕ _get_rec_ptimer ↦ gensem get_rec_ptimer_spec
      ⊕ _granule_lock ↦ gensem granule_lock_spec
      ⊕ _sysreg_write ↦ gensem sysreg_write_spec
      ⊕ _get_rec_sysregs ↦ gensem get_rec_sysregs_spec
      ⊕ _set_rec_sysregs ↦ gensem set_rec_sysregs_spec
      ⊕ _set_rec_ptimer_asserted ↦ gensem set_rec_ptimer_asserted_spec
      ⊕ _rvic_set_pending ↦ gensem rvic_set_pending_spec
      ⊕ _get_rec_rvic ↦ gensem get_rec_rvic_spec
      ⊕ _granule_unlock ↦ gensem granule_unlock_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_get_rec_g_rec: block.
    Hypothesis h_get_rec_g_rec_s : Genv.find_symbol ge _get_rec_g_rec = Some b_get_rec_g_rec.
    Hypothesis h_get_rec_g_rec_p : Genv.find_funct_ptr ge b_get_rec_g_rec
                                   = Some (External (EF_external _get_rec_g_rec
                                                    (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                          (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rec_g_rec_spec.

    Variable b_sysreg_read: block.
    Hypothesis h_sysreg_read_s : Genv.find_symbol ge _sysreg_read = Some b_sysreg_read.
    Hypothesis h_sysreg_read_p : Genv.find_funct_ptr ge b_sysreg_read
                                 = Some (External (EF_external _sysreg_read
                                                  (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                        (Tcons tuint Tnil) tulong cc_default).
    Local Opaque sysreg_read_spec.

    Variable b_check_timer_became_asserted: block.
    Hypothesis h_check_timer_became_asserted_s : Genv.find_symbol ge _check_timer_became_asserted = Some b_check_timer_became_asserted.
    Hypothesis h_check_timer_became_asserted_p : Genv.find_funct_ptr ge b_check_timer_became_asserted
                                                 = Some (External (EF_external _check_timer_became_asserted
                                                                  (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tuint cc_default))
                                                        (Tcons Tptr (Tcons tulong Tnil)) tuint cc_default).
    Local Opaque check_timer_became_asserted_spec.

    Variable b_get_rec_ptimer: block.
    Hypothesis h_get_rec_ptimer_s : Genv.find_symbol ge _get_rec_ptimer = Some b_get_rec_ptimer.
    Hypothesis h_get_rec_ptimer_p : Genv.find_funct_ptr ge b_get_rec_ptimer
                                    = Some (External (EF_external _get_rec_ptimer
                                                     (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                           (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rec_ptimer_spec.

    Variable b_granule_lock: block.
    Hypothesis h_granule_lock_s : Genv.find_symbol ge _granule_lock = Some b_granule_lock.
    Hypothesis h_granule_lock_p : Genv.find_funct_ptr ge b_granule_lock
                                  = Some (External (EF_external _granule_lock
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_lock_spec.

    Variable b_sysreg_write: block.
    Hypothesis h_sysreg_write_s : Genv.find_symbol ge _sysreg_write = Some b_sysreg_write.
    Hypothesis h_sysreg_write_p : Genv.find_funct_ptr ge b_sysreg_write
                                  = Some (External (EF_external _sysreg_write
                                                   (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                         (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque sysreg_write_spec.

    Variable b_get_rec_sysregs: block.
    Hypothesis h_get_rec_sysregs_s : Genv.find_symbol ge _get_rec_sysregs = Some b_get_rec_sysregs.
    Hypothesis h_get_rec_sysregs_p : Genv.find_funct_ptr ge b_get_rec_sysregs
                                     = Some (External (EF_external _get_rec_sysregs
                                                      (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tulong cc_default))
                                            (Tcons Tptr (Tcons tuint Tnil)) tulong cc_default).
    Local Opaque get_rec_sysregs_spec.

    Variable b_set_rec_sysregs: block.
    Hypothesis h_set_rec_sysregs_s : Genv.find_symbol ge _set_rec_sysregs = Some b_set_rec_sysregs.
    Hypothesis h_set_rec_sysregs_p : Genv.find_funct_ptr ge b_set_rec_sysregs
                                     = Some (External (EF_external _set_rec_sysregs
                                                      (signature_of_type (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                            (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque set_rec_sysregs_spec.

    Variable b_set_rec_ptimer_asserted: block.
    Hypothesis h_set_rec_ptimer_asserted_s : Genv.find_symbol ge _set_rec_ptimer_asserted = Some b_set_rec_ptimer_asserted.
    Hypothesis h_set_rec_ptimer_asserted_p : Genv.find_funct_ptr ge b_set_rec_ptimer_asserted
                                             = Some (External (EF_external _set_rec_ptimer_asserted
                                                              (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                                    (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque set_rec_ptimer_asserted_spec.

    Variable b_rvic_set_pending: block.
    Hypothesis h_rvic_set_pending_s : Genv.find_symbol ge _rvic_set_pending = Some b_rvic_set_pending.
    Hypothesis h_rvic_set_pending_p : Genv.find_funct_ptr ge b_rvic_set_pending
                                      = Some (External (EF_external _rvic_set_pending
                                                       (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                             (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque rvic_set_pending_spec.

    Variable b_get_rec_rvic: block.
    Hypothesis h_get_rec_rvic_s : Genv.find_symbol ge _get_rec_rvic = Some b_get_rec_rvic.
    Hypothesis h_get_rec_rvic_p : Genv.find_funct_ptr ge b_get_rec_rvic
                                  = Some (External (EF_external _get_rec_rvic
                                                   (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                         (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rec_rvic_spec.

    Variable b_granule_unlock: block.
    Hypothesis h_granule_unlock_s : Genv.find_symbol ge _granule_unlock = Some b_granule_unlock.
    Hypothesis h_granule_unlock_p : Genv.find_funct_ptr ge b_granule_unlock
                                    = Some (External (EF_external _granule_unlock
                                                     (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                           (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_unlock_spec.

    Lemma check_pending_ptimers_body_correct:
      forall m d d' env le rec_base rec_offset
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (Hspec: check_pending_ptimers_spec0 (rec_base, rec_offset) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) check_pending_ptimers_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec check_pending_ptimers_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
