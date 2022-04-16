Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import CtxtSwitch.Layer.
Require Import RealmTimerHandler.Code.handle_ptimer_sysreg_write.

Require Import RealmTimerHandler.LowSpecs.handle_ptimer_sysreg_write.

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
    _ESR_EL2_SYSREG_ISS_RT ↦ gensem ESR_EL2_SYSREG_ISS_RT_spec
      ⊕ _get_rec_regs ↦ gensem get_rec_regs_spec
      ⊕ _sysreg_write ↦ gensem sysreg_write_spec
      ⊕ _set_rec_ptimer_masked ↦ gensem set_rec_ptimer_masked_spec
      ⊕ _sysreg_read ↦ gensem sysreg_read_spec
      ⊕ _get_rec_ptimer_masked ↦ gensem get_rec_ptimer_masked_spec
      ⊕ _get_rec_ptimer ↦ gensem get_rec_ptimer_spec
      ⊕ _timer_condition_met ↦ gensem timer_condition_met_spec
      ⊕ _set_rec_ptimer_asserted ↦ gensem set_rec_ptimer_asserted_spec
      ⊕ _get_rec_sysregs ↦ gensem get_rec_sysregs_spec
      ⊕ _set_rec_sysregs ↦ gensem set_rec_sysregs_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_ESR_EL2_SYSREG_ISS_RT: block.
    Hypothesis h_ESR_EL2_SYSREG_ISS_RT_s : Genv.find_symbol ge _ESR_EL2_SYSREG_ISS_RT = Some b_ESR_EL2_SYSREG_ISS_RT.
    Hypothesis h_ESR_EL2_SYSREG_ISS_RT_p : Genv.find_funct_ptr ge b_ESR_EL2_SYSREG_ISS_RT
                                           = Some (External (EF_external _ESR_EL2_SYSREG_ISS_RT
                                                            (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                                  (Tcons tulong Tnil) tuint cc_default).
    Local Opaque ESR_EL2_SYSREG_ISS_RT_spec.

    Variable b_get_rec_regs: block.
    Hypothesis h_get_rec_regs_s : Genv.find_symbol ge _get_rec_regs = Some b_get_rec_regs.
    Hypothesis h_get_rec_regs_p : Genv.find_funct_ptr ge b_get_rec_regs
                                  = Some (External (EF_external _get_rec_regs
                                                   (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tulong cc_default))
                                         (Tcons Tptr (Tcons tuint Tnil)) tulong cc_default).
    Local Opaque get_rec_regs_spec.

    Variable b_sysreg_write: block.
    Hypothesis h_sysreg_write_s : Genv.find_symbol ge _sysreg_write = Some b_sysreg_write.
    Hypothesis h_sysreg_write_p : Genv.find_funct_ptr ge b_sysreg_write
                                  = Some (External (EF_external _sysreg_write
                                                   (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                         (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque sysreg_write_spec.

    Variable b_set_rec_ptimer_masked: block.
    Hypothesis h_set_rec_ptimer_masked_s : Genv.find_symbol ge _set_rec_ptimer_masked = Some b_set_rec_ptimer_masked.
    Hypothesis h_set_rec_ptimer_masked_p : Genv.find_funct_ptr ge b_set_rec_ptimer_masked
                                           = Some (External (EF_external _set_rec_ptimer_masked
                                                            (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                                  (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque set_rec_ptimer_masked_spec.

    Variable b_sysreg_read: block.
    Hypothesis h_sysreg_read_s : Genv.find_symbol ge _sysreg_read = Some b_sysreg_read.
    Hypothesis h_sysreg_read_p : Genv.find_funct_ptr ge b_sysreg_read
                                 = Some (External (EF_external _sysreg_read
                                                  (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                        (Tcons tuint Tnil) tulong cc_default).
    Local Opaque sysreg_read_spec.

    Variable b_get_rec_ptimer_masked: block.
    Hypothesis h_get_rec_ptimer_masked_s : Genv.find_symbol ge _get_rec_ptimer_masked = Some b_get_rec_ptimer_masked.
    Hypothesis h_get_rec_ptimer_masked_p : Genv.find_funct_ptr ge b_get_rec_ptimer_masked
                                           = Some (External (EF_external _get_rec_ptimer_masked
                                                            (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                                  (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque get_rec_ptimer_masked_spec.

    Variable b_get_rec_ptimer: block.
    Hypothesis h_get_rec_ptimer_s : Genv.find_symbol ge _get_rec_ptimer = Some b_get_rec_ptimer.
    Hypothesis h_get_rec_ptimer_p : Genv.find_funct_ptr ge b_get_rec_ptimer
                                    = Some (External (EF_external _get_rec_ptimer
                                                     (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                           (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rec_ptimer_spec.

    Variable b_timer_condition_met: block.
    Hypothesis h_timer_condition_met_s : Genv.find_symbol ge _timer_condition_met = Some b_timer_condition_met.
    Hypothesis h_timer_condition_met_p : Genv.find_funct_ptr ge b_timer_condition_met
                                         = Some (External (EF_external _timer_condition_met
                                                          (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                                (Tcons tulong Tnil) tuint cc_default).
    Local Opaque timer_condition_met_spec.

    Variable b_set_rec_ptimer_asserted: block.
    Hypothesis h_set_rec_ptimer_asserted_s : Genv.find_symbol ge _set_rec_ptimer_asserted = Some b_set_rec_ptimer_asserted.
    Hypothesis h_set_rec_ptimer_asserted_p : Genv.find_funct_ptr ge b_set_rec_ptimer_asserted
                                             = Some (External (EF_external _set_rec_ptimer_asserted
                                                              (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                                    (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque set_rec_ptimer_asserted_spec.

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

    Lemma handle_ptimer_sysreg_write_body_correct:
      forall m d d' env le rec_base rec_offset esr
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTesr: PTree.get _esr le = Some (Vlong esr))
             (Hspec: handle_ptimer_sysreg_write_spec0 (rec_base, rec_offset) (VZ64 (Int64.unsigned esr)) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) handle_ptimer_sysreg_write_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec handle_ptimer_sysreg_write_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
