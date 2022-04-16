Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import CtxtSwitch.Layer.
Require Import RealmTimerHandler.Code.handle_ptimer_sysreg_read.

Require Import RealmTimerHandler.LowSpecs.handle_ptimer_sysreg_read.

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
      ⊕ _sysreg_read ↦ gensem sysreg_read_spec
      ⊕ _set_rec_regs ↦ gensem set_rec_regs_spec
      ⊕ _emulate_timer_ctl_read ↦ gensem emulate_timer_ctl_read_spec
      ⊕ _get_rec_ptimer ↦ gensem get_rec_ptimer_spec
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

    Variable b_sysreg_read: block.
    Hypothesis h_sysreg_read_s : Genv.find_symbol ge _sysreg_read = Some b_sysreg_read.
    Hypothesis h_sysreg_read_p : Genv.find_funct_ptr ge b_sysreg_read
                                 = Some (External (EF_external _sysreg_read
                                                  (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                        (Tcons tuint Tnil) tulong cc_default).
    Local Opaque sysreg_read_spec.

    Variable b_set_rec_regs: block.
    Hypothesis h_set_rec_regs_s : Genv.find_symbol ge _set_rec_regs = Some b_set_rec_regs.
    Hypothesis h_set_rec_regs_p : Genv.find_funct_ptr ge b_set_rec_regs
                                  = Some (External (EF_external _set_rec_regs
                                                   (signature_of_type (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                         (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque set_rec_regs_spec.

    Variable b_emulate_timer_ctl_read: block.
    Hypothesis h_emulate_timer_ctl_read_s : Genv.find_symbol ge _emulate_timer_ctl_read = Some b_emulate_timer_ctl_read.
    Hypothesis h_emulate_timer_ctl_read_p : Genv.find_funct_ptr ge b_emulate_timer_ctl_read
                                            = Some (External (EF_external _emulate_timer_ctl_read
                                                             (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tulong cc_default))
                                                   (Tcons Tptr (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque emulate_timer_ctl_read_spec.

    Variable b_get_rec_ptimer: block.
    Hypothesis h_get_rec_ptimer_s : Genv.find_symbol ge _get_rec_ptimer = Some b_get_rec_ptimer.
    Hypothesis h_get_rec_ptimer_p : Genv.find_funct_ptr ge b_get_rec_ptimer
                                    = Some (External (EF_external _get_rec_ptimer
                                                     (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                           (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rec_ptimer_spec.

    Lemma handle_ptimer_sysreg_read_body_correct:
      forall m d d' env le rec_base rec_offset esr
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTesr: PTree.get _esr le = Some (Vlong esr))
             (Hspec: handle_ptimer_sysreg_read_spec0 (rec_base, rec_offset) (VZ64 (Int64.unsigned esr)) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) handle_ptimer_sysreg_read_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec handle_ptimer_sysreg_read_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
