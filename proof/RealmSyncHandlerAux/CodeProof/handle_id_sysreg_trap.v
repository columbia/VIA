Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmTimerHandler.Layer.
Require Import RealmSyncHandlerAux.Code.handle_id_sysreg_trap.

Require Import RealmSyncHandlerAux.LowSpecs.handle_id_sysreg_trap.

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
    _assert_cond ↦ gensem assert_cond_spec
      ⊕ _ESR_EL2_SYSREG_IS_WRITE ↦ gensem ESR_EL2_SYSREG_IS_WRITE_spec
      ⊕ _set_rec_regs ↦ gensem set_rec_regs_spec
      ⊕ _ESR_EL2_SYSREG_ISS_RT ↦ gensem ESR_EL2_SYSREG_ISS_RT_spec
      ⊕ _read_idreg ↦ gensem read_idreg_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_assert_cond: block.
    Hypothesis h_assert_cond_s : Genv.find_symbol ge _assert_cond = Some b_assert_cond.
    Hypothesis h_assert_cond_p : Genv.find_funct_ptr ge b_assert_cond
                                 = Some (External (EF_external _assert_cond
                                                  (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                        (Tcons tuint Tnil) tvoid cc_default).
    Local Opaque assert_cond_spec.

    Variable b_ESR_EL2_SYSREG_IS_WRITE: block.
    Hypothesis h_ESR_EL2_SYSREG_IS_WRITE_s : Genv.find_symbol ge _ESR_EL2_SYSREG_IS_WRITE = Some b_ESR_EL2_SYSREG_IS_WRITE.
    Hypothesis h_ESR_EL2_SYSREG_IS_WRITE_p : Genv.find_funct_ptr ge b_ESR_EL2_SYSREG_IS_WRITE
                                             = Some (External (EF_external _ESR_EL2_SYSREG_IS_WRITE
                                                              (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                                    (Tcons tulong Tnil) tuint cc_default).
    Local Opaque ESR_EL2_SYSREG_IS_WRITE_spec.

    Variable b_set_rec_regs: block.
    Hypothesis h_set_rec_regs_s : Genv.find_symbol ge _set_rec_regs = Some b_set_rec_regs.
    Hypothesis h_set_rec_regs_p : Genv.find_funct_ptr ge b_set_rec_regs
                                  = Some (External (EF_external _set_rec_regs
                                                   (signature_of_type (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                         (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque set_rec_regs_spec.

    Variable b_ESR_EL2_SYSREG_ISS_RT: block.
    Hypothesis h_ESR_EL2_SYSREG_ISS_RT_s : Genv.find_symbol ge _ESR_EL2_SYSREG_ISS_RT = Some b_ESR_EL2_SYSREG_ISS_RT.
    Hypothesis h_ESR_EL2_SYSREG_ISS_RT_p : Genv.find_funct_ptr ge b_ESR_EL2_SYSREG_ISS_RT
                                           = Some (External (EF_external _ESR_EL2_SYSREG_ISS_RT
                                                            (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                                  (Tcons tulong Tnil) tuint cc_default).
    Local Opaque ESR_EL2_SYSREG_ISS_RT_spec.

    Variable b_read_idreg: block.
    Hypothesis h_read_idreg_s : Genv.find_symbol ge _read_idreg = Some b_read_idreg.
    Hypothesis h_read_idreg_p : Genv.find_funct_ptr ge b_read_idreg
                                = Some (External (EF_external _read_idreg
                                                 (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                       (Tcons tuint Tnil) tulong cc_default).
    Local Opaque read_idreg_spec.

    Lemma handle_id_sysreg_trap_body_correct:
      forall m d d' env le rec_base rec_offset esr
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTesr: PTree.get _esr le = Some (Vlong esr))
             (Hspec: handle_id_sysreg_trap_spec0 (rec_base, rec_offset) (VZ64 (Int64.unsigned esr)) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) handle_id_sysreg_trap_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec handle_id_sysreg_trap_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
