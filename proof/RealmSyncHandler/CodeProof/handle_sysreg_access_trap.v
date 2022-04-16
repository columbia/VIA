Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmSyncHandlerAux.Spec.
Require Import RealmSyncHandlerAux.Layer.
Require Import RealmSyncHandler.Code.handle_sysreg_access_trap.

Require Import RealmSyncHandler.LowSpecs.handle_sysreg_access_trap.

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
      ⊕ _handle_id_sysreg_trap ↦ gensem handle_id_sysreg_trap_spec
      ⊕ _handle_timer_sysreg_trap ↦ gensem handle_timer_sysreg_trap_spec
      ⊕ _handle_icc_el1_sysreg_trap ↦ gensem handle_icc_el1_sysreg_trap_spec
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

    Variable b_handle_id_sysreg_trap: block.
    Hypothesis h_handle_id_sysreg_trap_s : Genv.find_symbol ge _handle_id_sysreg_trap = Some b_handle_id_sysreg_trap.
    Hypothesis h_handle_id_sysreg_trap_p : Genv.find_funct_ptr ge b_handle_id_sysreg_trap
                                           = Some (External (EF_external _handle_id_sysreg_trap
                                                            (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                                  (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque handle_id_sysreg_trap_spec.

    Variable b_handle_timer_sysreg_trap: block.
    Hypothesis h_handle_timer_sysreg_trap_s : Genv.find_symbol ge _handle_timer_sysreg_trap = Some b_handle_timer_sysreg_trap.
    Hypothesis h_handle_timer_sysreg_trap_p : Genv.find_funct_ptr ge b_handle_timer_sysreg_trap
                                              = Some (External (EF_external _handle_timer_sysreg_trap
                                                               (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                                     (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque handle_timer_sysreg_trap_spec.

    Variable b_handle_icc_el1_sysreg_trap: block.
    Hypothesis h_handle_icc_el1_sysreg_trap_s : Genv.find_symbol ge _handle_icc_el1_sysreg_trap = Some b_handle_icc_el1_sysreg_trap.
    Hypothesis h_handle_icc_el1_sysreg_trap_p : Genv.find_funct_ptr ge b_handle_icc_el1_sysreg_trap
                                                = Some (External (EF_external _handle_icc_el1_sysreg_trap
                                                                 (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                                       (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque handle_icc_el1_sysreg_trap_spec.

    Lemma handle_sysreg_access_trap_body_correct:
      forall m d d' env le rec_base rec_offset esr
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTesr: PTree.get _esr le = Some (Vlong esr))
             (Hspec: handle_sysreg_access_trap_spec0 (rec_base, rec_offset) (VZ64 (Int64.unsigned esr)) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) handle_sysreg_access_trap_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec handle_sysreg_access_trap_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
