Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import CtxtSwitchAux.Spec.
Require Import AbsAccessor.Spec.
Require Import CtxtSwitchAux.Layer.
Require Import CtxtSwitch.Code.save_realm_state.

Require Import CtxtSwitch.LowSpecs.save_realm_state.

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
    _save_sysreg_state ↦ gensem save_sysreg_state_spec
      ⊕ _sysreg_read ↦ gensem sysreg_read_spec
      ⊕ _set_rec_pc ↦ gensem set_rec_pc_spec
      ⊕ _set_rec_pstate ↦ gensem set_rec_pstate_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_save_sysreg_state: block.
    Hypothesis h_save_sysreg_state_s : Genv.find_symbol ge _save_sysreg_state = Some b_save_sysreg_state.
    Hypothesis h_save_sysreg_state_p : Genv.find_funct_ptr ge b_save_sysreg_state
                                       = Some (External (EF_external _save_sysreg_state
                                                        (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                              (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque save_sysreg_state_spec.

    Variable b_sysreg_read: block.
    Hypothesis h_sysreg_read_s : Genv.find_symbol ge _sysreg_read = Some b_sysreg_read.
    Hypothesis h_sysreg_read_p : Genv.find_funct_ptr ge b_sysreg_read
                                 = Some (External (EF_external _sysreg_read
                                                  (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                        (Tcons tuint Tnil) tulong cc_default).
    Local Opaque sysreg_read_spec.

    Variable b_set_rec_pc: block.
    Hypothesis h_set_rec_pc_s : Genv.find_symbol ge _set_rec_pc = Some b_set_rec_pc.
    Hypothesis h_set_rec_pc_p : Genv.find_funct_ptr ge b_set_rec_pc
                                = Some (External (EF_external _set_rec_pc
                                                 (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                       (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_rec_pc_spec.

    Variable b_set_rec_pstate: block.
    Hypothesis h_set_rec_pstate_s : Genv.find_symbol ge _set_rec_pstate = Some b_set_rec_pstate.
    Hypothesis h_set_rec_pstate_p : Genv.find_funct_ptr ge b_set_rec_pstate
                                    = Some (External (EF_external _set_rec_pstate
                                                     (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                           (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_rec_pstate_spec.

    Lemma save_realm_state_body_correct:
      forall m d d' env le rec_base rec_offset
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (Hspec: save_realm_state_spec0 (rec_base, rec_offset) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) save_realm_state_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec save_realm_state_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
