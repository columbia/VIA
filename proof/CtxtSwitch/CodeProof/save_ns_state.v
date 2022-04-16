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
Require Import CtxtSwitch.Code.save_ns_state.

Require Import CtxtSwitch.LowSpecs.save_ns_state.

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
    _save_ns_state_sysreg_state ↦ gensem save_ns_state_sysreg_state_spec
      ⊕ _sysreg_read ↦ gensem sysreg_read_spec
      ⊕ _set_ns_state ↦ gensem set_ns_state_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_save_ns_state_sysreg_state: block.
    Hypothesis h_save_ns_state_sysreg_state_s : Genv.find_symbol ge _save_ns_state_sysreg_state = Some b_save_ns_state_sysreg_state.
    Hypothesis h_save_ns_state_sysreg_state_p : Genv.find_funct_ptr ge b_save_ns_state_sysreg_state
                                                = Some (External (EF_external _save_ns_state_sysreg_state
                                                                 (signature_of_type Tnil tvoid cc_default))
                                                       Tnil tvoid cc_default).
    Local Opaque save_ns_state_sysreg_state_spec.

    Variable b_sysreg_read: block.
    Hypothesis h_sysreg_read_s : Genv.find_symbol ge _sysreg_read = Some b_sysreg_read.
    Hypothesis h_sysreg_read_p : Genv.find_funct_ptr ge b_sysreg_read
                                 = Some (External (EF_external _sysreg_read
                                                  (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                        (Tcons tuint Tnil) tulong cc_default).
    Local Opaque sysreg_read_spec.

    Variable b_set_ns_state: block.
    Hypothesis h_set_ns_state_s : Genv.find_symbol ge _set_ns_state = Some b_set_ns_state.
    Hypothesis h_set_ns_state_p : Genv.find_funct_ptr ge b_set_ns_state
                                  = Some (External (EF_external _set_ns_state
                                                   (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                         (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_ns_state_spec.

    Lemma save_ns_state_body_correct:
      forall m d d' env le 
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (Hspec: save_ns_state_spec0  d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) save_ns_state_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec save_ns_state_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
