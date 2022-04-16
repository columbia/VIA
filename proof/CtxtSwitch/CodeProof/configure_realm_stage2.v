Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import CtxtSwitchAux.Layer.
Require Import CtxtSwitch.Code.configure_realm_stage2.

Require Import CtxtSwitch.LowSpecs.configure_realm_stage2.

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
    _get_rec_common_sysregs ↦ gensem get_rec_common_sysregs_spec
      ⊕ _sysreg_write ↦ gensem sysreg_write_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_get_rec_common_sysregs: block.
    Hypothesis h_get_rec_common_sysregs_s : Genv.find_symbol ge _get_rec_common_sysregs = Some b_get_rec_common_sysregs.
    Hypothesis h_get_rec_common_sysregs_p : Genv.find_funct_ptr ge b_get_rec_common_sysregs
                                            = Some (External (EF_external _get_rec_common_sysregs
                                                             (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tulong cc_default))
                                                   (Tcons Tptr (Tcons tuint Tnil)) tulong cc_default).
    Local Opaque get_rec_common_sysregs_spec.

    Variable b_sysreg_write: block.
    Hypothesis h_sysreg_write_s : Genv.find_symbol ge _sysreg_write = Some b_sysreg_write.
    Hypothesis h_sysreg_write_p : Genv.find_funct_ptr ge b_sysreg_write
                                  = Some (External (EF_external _sysreg_write
                                                   (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                         (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque sysreg_write_spec.

    Lemma configure_realm_stage2_body_correct:
      forall m d d' env le rec_base rec_offset
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (Hspec: configure_realm_stage2_spec0 (rec_base, rec_offset) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) configure_realm_stage2_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec configure_realm_stage2_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
