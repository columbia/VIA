Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiSMC.Layer.
Require Import PSCIAux.Code.psci_reset_rec.

Require Import PSCIAux.LowSpecs.psci_reset_rec.

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
    _set_rec_pstate ↦ gensem set_rec_pstate_spec
      ⊕ _set_rec_sysregs ↦ gensem set_rec_sysregs_spec
      ⊕ _get_rec_sysregs ↦ gensem get_rec_sysregs_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_set_rec_pstate: block.
    Hypothesis h_set_rec_pstate_s : Genv.find_symbol ge _set_rec_pstate = Some b_set_rec_pstate.
    Hypothesis h_set_rec_pstate_p : Genv.find_funct_ptr ge b_set_rec_pstate
                                    = Some (External (EF_external _set_rec_pstate
                                                     (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                           (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_rec_pstate_spec.

    Variable b_set_rec_sysregs: block.
    Hypothesis h_set_rec_sysregs_s : Genv.find_symbol ge _set_rec_sysregs = Some b_set_rec_sysregs.
    Hypothesis h_set_rec_sysregs_p : Genv.find_funct_ptr ge b_set_rec_sysregs
                                     = Some (External (EF_external _set_rec_sysregs
                                                      (signature_of_type (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                            (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque set_rec_sysregs_spec.

    Variable b_get_rec_sysregs: block.
    Hypothesis h_get_rec_sysregs_s : Genv.find_symbol ge _get_rec_sysregs = Some b_get_rec_sysregs.
    Hypothesis h_get_rec_sysregs_p : Genv.find_funct_ptr ge b_get_rec_sysregs
                                     = Some (External (EF_external _get_rec_sysregs
                                                      (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tulong cc_default))
                                            (Tcons Tptr (Tcons tuint Tnil)) tulong cc_default).
    Local Opaque get_rec_sysregs_spec.

    Lemma psci_reset_rec_body_correct:
      forall m d d' env le rec_base rec_offset target_rec_base target_rec_offset
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTtarget_rec: PTree.get _target_rec le = Some (Vptr target_rec_base (Int.repr target_rec_offset)))
             (Hspec: psci_reset_rec_spec0 (rec_base, rec_offset) (target_rec_base, target_rec_offset) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) psci_reset_rec_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec psci_reset_rec_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
