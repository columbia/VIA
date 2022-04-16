Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import BaremoreSMC.Layer.
Require Import RmiAux.Code.init_rec_sysregs.

Require Import RmiAux.LowSpecs.init_rec_sysregs.

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
    _set_rec_sysregs ↦ gensem set_rec_sysregs_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_set_rec_sysregs: block.
    Hypothesis h_set_rec_sysregs_s : Genv.find_symbol ge _set_rec_sysregs = Some b_set_rec_sysregs.
    Hypothesis h_set_rec_sysregs_p : Genv.find_funct_ptr ge b_set_rec_sysregs
                                     = Some (External (EF_external _set_rec_sysregs
                                                      (signature_of_type (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                            (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque set_rec_sysregs_spec.

    Lemma init_rec_sysregs_body_correct:
      forall m d d' env le rec_base rec_offset mpidr
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTmpidr: PTree.get _mpidr le = Some (Vlong mpidr))
             (Hspec: init_rec_sysregs_spec0 (rec_base, rec_offset) (VZ64 (Int64.unsigned mpidr)) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) init_rec_sysregs_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec init_rec_sysregs_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
