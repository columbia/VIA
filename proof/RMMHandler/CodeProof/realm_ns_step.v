Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import SMCHandler.Layer.
Require Import RMMHandler.Code.realm_ns_step.

Require Import RMMHandler.LowSpecs.realm_ns_step.

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
    _user_step ↦ gensem user_step_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_user_step: block.
    Hypothesis h_user_step_s : Genv.find_symbol ge _user_step = Some b_user_step.
    Hypothesis h_user_step_p : Genv.find_funct_ptr ge b_user_step
                               = Some (External (EF_external _user_step
                                                (signature_of_type Tnil tulong cc_default))
                                      Tnil tulong cc_default).
    Local Opaque user_step_spec.

    Lemma realm_ns_step_body_correct:
      forall m d d' env le  res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (Hspec: realm_ns_step_spec0  d = Some (d', VZ64 (Int64.unsigned res))),
           exists le', (exec_stmt ge env le ((m, d): mem) realm_ns_step_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
    Proof.
      solve_code_proof Hspec realm_ns_step_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
