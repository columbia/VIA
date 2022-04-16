Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import PSCIHandler.Layer.
Require Import RVIC.Code.is_untrusted_intid.

Require Import RVIC.LowSpecs.is_untrusted_intid.

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
    ∅.

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Lemma is_untrusted_intid_body_correct:
      forall m d env le intid res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTintid: PTree.get _intid le = Some (Vlong intid))
             (Hspec: is_untrusted_intid_spec0 (VZ64 (Int64.unsigned intid)) d = Some (Int.unsigned res)),
           exists le', (exec_stmt ge env le ((m, d): mem) is_untrusted_intid_body E0 le' (m, d) (Out_return (Some (Vint res, tuint)))).
    Proof.
      solve_code_proof Hspec is_untrusted_intid_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
