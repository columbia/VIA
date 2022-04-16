Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import RVIC.Layer.
Require Import RVIC2.Code.rvic_target_is_valid.

Require Import RVIC2.LowSpecs.rvic_target_is_valid.

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

    Lemma rvic_target_is_valid_body_correct:
      forall m d env le target res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTtarget: PTree.get _target le = Some (Vlong target))
             (Hspec: rvic_target_is_valid_spec0 (VZ64 (Int64.unsigned target)) d = Some (Int.unsigned res)),
           exists le', (exec_stmt ge env le ((m, d): mem) rvic_target_is_valid_body E0 le' (m, d) (Out_return (Some (Vint res, tuint)))).
    Proof.
      solve_code_proof Hspec rvic_target_is_valid_body; eexists; solve_proof_low.
      simpl in C1. solve_proof_low. simpl in C1. omega.
      solve_proof_low. solve_proof_low. simpl in *. solve_proof_low.
      solve_proof_low. solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
