Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PSCIAux2.Layer.
Require Import PSCI.Code.psci_features.

Require Import PSCI.LowSpecs.psci_features.

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
    _set_psci_result_x0 ↦ gensem set_psci_result_x0_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_set_psci_result_x0: block.
    Hypothesis h_set_psci_result_x0_s : Genv.find_symbol ge _set_psci_result_x0 = Some b_set_psci_result_x0.
    Hypothesis h_set_psci_result_x0_p : Genv.find_funct_ptr ge b_set_psci_result_x0
                                        = Some (External (EF_external _set_psci_result_x0
                                                         (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                               (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_psci_result_x0_spec.

    Lemma psci_features_body_correct:
      forall m d d' env le rec_base rec_offset psci_func_id
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTpsci_func_id: PTree.get _psci_func_id le = Some (Vint psci_func_id))
             (Hspec: psci_features_spec0 (rec_base, rec_offset) (Int.unsigned psci_func_id) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) psci_features_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec psci_features_body; eexists;
        repeat (repeat sstep; try big_vcgen;
                match goal with
                | [H: ?a = ?c |- context[zeq ?a ?b]] =>
                    destruct (zeq a b); try omega
                | _ => idtac
                end).
    Qed.

  End BodyProof.

End CodeProof.
