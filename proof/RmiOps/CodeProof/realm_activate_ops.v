Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiAux2.Layer.
Require Import RmiOps.Code.realm_activate_ops.

Require Import RmiOps.LowSpecs.realm_activate_ops.

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
    _measurement_finish ↦ gensem measurement_finish_spec
      ⊕ _set_rd_state ↦ gensem set_rd_state_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_measurement_finish: block.
    Hypothesis h_measurement_finish_s : Genv.find_symbol ge _measurement_finish = Some b_measurement_finish.
    Hypothesis h_measurement_finish_p : Genv.find_funct_ptr ge b_measurement_finish
                                        = Some (External (EF_external _measurement_finish
                                                         (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                               (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque measurement_finish_spec.

    Variable b_set_rd_state: block.
    Hypothesis h_set_rd_state_s : Genv.find_symbol ge _set_rd_state = Some b_set_rd_state.
    Hypothesis h_set_rd_state_p : Genv.find_funct_ptr ge b_set_rd_state
                                  = Some (External (EF_external _set_rd_state
                                                   (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                         (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque set_rd_state_spec.

    Lemma realm_activate_ops_body_correct:
      forall m d d' env le rd_base rd_offset
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrd: PTree.get _rd le = Some (Vptr rd_base (Int.repr rd_offset)))
             (Hspec: realm_activate_ops_spec0 (rd_base, rd_offset) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) realm_activate_ops_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec realm_activate_ops_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
