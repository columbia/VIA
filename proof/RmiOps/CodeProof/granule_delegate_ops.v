Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import BaremoreSMC.Spec.
Require Import AbsAccessor.Spec.
Require Import RmiAux2.Layer.
Require Import RmiOps.Code.granule_delegate_ops.

Require Import RmiOps.LowSpecs.granule_delegate_ops.

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
    _smc_mark_realm ↦ gensem smc_mark_realm_spec
      ⊕ _granule_set_state ↦ gensem granule_set_state_spec
      ⊕ _granule_memzero ↦ gensem granule_memzero_spec
      ⊕ _granule_unlock ↦ gensem granule_unlock_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_smc_mark_realm: block.
    Hypothesis h_smc_mark_realm_s : Genv.find_symbol ge _smc_mark_realm = Some b_smc_mark_realm.
    Hypothesis h_smc_mark_realm_p : Genv.find_funct_ptr ge b_smc_mark_realm
                                    = Some (External (EF_external _smc_mark_realm
                                                     (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                           (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque smc_mark_realm_spec.

    Variable b_granule_set_state: block.
    Hypothesis h_granule_set_state_s : Genv.find_symbol ge _granule_set_state = Some b_granule_set_state.
    Hypothesis h_granule_set_state_p : Genv.find_funct_ptr ge b_granule_set_state
                                       = Some (External (EF_external _granule_set_state
                                                        (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                              (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque granule_set_state_spec.

    Variable b_granule_memzero: block.
    Hypothesis h_granule_memzero_s : Genv.find_symbol ge _granule_memzero = Some b_granule_memzero.
    Hypothesis h_granule_memzero_p : Genv.find_funct_ptr ge b_granule_memzero
                                     = Some (External (EF_external _granule_memzero
                                                      (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                            (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque granule_memzero_spec.

    Variable b_granule_unlock: block.
    Hypothesis h_granule_unlock_s : Genv.find_symbol ge _granule_unlock = Some b_granule_unlock.
    Hypothesis h_granule_unlock_p : Genv.find_funct_ptr ge b_granule_unlock
                                    = Some (External (EF_external _granule_unlock
                                                     (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                           (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_unlock_spec.

    Lemma granule_delegate_ops_body_correct:
      forall m d d' env le g_base g_offset addr
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTg: PTree.get _g le = Some (Vptr g_base (Int.repr g_offset)))
             (HPTaddr: PTree.get _addr le = Some (Vlong addr))
             (Hspec: granule_delegate_ops_spec0 (g_base, g_offset) (VZ64 (Int64.unsigned addr)) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) granule_delegate_ops_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec granule_delegate_ops_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
