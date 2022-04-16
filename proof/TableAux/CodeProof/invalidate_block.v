Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RunSMC.Layer.
Require Import TableAux.Code.invalidate_block.

Require Import TableAux.LowSpecs.invalidate_block.

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
    _barrier ↦ gensem barrier_spec
      ⊕ _stage2_tlbi_ipa ↦ gensem stage2_tlbi_ipa_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_barrier: block.
    Hypothesis h_barrier_s : Genv.find_symbol ge _barrier = Some b_barrier.
    Hypothesis h_barrier_p : Genv.find_funct_ptr ge b_barrier
                             = Some (External (EF_external _barrier
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).
    Local Opaque barrier_spec.

    Variable b_stage2_tlbi_ipa: block.
    Hypothesis h_stage2_tlbi_ipa_s : Genv.find_symbol ge _stage2_tlbi_ipa = Some b_stage2_tlbi_ipa.
    Hypothesis h_stage2_tlbi_ipa_p : Genv.find_funct_ptr ge b_stage2_tlbi_ipa
                                     = Some (External (EF_external _stage2_tlbi_ipa
                                                      (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default))
                                            (Tcons tulong (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque stage2_tlbi_ipa_spec.

    Lemma invalidate_block_body_correct:
      forall m d d' env le addr
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTaddr: PTree.get _addr le = Some (Vlong addr))
             (Hspec: invalidate_block_spec0 (VZ64 (Int64.unsigned addr)) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) invalidate_block_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec invalidate_block_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
