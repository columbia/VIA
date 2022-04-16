Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiOps.Spec.
Require Import RmiOps.Layer.
Require Import RmiSMC.Code.smc_rec_destroy.

Require Import RmiSMC.LowSpecs.smc_rec_destroy.

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
    _find_lock_unused_granule ↦ gensem find_lock_unused_granule_spec
      ⊕ _is_null ↦ gensem is_null_spec
      ⊕ _rec_destroy_ops ↦ gensem rec_destroy_ops_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_find_lock_unused_granule: block.
    Hypothesis h_find_lock_unused_granule_s : Genv.find_symbol ge _find_lock_unused_granule = Some b_find_lock_unused_granule.
    Hypothesis h_find_lock_unused_granule_p : Genv.find_funct_ptr ge b_find_lock_unused_granule
                                              = Some (External (EF_external _find_lock_unused_granule
                                                               (signature_of_type (Tcons tulong (Tcons tulong Tnil)) Tptr cc_default))
                                                     (Tcons tulong (Tcons tulong Tnil)) Tptr cc_default).
    Local Opaque find_lock_unused_granule_spec.

    Variable b_is_null: block.
    Hypothesis h_is_null_s : Genv.find_symbol ge _is_null = Some b_is_null.
    Hypothesis h_is_null_p : Genv.find_funct_ptr ge b_is_null
                             = Some (External (EF_external _is_null
                                              (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                    (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque is_null_spec.

    Variable b_rec_destroy_ops: block.
    Hypothesis h_rec_destroy_ops_s : Genv.find_symbol ge _rec_destroy_ops = Some b_rec_destroy_ops.
    Hypothesis h_rec_destroy_ops_p : Genv.find_funct_ptr ge b_rec_destroy_ops
                                     = Some (External (EF_external _rec_destroy_ops
                                                      (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                            (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque rec_destroy_ops_spec.

    Lemma smc_rec_destroy_body_correct:
      forall m d d' env le rec_addr res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec_addr: PTree.get _rec_addr le = Some (Vlong rec_addr))
             (Hspec: smc_rec_destroy_spec0 (VZ64 (Int64.unsigned rec_addr)) d = Some (d', VZ64 (Int64.unsigned res))),
           exists le', (exec_stmt ge env le ((m, d): mem) smc_rec_destroy_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
    Proof.
      solve_code_proof Hspec smc_rec_destroy_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
