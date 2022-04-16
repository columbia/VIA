Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RVIC2.Spec.
Require Import RVIC2.Layer.
Require Import RVIC3.Code.need_ns_notify.

Require Import RVIC3.LowSpecs.need_ns_notify.

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
    _get_rec_rec_idx ↦ gensem get_rec_rec_idx_spec
      ⊕ _get_rec_rvic_enabled ↦ gensem get_rec_rvic_enabled_spec
      ⊕ _get_rec_rvic ↦ gensem get_rec_rvic_spec
      ⊕ _rvic_is_pending ↦ gensem rvic_is_pending_spec
      ⊕ _rvic_is_masked ↦ gensem rvic_is_masked_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_get_rec_rec_idx: block.
    Hypothesis h_get_rec_rec_idx_s : Genv.find_symbol ge _get_rec_rec_idx = Some b_get_rec_rec_idx.
    Hypothesis h_get_rec_rec_idx_p : Genv.find_funct_ptr ge b_get_rec_rec_idx
                                     = Some (External (EF_external _get_rec_rec_idx
                                                      (signature_of_type (Tcons Tptr Tnil) tulong cc_default))
                                            (Tcons Tptr Tnil) tulong cc_default).
    Local Opaque get_rec_rec_idx_spec.

    Variable b_get_rec_rvic_enabled: block.
    Hypothesis h_get_rec_rvic_enabled_s : Genv.find_symbol ge _get_rec_rvic_enabled = Some b_get_rec_rvic_enabled.
    Hypothesis h_get_rec_rvic_enabled_p : Genv.find_funct_ptr ge b_get_rec_rvic_enabled
                                          = Some (External (EF_external _get_rec_rvic_enabled
                                                           (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                                 (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque get_rec_rvic_enabled_spec.

    Variable b_get_rec_rvic: block.
    Hypothesis h_get_rec_rvic_s : Genv.find_symbol ge _get_rec_rvic = Some b_get_rec_rvic.
    Hypothesis h_get_rec_rvic_p : Genv.find_funct_ptr ge b_get_rec_rvic
                                  = Some (External (EF_external _get_rec_rvic
                                                   (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                         (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rec_rvic_spec.

    Variable b_rvic_is_pending: block.
    Hypothesis h_rvic_is_pending_s : Genv.find_symbol ge _rvic_is_pending = Some b_rvic_is_pending.
    Hypothesis h_rvic_is_pending_p : Genv.find_funct_ptr ge b_rvic_is_pending
                                     = Some (External (EF_external _rvic_is_pending
                                                      (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tuint cc_default))
                                            (Tcons Tptr (Tcons tulong Tnil)) tuint cc_default).
    Local Opaque rvic_is_pending_spec.

    Variable b_rvic_is_masked: block.
    Hypothesis h_rvic_is_masked_s : Genv.find_symbol ge _rvic_is_masked = Some b_rvic_is_masked.
    Hypothesis h_rvic_is_masked_p : Genv.find_funct_ptr ge b_rvic_is_masked
                                    = Some (External (EF_external _rvic_is_masked
                                                     (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tuint cc_default))
                                           (Tcons Tptr (Tcons tulong Tnil)) tuint cc_default).
    Local Opaque rvic_is_masked_spec.

    Lemma need_ns_notify_body_correct:
      forall m d env le rec_base rec_offset target_rec_base target_rec_offset intid res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTtarget_rec: PTree.get _target_rec le = Some (Vptr target_rec_base (Int.repr target_rec_offset)))
             (HPTintid: PTree.get _intid le = Some (Vlong intid))
             (Hspec: need_ns_notify_spec0 (rec_base, rec_offset) (target_rec_base, target_rec_offset) (VZ64 (Int64.unsigned intid)) d = Some (Int.unsigned res)),
           exists le', (exec_stmt ge env le ((m, d): mem) need_ns_notify_body E0 le' (m, d) (Out_return (Some (Vint res, tuint)))).
    Proof.
      solve_code_proof Hspec need_ns_notify_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
