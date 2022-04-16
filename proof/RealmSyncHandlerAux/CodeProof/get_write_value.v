Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmTimerHandler.Layer.
Require Import RealmSyncHandlerAux.Code.get_write_value.

Require Import RealmSyncHandlerAux.LowSpecs.get_write_value.

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
    _esr_srt ↦ gensem esr_srt_spec
      ⊕ _access_mask ↦ gensem access_mask_spec
      ⊕ _get_rec_regs ↦ gensem get_rec_regs_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_esr_srt: block.
    Hypothesis h_esr_srt_s : Genv.find_symbol ge _esr_srt = Some b_esr_srt.
    Hypothesis h_esr_srt_p : Genv.find_funct_ptr ge b_esr_srt
                             = Some (External (EF_external _esr_srt
                                              (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                    (Tcons tulong Tnil) tuint cc_default).
    Local Opaque esr_srt_spec.

    Variable b_access_mask: block.
    Hypothesis h_access_mask_s : Genv.find_symbol ge _access_mask = Some b_access_mask.
    Hypothesis h_access_mask_p : Genv.find_funct_ptr ge b_access_mask
                                 = Some (External (EF_external _access_mask
                                                  (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                        (Tcons tulong Tnil) tulong cc_default).
    Local Opaque access_mask_spec.

    Variable b_get_rec_regs: block.
    Hypothesis h_get_rec_regs_s : Genv.find_symbol ge _get_rec_regs = Some b_get_rec_regs.
    Hypothesis h_get_rec_regs_p : Genv.find_funct_ptr ge b_get_rec_regs
                                  = Some (External (EF_external _get_rec_regs
                                                   (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tulong cc_default))
                                         (Tcons Tptr (Tcons tuint Tnil)) tulong cc_default).
    Local Opaque get_rec_regs_spec.

    Lemma get_write_value_body_correct:
      forall m d env le rec_base rec_offset esr res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTesr: PTree.get _esr le = Some (Vlong esr))
             (Hspec: get_write_value_spec0 (rec_base, rec_offset) (VZ64 (Int64.unsigned esr)) d = Some (VZ64 (Int64.unsigned res))),
           exists le', (exec_stmt ge env le ((m, d): mem) get_write_value_body E0 le' (m, d) (Out_return (Some (Vlong res, tulong)))).
    Proof.
      solve_code_proof Hspec get_write_value_body; eexists; solve_proof_low.
      unfold sem_binary_operation. unfold sem_and. unfold sem_binarith. simpl.
      solve_proof_low. rewrite H0. solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
