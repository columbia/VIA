Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RunAux.Spec.
Require Import RunAux.Layer.
Require Import RunComplete.Code.complete_mmio_emulation.

Require Import RunComplete.LowSpecs.complete_mmio_emulation.

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
    _get_rec_run_is_emulated_mmio ↦ gensem get_rec_run_is_emulated_mmio_spec
      ⊕ _get_rec_last_run_info_esr ↦ gensem get_rec_last_run_info_esr_spec
      ⊕ _esr_srt ↦ gensem esr_srt_spec
      ⊕ _esr_is_write ↦ gensem esr_is_write_spec
      ⊕ _emulate_mmio_read ↦ gensem emulate_mmio_read_spec
      ⊕ _get_rec_pc ↦ gensem get_rec_pc_spec
      ⊕ _set_rec_pc ↦ gensem set_rec_pc_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_get_rec_run_is_emulated_mmio: block.
    Hypothesis h_get_rec_run_is_emulated_mmio_s : Genv.find_symbol ge _get_rec_run_is_emulated_mmio = Some b_get_rec_run_is_emulated_mmio.
    Hypothesis h_get_rec_run_is_emulated_mmio_p : Genv.find_funct_ptr ge b_get_rec_run_is_emulated_mmio
                                                  = Some (External (EF_external _get_rec_run_is_emulated_mmio
                                                                   (signature_of_type Tnil tulong cc_default))
                                                         Tnil tulong cc_default).
    Local Opaque get_rec_run_is_emulated_mmio_spec.

    Variable b_get_rec_last_run_info_esr: block.
    Hypothesis h_get_rec_last_run_info_esr_s : Genv.find_symbol ge _get_rec_last_run_info_esr = Some b_get_rec_last_run_info_esr.
    Hypothesis h_get_rec_last_run_info_esr_p : Genv.find_funct_ptr ge b_get_rec_last_run_info_esr
                                               = Some (External (EF_external _get_rec_last_run_info_esr
                                                                (signature_of_type (Tcons Tptr Tnil) tulong cc_default))
                                                      (Tcons Tptr Tnil) tulong cc_default).
    Local Opaque get_rec_last_run_info_esr_spec.

    Variable b_esr_srt: block.
    Hypothesis h_esr_srt_s : Genv.find_symbol ge _esr_srt = Some b_esr_srt.
    Hypothesis h_esr_srt_p : Genv.find_funct_ptr ge b_esr_srt
                             = Some (External (EF_external _esr_srt
                                              (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                    (Tcons tulong Tnil) tuint cc_default).
    Local Opaque esr_srt_spec.

    Variable b_esr_is_write: block.
    Hypothesis h_esr_is_write_s : Genv.find_symbol ge _esr_is_write = Some b_esr_is_write.
    Hypothesis h_esr_is_write_p : Genv.find_funct_ptr ge b_esr_is_write
                                  = Some (External (EF_external _esr_is_write
                                                   (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                         (Tcons tulong Tnil) tuint cc_default).
    Local Opaque esr_is_write_spec.

    Variable b_emulate_mmio_read: block.
    Hypothesis h_emulate_mmio_read_s : Genv.find_symbol ge _emulate_mmio_read = Some b_emulate_mmio_read.
    Hypothesis h_emulate_mmio_read_p : Genv.find_funct_ptr ge b_emulate_mmio_read
                                       = Some (External (EF_external _emulate_mmio_read
                                                        (signature_of_type (Tcons tulong (Tcons tuint (Tcons Tptr Tnil))) tvoid cc_default))
                                              (Tcons tulong (Tcons tuint (Tcons Tptr Tnil))) tvoid cc_default).
    Local Opaque emulate_mmio_read_spec.

    Variable b_get_rec_pc: block.
    Hypothesis h_get_rec_pc_s : Genv.find_symbol ge _get_rec_pc = Some b_get_rec_pc.
    Hypothesis h_get_rec_pc_p : Genv.find_funct_ptr ge b_get_rec_pc
                                = Some (External (EF_external _get_rec_pc
                                                 (signature_of_type (Tcons Tptr Tnil) tulong cc_default))
                                       (Tcons Tptr Tnil) tulong cc_default).
    Local Opaque get_rec_pc_spec.

    Variable b_set_rec_pc: block.
    Hypothesis h_set_rec_pc_s : Genv.find_symbol ge _set_rec_pc = Some b_set_rec_pc.
    Hypothesis h_set_rec_pc_p : Genv.find_funct_ptr ge b_set_rec_pc
                                = Some (External (EF_external _set_rec_pc
                                                 (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                       (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_rec_pc_spec.

    Lemma complete_mmio_emulation_body_correct:
      forall m d d' env le rec_base rec_offset res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (Hspec: complete_mmio_emulation_spec0 (rec_base, rec_offset) d = Some (d',Int.unsigned res)),
           exists le', (exec_stmt ge env le ((m, d): mem) complete_mmio_emulation_body E0 le' (m, d') (Out_return (Some (Vint res, tuint)))).
    Proof.
      solve_code_proof Hspec complete_mmio_emulation_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
