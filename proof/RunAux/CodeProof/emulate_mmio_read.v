Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmExitHandler.Layer.
Require Import RunAux.Code.emulate_mmio_read.

Require Import RunAux.LowSpecs.emulate_mmio_read.

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
    _access_mask ↦ gensem access_mask_spec
      ⊕ _get_rec_run_emulated_read_val ↦ gensem get_rec_run_emulated_read_val_spec
      ⊕ _esr_sign_extend ↦ gensem esr_sign_extend_spec
      ⊕ _access_len ↦ gensem access_len_spec
      ⊕ _shiftl ↦ gensem shiftl_spec
      ⊕ _esr_sixty_four ↦ gensem esr_sixty_four_spec
      ⊕ _set_rec_regs ↦ gensem set_rec_regs_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_access_mask: block.
    Hypothesis h_access_mask_s : Genv.find_symbol ge _access_mask = Some b_access_mask.
    Hypothesis h_access_mask_p : Genv.find_funct_ptr ge b_access_mask
                                 = Some (External (EF_external _access_mask
                                                  (signature_of_type (Tcons tulong Tnil) tulong cc_default))
                                        (Tcons tulong Tnil) tulong cc_default).
    Local Opaque access_mask_spec.

    Variable b_get_rec_run_emulated_read_val: block.
    Hypothesis h_get_rec_run_emulated_read_val_s : Genv.find_symbol ge _get_rec_run_emulated_read_val = Some b_get_rec_run_emulated_read_val.
    Hypothesis h_get_rec_run_emulated_read_val_p : Genv.find_funct_ptr ge b_get_rec_run_emulated_read_val
                                                   = Some (External (EF_external _get_rec_run_emulated_read_val
                                                                    (signature_of_type Tnil tulong cc_default))
                                                          Tnil tulong cc_default).
    Local Opaque get_rec_run_emulated_read_val_spec.

    Variable b_esr_sign_extend: block.
    Hypothesis h_esr_sign_extend_s : Genv.find_symbol ge _esr_sign_extend = Some b_esr_sign_extend.
    Hypothesis h_esr_sign_extend_p : Genv.find_funct_ptr ge b_esr_sign_extend
                                     = Some (External (EF_external _esr_sign_extend
                                                      (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                            (Tcons tulong Tnil) tuint cc_default).
    Local Opaque esr_sign_extend_spec.

    Variable b_access_len: block.
    Hypothesis h_access_len_s : Genv.find_symbol ge _access_len = Some b_access_len.
    Hypothesis h_access_len_p : Genv.find_funct_ptr ge b_access_len
                                = Some (External (EF_external _access_len
                                                 (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                       (Tcons tulong Tnil) tuint cc_default).
    Local Opaque access_len_spec.

    Variable b_shiftl: block.
    Hypothesis h_shiftl_s : Genv.find_symbol ge _shiftl = Some b_shiftl.
    Hypothesis h_shiftl_p : Genv.find_funct_ptr ge b_shiftl
                            = Some (External (EF_external _shiftl
                                             (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
                                   (Tcons tulong (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque shiftl_spec.

    Variable b_esr_sixty_four: block.
    Hypothesis h_esr_sixty_four_s : Genv.find_symbol ge _esr_sixty_four = Some b_esr_sixty_four.
    Hypothesis h_esr_sixty_four_p : Genv.find_funct_ptr ge b_esr_sixty_four
                                    = Some (External (EF_external _esr_sixty_four
                                                     (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                           (Tcons tulong Tnil) tuint cc_default).
    Local Opaque esr_sixty_four_spec.

    Variable b_set_rec_regs: block.
    Hypothesis h_set_rec_regs_s : Genv.find_symbol ge _set_rec_regs = Some b_set_rec_regs.
    Hypothesis h_set_rec_regs_p : Genv.find_funct_ptr ge b_set_rec_regs
                                  = Some (External (EF_external _set_rec_regs
                                                   (signature_of_type (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                         (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque set_rec_regs_spec.

    Lemma emulate_mmio_read_body_correct:
      forall m d d' env le esr rt rec_base rec_offset
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTesr: PTree.get _esr le = Some (Vlong esr))
             (HPTrt: PTree.get _rt le = Some (Vint rt))
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (Hspec: emulate_mmio_read_spec0 (VZ64 (Int64.unsigned esr)) (Int.unsigned rt) (rec_base, rec_offset) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) emulate_mmio_read_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec emulate_mmio_read_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
