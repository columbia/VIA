Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmSyncHandlerAux.Layer.
Require Import RealmSyncHandler.Code.handle_instruction_abort.

Require Import RealmSyncHandler.LowSpecs.handle_instruction_abort.

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
    _sysreg_read ↦ gensem sysreg_read_spec
      ⊕ _shiftl ↦ gensem shiftl_spec
      ⊕ _is_addr_in_par_rec ↦ gensem is_addr_in_par_rec_spec
      ⊕ _is_addr_in_par ↦ gensem is_addr_in_par_spec
      ⊕ _set_rec_run_hpfar ↦ gensem set_rec_run_hpfar_spec
      ⊕ _set_rec_run_esr ↦ gensem set_rec_run_esr_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_sysreg_read: block.
    Hypothesis h_sysreg_read_s : Genv.find_symbol ge _sysreg_read = Some b_sysreg_read.
    Hypothesis h_sysreg_read_p : Genv.find_funct_ptr ge b_sysreg_read
                                 = Some (External (EF_external _sysreg_read
                                                  (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                        (Tcons tuint Tnil) tulong cc_default).
    Local Opaque sysreg_read_spec.

    Variable b_shiftl: block.
    Hypothesis h_shiftl_s : Genv.find_symbol ge _shiftl = Some b_shiftl.
    Hypothesis h_shiftl_p : Genv.find_funct_ptr ge b_shiftl
                            = Some (External (EF_external _shiftl
                                             (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
                                   (Tcons tulong (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque shiftl_spec.

    Variable b_is_addr_in_par_rec: block.
    Hypothesis h_is_addr_in_par_rec_s : Genv.find_symbol ge _is_addr_in_par_rec = Some b_is_addr_in_par_rec.
    Hypothesis h_is_addr_in_par_rec_p : Genv.find_funct_ptr ge b_is_addr_in_par_rec
                                        = Some (External (EF_external _is_addr_in_par_rec
                                                         (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tuint cc_default))
                                               (Tcons Tptr (Tcons tulong Tnil)) tuint cc_default).
    Local Opaque is_addr_in_par_rec_spec.

    Variable b_is_addr_in_par: block.
    Hypothesis h_is_addr_in_par_s : Genv.find_symbol ge _is_addr_in_par = Some b_is_addr_in_par.
    Hypothesis h_is_addr_in_par_p : Genv.find_funct_ptr ge b_is_addr_in_par
                                    = Some (External (EF_external _is_addr_in_par
                                                     (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tuint cc_default))
                                           (Tcons Tptr (Tcons tulong Tnil)) tuint cc_default).
    Local Opaque is_addr_in_par_spec.

    Variable b_set_rec_run_hpfar: block.
    Hypothesis h_set_rec_run_hpfar_s : Genv.find_symbol ge _set_rec_run_hpfar = Some b_set_rec_run_hpfar.
    Hypothesis h_set_rec_run_hpfar_p : Genv.find_funct_ptr ge b_set_rec_run_hpfar
                                       = Some (External (EF_external _set_rec_run_hpfar
                                                        (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                              (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_rec_run_hpfar_spec.

    Variable b_set_rec_run_esr: block.
    Hypothesis h_set_rec_run_esr_s : Genv.find_symbol ge _set_rec_run_esr = Some b_set_rec_run_esr.
    Hypothesis h_set_rec_run_esr_p : Genv.find_funct_ptr ge b_set_rec_run_esr
                                     = Some (External (EF_external _set_rec_run_esr
                                                      (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                            (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_rec_run_esr_spec.

    Lemma handle_instruction_abort_body_correct:
      forall m d d' env le rec_base rec_offset esr res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTesr: PTree.get _esr le = Some (Vlong esr))
             (Hspec: handle_instruction_abort_spec0 (rec_base, rec_offset) (VZ64 (Int64.unsigned esr)) d = Some (d',Int.unsigned res)),
           exists le', (exec_stmt ge env le ((m, d): mem) handle_instruction_abort_body E0 le' (m, d') (Out_return (Some (Vint res, tuint)))).
    Proof.
      solve_code_proof Hspec handle_instruction_abort_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
