Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmSyncHandler.Spec.
Require Import RealmSyncHandler.Layer.
Require Import RealmExitHandlerAux.Code.handle_exception_sync.

Require Import RealmExitHandlerAux.LowSpecs.handle_exception_sync.

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
      ⊕ _set_rec_run_esr ↦ gensem set_rec_run_esr_spec
      ⊕ _set_rec_last_run_info_esr ↦ gensem set_rec_last_run_info_esr_spec
      ⊕ _set_rec_run_gprs ↦ gensem set_rec_run_gprs_spec
      ⊕ _get_rec_regs ↦ gensem get_rec_regs_spec
      ⊕ _sysreg_write ↦ gensem sysreg_write_spec
      ⊕ _handle_realm_rsi ↦ gensem handle_realm_rsi_spec
      ⊕ _handle_sysreg_access_trap ↦ gensem handle_sysreg_access_trap_spec
      ⊕ _handle_instruction_abort ↦ gensem handle_instruction_abort_spec
      ⊕ _set_rec_run_far ↦ gensem set_rec_run_far_spec
      ⊕ _set_rec_run_hpfar ↦ gensem set_rec_run_hpfar_spec
      ⊕ _handle_data_abort ↦ gensem handle_data_abort_spec
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

    Variable b_set_rec_run_esr: block.
    Hypothesis h_set_rec_run_esr_s : Genv.find_symbol ge _set_rec_run_esr = Some b_set_rec_run_esr.
    Hypothesis h_set_rec_run_esr_p : Genv.find_funct_ptr ge b_set_rec_run_esr
                                     = Some (External (EF_external _set_rec_run_esr
                                                      (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                            (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_rec_run_esr_spec.

    Variable b_set_rec_last_run_info_esr: block.
    Hypothesis h_set_rec_last_run_info_esr_s : Genv.find_symbol ge _set_rec_last_run_info_esr = Some b_set_rec_last_run_info_esr.
    Hypothesis h_set_rec_last_run_info_esr_p : Genv.find_funct_ptr ge b_set_rec_last_run_info_esr
                                               = Some (External (EF_external _set_rec_last_run_info_esr
                                                                (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                                      (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_rec_last_run_info_esr_spec.

    Variable b_set_rec_run_gprs: block.
    Hypothesis h_set_rec_run_gprs_s : Genv.find_symbol ge _set_rec_run_gprs = Some b_set_rec_run_gprs.
    Hypothesis h_set_rec_run_gprs_p : Genv.find_funct_ptr ge b_set_rec_run_gprs
                                      = Some (External (EF_external _set_rec_run_gprs
                                                       (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                             (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque set_rec_run_gprs_spec.

    Variable b_get_rec_regs: block.
    Hypothesis h_get_rec_regs_s : Genv.find_symbol ge _get_rec_regs = Some b_get_rec_regs.
    Hypothesis h_get_rec_regs_p : Genv.find_funct_ptr ge b_get_rec_regs
                                  = Some (External (EF_external _get_rec_regs
                                                   (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tulong cc_default))
                                         (Tcons Tptr (Tcons tuint Tnil)) tulong cc_default).
    Local Opaque get_rec_regs_spec.

    Variable b_sysreg_write: block.
    Hypothesis h_sysreg_write_s : Genv.find_symbol ge _sysreg_write = Some b_sysreg_write.
    Hypothesis h_sysreg_write_p : Genv.find_funct_ptr ge b_sysreg_write
                                  = Some (External (EF_external _sysreg_write
                                                   (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                         (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque sysreg_write_spec.

    Variable b_handle_realm_rsi: block.
    Hypothesis h_handle_realm_rsi_s : Genv.find_symbol ge _handle_realm_rsi = Some b_handle_realm_rsi.
    Hypothesis h_handle_realm_rsi_p : Genv.find_funct_ptr ge b_handle_realm_rsi
                                      = Some (External (EF_external _handle_realm_rsi
                                                       (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                             (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque handle_realm_rsi_spec.

    Variable b_handle_sysreg_access_trap: block.
    Hypothesis h_handle_sysreg_access_trap_s : Genv.find_symbol ge _handle_sysreg_access_trap = Some b_handle_sysreg_access_trap.
    Hypothesis h_handle_sysreg_access_trap_p : Genv.find_funct_ptr ge b_handle_sysreg_access_trap
                                               = Some (External (EF_external _handle_sysreg_access_trap
                                                                (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                                      (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque handle_sysreg_access_trap_spec.

    Variable b_handle_instruction_abort: block.
    Hypothesis h_handle_instruction_abort_s : Genv.find_symbol ge _handle_instruction_abort = Some b_handle_instruction_abort.
    Hypothesis h_handle_instruction_abort_p : Genv.find_funct_ptr ge b_handle_instruction_abort
                                              = Some (External (EF_external _handle_instruction_abort
                                                               (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tuint cc_default))
                                                     (Tcons Tptr (Tcons tulong Tnil)) tuint cc_default).
    Local Opaque handle_instruction_abort_spec.

    Variable b_set_rec_run_far: block.
    Hypothesis h_set_rec_run_far_s : Genv.find_symbol ge _set_rec_run_far = Some b_set_rec_run_far.
    Hypothesis h_set_rec_run_far_p : Genv.find_funct_ptr ge b_set_rec_run_far
                                     = Some (External (EF_external _set_rec_run_far
                                                      (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                            (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_rec_run_far_spec.

    Variable b_set_rec_run_hpfar: block.
    Hypothesis h_set_rec_run_hpfar_s : Genv.find_symbol ge _set_rec_run_hpfar = Some b_set_rec_run_hpfar.
    Hypothesis h_set_rec_run_hpfar_p : Genv.find_funct_ptr ge b_set_rec_run_hpfar
                                       = Some (External (EF_external _set_rec_run_hpfar
                                                        (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                              (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque set_rec_run_hpfar_spec.

    Variable b_handle_data_abort: block.
    Hypothesis h_handle_data_abort_s : Genv.find_symbol ge _handle_data_abort = Some b_handle_data_abort.
    Hypothesis h_handle_data_abort_p : Genv.find_funct_ptr ge b_handle_data_abort
                                       = Some (External (EF_external _handle_data_abort
                                                        (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                              (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque handle_data_abort_spec.

  End BodyProof.

End CodeProof.
