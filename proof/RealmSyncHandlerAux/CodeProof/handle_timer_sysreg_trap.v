Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmTimerHandler.Spec.
Require Import RealmTimerHandler.Layer.
Require Import RealmSyncHandlerAux.Code.handle_timer_sysreg_trap.

Require Import RealmSyncHandlerAux.LowSpecs.handle_timer_sysreg_trap.

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
    _ESR_EL2_SYSREG_IS_WRITE ↦ gensem ESR_EL2_SYSREG_IS_WRITE_spec
      ⊕ _handle_vtimer_sysreg_write ↦ gensem handle_vtimer_sysreg_write_spec
      ⊕ _sysreg_write ↦ gensem sysreg_write_spec
      ⊕ _sysreg_read ↦ gensem sysreg_read_spec
      ⊕ _handle_vtimer_sysreg_read ↦ gensem handle_vtimer_sysreg_read_spec
      ⊕ _handle_ptimer_sysreg_write ↦ gensem handle_ptimer_sysreg_write_spec
      ⊕ _handle_ptimer_sysreg_read ↦ gensem handle_ptimer_sysreg_read_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_ESR_EL2_SYSREG_IS_WRITE: block.
    Hypothesis h_ESR_EL2_SYSREG_IS_WRITE_s : Genv.find_symbol ge _ESR_EL2_SYSREG_IS_WRITE = Some b_ESR_EL2_SYSREG_IS_WRITE.
    Hypothesis h_ESR_EL2_SYSREG_IS_WRITE_p : Genv.find_funct_ptr ge b_ESR_EL2_SYSREG_IS_WRITE
                                             = Some (External (EF_external _ESR_EL2_SYSREG_IS_WRITE
                                                              (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                                    (Tcons tulong Tnil) tuint cc_default).
    Local Opaque ESR_EL2_SYSREG_IS_WRITE_spec.

    Variable b_handle_vtimer_sysreg_write: block.
    Hypothesis h_handle_vtimer_sysreg_write_s : Genv.find_symbol ge _handle_vtimer_sysreg_write = Some b_handle_vtimer_sysreg_write.
    Hypothesis h_handle_vtimer_sysreg_write_p : Genv.find_funct_ptr ge b_handle_vtimer_sysreg_write
                                                = Some (External (EF_external _handle_vtimer_sysreg_write
                                                                 (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                                       (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque handle_vtimer_sysreg_write_spec.

    Variable b_sysreg_write: block.
    Hypothesis h_sysreg_write_s : Genv.find_symbol ge _sysreg_write = Some b_sysreg_write.
    Hypothesis h_sysreg_write_p : Genv.find_funct_ptr ge b_sysreg_write
                                  = Some (External (EF_external _sysreg_write
                                                   (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                         (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque sysreg_write_spec.

    Variable b_sysreg_read: block.
    Hypothesis h_sysreg_read_s : Genv.find_symbol ge _sysreg_read = Some b_sysreg_read.
    Hypothesis h_sysreg_read_p : Genv.find_funct_ptr ge b_sysreg_read
                                 = Some (External (EF_external _sysreg_read
                                                  (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                        (Tcons tuint Tnil) tulong cc_default).
    Local Opaque sysreg_read_spec.

    Variable b_handle_vtimer_sysreg_read: block.
    Hypothesis h_handle_vtimer_sysreg_read_s : Genv.find_symbol ge _handle_vtimer_sysreg_read = Some b_handle_vtimer_sysreg_read.
    Hypothesis h_handle_vtimer_sysreg_read_p : Genv.find_funct_ptr ge b_handle_vtimer_sysreg_read
                                               = Some (External (EF_external _handle_vtimer_sysreg_read
                                                                (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                                      (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque handle_vtimer_sysreg_read_spec.

    Variable b_handle_ptimer_sysreg_write: block.
    Hypothesis h_handle_ptimer_sysreg_write_s : Genv.find_symbol ge _handle_ptimer_sysreg_write = Some b_handle_ptimer_sysreg_write.
    Hypothesis h_handle_ptimer_sysreg_write_p : Genv.find_funct_ptr ge b_handle_ptimer_sysreg_write
                                                = Some (External (EF_external _handle_ptimer_sysreg_write
                                                                 (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                                       (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque handle_ptimer_sysreg_write_spec.

    Variable b_handle_ptimer_sysreg_read: block.
    Hypothesis h_handle_ptimer_sysreg_read_s : Genv.find_symbol ge _handle_ptimer_sysreg_read = Some b_handle_ptimer_sysreg_read.
    Hypothesis h_handle_ptimer_sysreg_read_p : Genv.find_funct_ptr ge b_handle_ptimer_sysreg_read
                                               = Some (External (EF_external _handle_ptimer_sysreg_read
                                                                (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                                      (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque handle_ptimer_sysreg_read_spec.

  End BodyProof.

End CodeProof.
