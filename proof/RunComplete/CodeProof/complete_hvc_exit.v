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
Require Import RunComplete.Code.complete_hvc_exit.

Require Import RunComplete.LowSpecs.complete_hvc_exit.

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
    _get_rec_last_run_info_esr ↦ gensem get_rec_last_run_info_esr_spec
      ⊕ _set_rec_regs ↦ gensem set_rec_regs_spec
      ⊕ _get_rec_run_gprs ↦ gensem get_rec_run_gprs_spec
      ⊕ _reset_last_run_info ↦ gensem reset_last_run_info_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_get_rec_last_run_info_esr: block.
    Hypothesis h_get_rec_last_run_info_esr_s : Genv.find_symbol ge _get_rec_last_run_info_esr = Some b_get_rec_last_run_info_esr.
    Hypothesis h_get_rec_last_run_info_esr_p : Genv.find_funct_ptr ge b_get_rec_last_run_info_esr
                                               = Some (External (EF_external _get_rec_last_run_info_esr
                                                                (signature_of_type (Tcons Tptr Tnil) tulong cc_default))
                                                      (Tcons Tptr Tnil) tulong cc_default).
    Local Opaque get_rec_last_run_info_esr_spec.

    Variable b_set_rec_regs: block.
    Hypothesis h_set_rec_regs_s : Genv.find_symbol ge _set_rec_regs = Some b_set_rec_regs.
    Hypothesis h_set_rec_regs_p : Genv.find_funct_ptr ge b_set_rec_regs
                                  = Some (External (EF_external _set_rec_regs
                                                   (signature_of_type (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                         (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque set_rec_regs_spec.

    Variable b_get_rec_run_gprs: block.
    Hypothesis h_get_rec_run_gprs_s : Genv.find_symbol ge _get_rec_run_gprs = Some b_get_rec_run_gprs.
    Hypothesis h_get_rec_run_gprs_p : Genv.find_funct_ptr ge b_get_rec_run_gprs
                                      = Some (External (EF_external _get_rec_run_gprs
                                                       (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                             (Tcons tuint Tnil) tulong cc_default).
    Local Opaque get_rec_run_gprs_spec.

    Variable b_reset_last_run_info: block.
    Hypothesis h_reset_last_run_info_s : Genv.find_symbol ge _reset_last_run_info = Some b_reset_last_run_info.
    Hypothesis h_reset_last_run_info_p : Genv.find_funct_ptr ge b_reset_last_run_info
                                         = Some (External (EF_external _reset_last_run_info
                                                          (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                                (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque reset_last_run_info_spec.

  End BodyProof.

End CodeProof.
