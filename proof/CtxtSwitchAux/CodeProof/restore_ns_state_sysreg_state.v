Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import PendingCheck.Layer.
Require Import CtxtSwitchAux.Code.restore_ns_state_sysreg_state.

Require Import CtxtSwitchAux.LowSpecs.restore_ns_state_sysreg_state.

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
    _get_ns_state ↦ gensem get_ns_state_spec
      ⊕ _sysreg_write ↦ gensem sysreg_write_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_get_ns_state: block.
    Hypothesis h_get_ns_state_s : Genv.find_symbol ge _get_ns_state = Some b_get_ns_state.
    Hypothesis h_get_ns_state_p : Genv.find_funct_ptr ge b_get_ns_state
                                  = Some (External (EF_external _get_ns_state
                                                   (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                         (Tcons tuint Tnil) tulong cc_default).
    Local Opaque get_ns_state_spec.

    Variable b_sysreg_write: block.
    Hypothesis h_sysreg_write_s : Genv.find_symbol ge _sysreg_write = Some b_sysreg_write.
    Hypothesis h_sysreg_write_p : Genv.find_funct_ptr ge b_sysreg_write
                                  = Some (External (EF_external _sysreg_write
                                                   (signature_of_type (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default))
                                         (Tcons tuint (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque sysreg_write_spec.

  End BodyProof.

End CodeProof.
