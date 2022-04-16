Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RunSMC.Layer.
Require Import TableAux.Code.granule_fill_table.

Require Import TableAux.LowSpecs.granule_fill_table.

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
    _pgte_write ↦ gensem pgte_write_spec
      ⊕ _barrier ↦ gensem barrier_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_pgte_write: block.
    Hypothesis h_pgte_write_s : Genv.find_symbol ge _pgte_write = Some b_pgte_write.
    Hypothesis h_pgte_write_p : Genv.find_funct_ptr ge b_pgte_write
                                = Some (External (EF_external _pgte_write
                                                 (signature_of_type (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                       (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque pgte_write_spec.

    Variable b_barrier: block.
    Hypothesis h_barrier_s : Genv.find_symbol ge _barrier = Some b_barrier.
    Hypothesis h_barrier_p : Genv.find_funct_ptr ge b_barrier
                             = Some (External (EF_external _barrier
                                              (signature_of_type Tnil tvoid cc_default))
                                    Tnil tvoid cc_default).
    Local Opaque barrier_spec.

  End BodyProof.

End CodeProof.
