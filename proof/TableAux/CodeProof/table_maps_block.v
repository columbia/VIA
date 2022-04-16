Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RunSMC.Layer.
Require Import TableAux.Code.table_maps_block.

Require Import TableAux.LowSpecs.table_maps_block.

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
    _pgte_read ↦ gensem pgte_read_spec
      ⊕ _entry_to_phys ↦ gensem entry_to_phys_spec
      ⊕ _addr_is_level_aligned ↦ gensem addr_is_level_aligned_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_pgte_read: block.
    Hypothesis h_pgte_read_s : Genv.find_symbol ge _pgte_read = Some b_pgte_read.
    Hypothesis h_pgte_read_p : Genv.find_funct_ptr ge b_pgte_read
                               = Some (External (EF_external _pgte_read
                                                (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tulong cc_default))
                                      (Tcons Tptr (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque pgte_read_spec.

    Variable b_entry_to_phys: block.
    Hypothesis h_entry_to_phys_s : Genv.find_symbol ge _entry_to_phys = Some b_entry_to_phys.
    Hypothesis h_entry_to_phys_p : Genv.find_funct_ptr ge b_entry_to_phys
                                   = Some (External (EF_external _entry_to_phys
                                                    (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
                                          (Tcons tulong (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque entry_to_phys_spec.

    Variable b_addr_is_level_aligned: block.
    Hypothesis h_addr_is_level_aligned_s : Genv.find_symbol ge _addr_is_level_aligned = Some b_addr_is_level_aligned.
    Hypothesis h_addr_is_level_aligned_p : Genv.find_funct_ptr ge b_addr_is_level_aligned
                                           = Some (External (EF_external _addr_is_level_aligned
                                                            (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tuint cc_default))
                                                  (Tcons tulong (Tcons tulong Tnil)) tuint cc_default).
    Local Opaque addr_is_level_aligned_spec.

  End BodyProof.

End CodeProof.
