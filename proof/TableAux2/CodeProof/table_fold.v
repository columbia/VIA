Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import TableAux.Spec.
Require Import TableAux.Layer.
Require Import TableAux2.Code.table_fold.

Require Import TableAux2.LowSpecs.table_fold.

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
      ⊕ _assert_cond ↦ gensem assert_cond_spec
      ⊕ _table_maps_block ↦ gensem table_maps_block_spec
      ⊕ _granule_refcount_dec ↦ gensem granule_refcount_dec_spec
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

    Variable b_assert_cond: block.
    Hypothesis h_assert_cond_s : Genv.find_symbol ge _assert_cond = Some b_assert_cond.
    Hypothesis h_assert_cond_p : Genv.find_funct_ptr ge b_assert_cond
                                 = Some (External (EF_external _assert_cond
                                                  (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                        (Tcons tuint Tnil) tvoid cc_default).
    Local Opaque assert_cond_spec.

    Variable b_table_maps_block: block.
    Hypothesis h_table_maps_block_s : Genv.find_symbol ge _table_maps_block = Some b_table_maps_block.
    Hypothesis h_table_maps_block_p : Genv.find_funct_ptr ge b_table_maps_block
                                      = Some (External (EF_external _table_maps_block
                                                       (signature_of_type (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tuint cc_default))
                                             (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tuint cc_default).
    Local Opaque table_maps_block_spec.

    Variable b_granule_refcount_dec: block.
    Hypothesis h_granule_refcount_dec_s : Genv.find_symbol ge _granule_refcount_dec = Some b_granule_refcount_dec.
    Hypothesis h_granule_refcount_dec_p : Genv.find_funct_ptr ge b_granule_refcount_dec
                                          = Some (External (EF_external _granule_refcount_dec
                                                           (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                                 (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque granule_refcount_dec_spec.

  End BodyProof.

End CodeProof.
