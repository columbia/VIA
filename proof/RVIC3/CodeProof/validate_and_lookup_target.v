Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import RVIC2.Spec.
Require Import RVIC.Spec.
Require Import AbsAccessor.Spec.
Require Import RVIC2.Layer.
Require Import RVIC3.Code.validate_and_lookup_target.

Require Import RVIC3.LowSpecs.validate_and_lookup_target.

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
    _rvic_target_is_valid ↦ gensem rvic_target_is_valid_spec
      ⊕ _is_untrusted_intid ↦ gensem is_untrusted_intid_spec
      ⊕ _is_trusted_intid ↦ gensem is_trusted_intid_spec
      ⊕ _find_lock_map_target_rec ↦ gensem find_lock_map_target_rec_spec
      ⊕ _get_target_rec ↦ gensem get_target_rec_spec
      ⊕ _is_null ↦ gensem is_null_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_rvic_target_is_valid: block.
    Hypothesis h_rvic_target_is_valid_s : Genv.find_symbol ge _rvic_target_is_valid = Some b_rvic_target_is_valid.
    Hypothesis h_rvic_target_is_valid_p : Genv.find_funct_ptr ge b_rvic_target_is_valid
                                          = Some (External (EF_external _rvic_target_is_valid
                                                           (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                                 (Tcons tulong Tnil) tuint cc_default).
    Local Opaque rvic_target_is_valid_spec.

    Variable b_is_untrusted_intid: block.
    Hypothesis h_is_untrusted_intid_s : Genv.find_symbol ge _is_untrusted_intid = Some b_is_untrusted_intid.
    Hypothesis h_is_untrusted_intid_p : Genv.find_funct_ptr ge b_is_untrusted_intid
                                        = Some (External (EF_external _is_untrusted_intid
                                                         (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                               (Tcons tulong Tnil) tuint cc_default).
    Local Opaque is_untrusted_intid_spec.

    Variable b_is_trusted_intid: block.
    Hypothesis h_is_trusted_intid_s : Genv.find_symbol ge _is_trusted_intid = Some b_is_trusted_intid.
    Hypothesis h_is_trusted_intid_p : Genv.find_funct_ptr ge b_is_trusted_intid
                                      = Some (External (EF_external _is_trusted_intid
                                                       (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                             (Tcons tulong Tnil) tuint cc_default).
    Local Opaque is_trusted_intid_spec.

    Variable b_find_lock_map_target_rec: block.
    Hypothesis h_find_lock_map_target_rec_s : Genv.find_symbol ge _find_lock_map_target_rec = Some b_find_lock_map_target_rec.
    Hypothesis h_find_lock_map_target_rec_p : Genv.find_funct_ptr ge b_find_lock_map_target_rec
                                              = Some (External (EF_external _find_lock_map_target_rec
                                                               (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                                     (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque find_lock_map_target_rec_spec.

    Variable b_get_target_rec: block.
    Hypothesis h_get_target_rec_s : Genv.find_symbol ge _get_target_rec = Some b_get_target_rec.
    Hypothesis h_get_target_rec_p : Genv.find_funct_ptr ge b_get_target_rec
                                    = Some (External (EF_external _get_target_rec
                                                     (signature_of_type Tnil Tptr cc_default))
                                           Tnil Tptr cc_default).
    Local Opaque get_target_rec_spec.

    Variable b_is_null: block.
    Hypothesis h_is_null_s : Genv.find_symbol ge _is_null = Some b_is_null.
    Hypothesis h_is_null_p : Genv.find_funct_ptr ge b_is_null
                             = Some (External (EF_external _is_null
                                              (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                    (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque is_null_spec.

  End BodyProof.

End CodeProof.
