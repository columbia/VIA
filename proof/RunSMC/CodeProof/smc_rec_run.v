Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RunComplete.Spec.
Require Import RunAux.Spec.
Require Import RunLoop.Spec.
Require Import RunLoop.Layer.
Require Import RunSMC.Code.smc_rec_run.

Require Import RunSMC.LowSpecs.smc_rec_run.

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
    _find_granule ↦ gensem find_granule_spec
      ⊕ _is_null ↦ gensem is_null_spec
      ⊕ _find_lock_unused_granule ↦ gensem find_lock_unused_granule_spec
      ⊕ _granule_get ↦ gensem granule_get_spec
      ⊕ _atomic_granule_get ↦ gensem atomic_granule_get_spec
      ⊕ _granule_unlock ↦ gensem granule_unlock_spec
      ⊕ _granule_map ↦ gensem granule_map_spec
      ⊕ _ns_granule_map ↦ gensem ns_granule_map_spec
      ⊕ _ns_buffer_read_rec_run ↦ gensem ns_buffer_read_rec_run_spec
      ⊕ _ns_buffer_unmap ↦ gensem ns_buffer_unmap_spec
      ⊕ _buffer_unmap ↦ gensem buffer_unmap_spec
      ⊕ _granule_put ↦ gensem granule_put_spec
      ⊕ _atomic_granule_put_release ↦ gensem atomic_granule_put_release_spec
      ⊕ _atomic_granule_put ↦ gensem atomic_granule_put_spec
      ⊕ _granule_lock ↦ gensem granule_lock_spec
      ⊕ _get_rec_runnable ↦ gensem get_rec_runnable_spec
      ⊕ _complete_mmio_emulation ↦ gensem complete_mmio_emulation_spec
      ⊕ _complete_hvc_exit ↦ gensem complete_hvc_exit_spec
      ⊕ _reset_last_run_info ↦ gensem reset_last_run_info_spec
      ⊕ _reset_disposed_info ↦ gensem reset_disposed_info_spec
      ⊕ _rec_run_loop ↦ gensem rec_run_loop_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_find_granule: block.
    Hypothesis h_find_granule_s : Genv.find_symbol ge _find_granule = Some b_find_granule.
    Hypothesis h_find_granule_p : Genv.find_funct_ptr ge b_find_granule
                                  = Some (External (EF_external _find_granule
                                                   (signature_of_type (Tcons tulong Tnil) Tptr cc_default))
                                         (Tcons tulong Tnil) Tptr cc_default).
    Local Opaque find_granule_spec.

    Variable b_is_null: block.
    Hypothesis h_is_null_s : Genv.find_symbol ge _is_null = Some b_is_null.
    Hypothesis h_is_null_p : Genv.find_funct_ptr ge b_is_null
                             = Some (External (EF_external _is_null
                                              (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                    (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque is_null_spec.

    Variable b_find_lock_unused_granule: block.
    Hypothesis h_find_lock_unused_granule_s : Genv.find_symbol ge _find_lock_unused_granule = Some b_find_lock_unused_granule.
    Hypothesis h_find_lock_unused_granule_p : Genv.find_funct_ptr ge b_find_lock_unused_granule
                                              = Some (External (EF_external _find_lock_unused_granule
                                                               (signature_of_type (Tcons tulong (Tcons tulong Tnil)) Tptr cc_default))
                                                     (Tcons tulong (Tcons tulong Tnil)) Tptr cc_default).
    Local Opaque find_lock_unused_granule_spec.

    Variable b_granule_get: block.
    Hypothesis h_granule_get_s : Genv.find_symbol ge _granule_get = Some b_granule_get.
    Hypothesis h_granule_get_p : Genv.find_funct_ptr ge b_granule_get
                                 = Some (External (EF_external _granule_get
                                                  (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                        (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_get_spec.

    Variable b_atomic_granule_get: block.
    Hypothesis h_atomic_granule_get_s : Genv.find_symbol ge _atomic_granule_get = Some b_atomic_granule_get.
    Hypothesis h_atomic_granule_get_p : Genv.find_funct_ptr ge b_atomic_granule_get
                                        = Some (External (EF_external _atomic_granule_get
                                                         (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                               (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque atomic_granule_get_spec.

    Variable b_granule_unlock: block.
    Hypothesis h_granule_unlock_s : Genv.find_symbol ge _granule_unlock = Some b_granule_unlock.
    Hypothesis h_granule_unlock_p : Genv.find_funct_ptr ge b_granule_unlock
                                    = Some (External (EF_external _granule_unlock
                                                     (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                           (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_unlock_spec.

    Variable b_granule_map: block.
    Hypothesis h_granule_map_s : Genv.find_symbol ge _granule_map = Some b_granule_map.
    Hypothesis h_granule_map_p : Genv.find_funct_ptr ge b_granule_map
                                 = Some (External (EF_external _granule_map
                                                  (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default))
                                        (Tcons Tptr (Tcons tuint Tnil)) Tptr cc_default).
    Local Opaque granule_map_spec.

    Variable b_ns_granule_map: block.
    Hypothesis h_ns_granule_map_s : Genv.find_symbol ge _ns_granule_map = Some b_ns_granule_map.
    Hypothesis h_ns_granule_map_p : Genv.find_funct_ptr ge b_ns_granule_map
                                    = Some (External (EF_external _ns_granule_map
                                                     (signature_of_type (Tcons tuint (Tcons Tptr Tnil)) tvoid cc_default))
                                           (Tcons tuint (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque ns_granule_map_spec.

    Variable b_ns_buffer_read_rec_run: block.
    Hypothesis h_ns_buffer_read_rec_run_s : Genv.find_symbol ge _ns_buffer_read_rec_run = Some b_ns_buffer_read_rec_run.
    Hypothesis h_ns_buffer_read_rec_run_p : Genv.find_funct_ptr ge b_ns_buffer_read_rec_run
                                            = Some (External (EF_external _ns_buffer_read_rec_run
                                                             (signature_of_type (Tcons tuint Tnil) tuint cc_default))
                                                   (Tcons tuint Tnil) tuint cc_default).
    Local Opaque ns_buffer_read_rec_run_spec.

    Variable b_ns_buffer_unmap: block.
    Hypothesis h_ns_buffer_unmap_s : Genv.find_symbol ge _ns_buffer_unmap = Some b_ns_buffer_unmap.
    Hypothesis h_ns_buffer_unmap_p : Genv.find_funct_ptr ge b_ns_buffer_unmap
                                     = Some (External (EF_external _ns_buffer_unmap
                                                      (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                            (Tcons tuint Tnil) tvoid cc_default).
    Local Opaque ns_buffer_unmap_spec.

    Variable b_buffer_unmap: block.
    Hypothesis h_buffer_unmap_s : Genv.find_symbol ge _buffer_unmap = Some b_buffer_unmap.
    Hypothesis h_buffer_unmap_p : Genv.find_funct_ptr ge b_buffer_unmap
                                  = Some (External (EF_external _buffer_unmap
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque buffer_unmap_spec.

    Variable b_granule_put: block.
    Hypothesis h_granule_put_s : Genv.find_symbol ge _granule_put = Some b_granule_put.
    Hypothesis h_granule_put_p : Genv.find_funct_ptr ge b_granule_put
                                 = Some (External (EF_external _granule_put
                                                  (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                        (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_put_spec.

    Variable b_atomic_granule_put_release: block.
    Hypothesis h_atomic_granule_put_release_s : Genv.find_symbol ge _atomic_granule_put_release = Some b_atomic_granule_put_release.
    Hypothesis h_atomic_granule_put_release_p : Genv.find_funct_ptr ge b_atomic_granule_put_release
                                                = Some (External (EF_external _atomic_granule_put_release
                                                                 (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                                       (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque atomic_granule_put_release_spec.

    Variable b_atomic_granule_put: block.
    Hypothesis h_atomic_granule_put_s : Genv.find_symbol ge _atomic_granule_put = Some b_atomic_granule_put.
    Hypothesis h_atomic_granule_put_p : Genv.find_funct_ptr ge b_atomic_granule_put
                                        = Some (External (EF_external _atomic_granule_put
                                                         (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                               (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque atomic_granule_put_spec.

    Variable b_granule_lock: block.
    Hypothesis h_granule_lock_s : Genv.find_symbol ge _granule_lock = Some b_granule_lock.
    Hypothesis h_granule_lock_p : Genv.find_funct_ptr ge b_granule_lock
                                  = Some (External (EF_external _granule_lock
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_lock_spec.

    Variable b_get_rec_runnable: block.
    Hypothesis h_get_rec_runnable_s : Genv.find_symbol ge _get_rec_runnable = Some b_get_rec_runnable.
    Hypothesis h_get_rec_runnable_p : Genv.find_funct_ptr ge b_get_rec_runnable
                                      = Some (External (EF_external _get_rec_runnable
                                                       (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                             (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque get_rec_runnable_spec.

    Variable b_complete_mmio_emulation: block.
    Hypothesis h_complete_mmio_emulation_s : Genv.find_symbol ge _complete_mmio_emulation = Some b_complete_mmio_emulation.
    Hypothesis h_complete_mmio_emulation_p : Genv.find_funct_ptr ge b_complete_mmio_emulation
                                             = Some (External (EF_external _complete_mmio_emulation
                                                              (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                                    (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque complete_mmio_emulation_spec.

    Variable b_complete_hvc_exit: block.
    Hypothesis h_complete_hvc_exit_s : Genv.find_symbol ge _complete_hvc_exit = Some b_complete_hvc_exit.
    Hypothesis h_complete_hvc_exit_p : Genv.find_funct_ptr ge b_complete_hvc_exit
                                       = Some (External (EF_external _complete_hvc_exit
                                                        (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                              (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque complete_hvc_exit_spec.

    Variable b_reset_last_run_info: block.
    Hypothesis h_reset_last_run_info_s : Genv.find_symbol ge _reset_last_run_info = Some b_reset_last_run_info.
    Hypothesis h_reset_last_run_info_p : Genv.find_funct_ptr ge b_reset_last_run_info
                                         = Some (External (EF_external _reset_last_run_info
                                                          (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                                (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque reset_last_run_info_spec.

    Variable b_reset_disposed_info: block.
    Hypothesis h_reset_disposed_info_s : Genv.find_symbol ge _reset_disposed_info = Some b_reset_disposed_info.
    Hypothesis h_reset_disposed_info_p : Genv.find_funct_ptr ge b_reset_disposed_info
                                         = Some (External (EF_external _reset_disposed_info
                                                          (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                                (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque reset_disposed_info_spec.

    Variable b_rec_run_loop: block.
    Hypothesis h_rec_run_loop_s : Genv.find_symbol ge _rec_run_loop = Some b_rec_run_loop.
    Hypothesis h_rec_run_loop_p : Genv.find_funct_ptr ge b_rec_run_loop
                                  = Some (External (EF_external _rec_run_loop
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque rec_run_loop_spec.

  End BodyProof.

End CodeProof.
