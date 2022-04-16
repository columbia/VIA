Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import BaremoreHandler.Spec.
Require Import AbsAccessor.Spec.
Require Import SMCHandler.Spec.
Require Import SMCHandler.Layer.
Require Import RMMHandler.Code.rmm_handler.

Require Import RMMHandler.LowSpecs.rmm_handler.

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
    _el3_sync_lel ↦ gensem el3_sync_lel_spec
      ⊕ _enter_rmm ↦ gensem enter_rmm_spec
      ⊕ _read_reg ↦ gensem read_reg_spec
      ⊕ _handle_ns_smc ↦ gensem handle_ns_smc_spec
      ⊕ _exit_rmm ↦ gensem exit_rmm_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_el3_sync_lel: block.
    Hypothesis h_el3_sync_lel_s : Genv.find_symbol ge _el3_sync_lel = Some b_el3_sync_lel.
    Hypothesis h_el3_sync_lel_p : Genv.find_funct_ptr ge b_el3_sync_lel
                                  = Some (External (EF_external _el3_sync_lel
                                                   (signature_of_type Tnil tvoid cc_default))
                                         Tnil tvoid cc_default).
    Local Opaque el3_sync_lel_spec.

    Variable b_enter_rmm: block.
    Hypothesis h_enter_rmm_s : Genv.find_symbol ge _enter_rmm = Some b_enter_rmm.
    Hypothesis h_enter_rmm_p : Genv.find_funct_ptr ge b_enter_rmm
                               = Some (External (EF_external _enter_rmm
                                                (signature_of_type Tnil tvoid cc_default))
                                      Tnil tvoid cc_default).
    Local Opaque enter_rmm_spec.

    Variable b_read_reg: block.
    Hypothesis h_read_reg_s : Genv.find_symbol ge _read_reg = Some b_read_reg.
    Hypothesis h_read_reg_p : Genv.find_funct_ptr ge b_read_reg
                              = Some (External (EF_external _read_reg
                                               (signature_of_type (Tcons tuint Tnil) tulong cc_default))
                                     (Tcons tuint Tnil) tulong cc_default).
    Local Opaque read_reg_spec.

    Variable b_handle_ns_smc: block.
    Hypothesis h_handle_ns_smc_s : Genv.find_symbol ge _handle_ns_smc = Some b_handle_ns_smc.
    Hypothesis h_handle_ns_smc_p : Genv.find_funct_ptr ge b_handle_ns_smc
                                   = Some (External (EF_external _handle_ns_smc
                                                    (signature_of_type (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tulong Tnil))))) tulong cc_default))
                                          (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tulong Tnil))))) tulong cc_default).
    Local Opaque handle_ns_smc_spec.

    Variable b_exit_rmm: block.
    Hypothesis h_exit_rmm_s : Genv.find_symbol ge _exit_rmm = Some b_exit_rmm.
    Hypothesis h_exit_rmm_p : Genv.find_funct_ptr ge b_exit_rmm
                              = Some (External (EF_external _exit_rmm
                                               (signature_of_type (Tcons tulong Tnil) tvoid cc_default))
                                     (Tcons tulong Tnil) tvoid cc_default).
    Local Opaque exit_rmm_spec.

    Lemma rmm_handler_body_correct:
      forall m d d' env le 
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (Hspec: rmm_handler_spec0  d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) rmm_handler_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec rmm_handler_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
