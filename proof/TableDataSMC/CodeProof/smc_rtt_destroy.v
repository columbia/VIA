Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import TableAux.Spec.
Require Import AbsAccessor.Spec.
Require Import TableDataOpsIntro.Spec.
Require Import TableDataOpsRef3.Spec.
Require Import TableDataOpsRef3.Layer.
Require Import TableDataSMC.Code.smc_rtt_destroy.

Require Import TableDataSMC.LowSpecs.smc_rtt_destroy.

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
    _validate_table_commands ↦ gensem validate_table_commands_spec
      ⊕ _find_lock_granule ↦ gensem find_lock_granule_spec
      ⊕ _is_null ↦ gensem is_null_spec
      ⊕ _table_destroy ↦ gensem table_destroy_spec
      ⊕ _table_destroy3 ↦ gensem table_destroy3_spec
      ⊕ _granule_unlock ↦ gensem granule_unlock_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_validate_table_commands: block.
    Hypothesis h_validate_table_commands_s : Genv.find_symbol ge _validate_table_commands = Some b_validate_table_commands.
    Hypothesis h_validate_table_commands_p : Genv.find_funct_ptr ge b_validate_table_commands
                                             = Some (External (EF_external _validate_table_commands
                                                              (signature_of_type (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tulong Tnil))))) tuint cc_default))
                                                    (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tulong (Tcons tulong Tnil))))) tuint cc_default).
    Local Opaque validate_table_commands_spec.

    Variable b_find_lock_granule: block.
    Hypothesis h_find_lock_granule_s : Genv.find_symbol ge _find_lock_granule = Some b_find_lock_granule.
    Hypothesis h_find_lock_granule_p : Genv.find_funct_ptr ge b_find_lock_granule
                                       = Some (External (EF_external _find_lock_granule
                                                        (signature_of_type (Tcons tulong (Tcons tulong Tnil)) Tptr cc_default))
                                              (Tcons tulong (Tcons tulong Tnil)) Tptr cc_default).
    Local Opaque find_lock_granule_spec.

    Variable b_is_null: block.
    Hypothesis h_is_null_s : Genv.find_symbol ge _is_null = Some b_is_null.
    Hypothesis h_is_null_p : Genv.find_funct_ptr ge b_is_null
                             = Some (External (EF_external _is_null
                                              (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                    (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque is_null_spec.

    Variable b_table_destroy: block.
    Hypothesis h_table_destroy_s : Genv.find_symbol ge _table_destroy = Some b_table_destroy.
    Hypothesis h_table_destroy_p : Genv.find_funct_ptr ge b_table_destroy
                                   = Some (External (EF_external _table_destroy
                                                    (signature_of_type (Tcons Tptr (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tulong cc_default))
                                          (Tcons Tptr (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tulong cc_default).
    Local Opaque table_destroy_spec.

    Variable b_table_destroy3: block.
    Hypothesis h_table_destroy3_s : Genv.find_symbol ge _table_destroy3 = Some b_table_destroy3.
    Hypothesis h_table_destroy3_p : Genv.find_funct_ptr ge b_table_destroy3
                                    = Some (External (EF_external _table_destroy3
                                                     (signature_of_type (Tcons Tptr (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tulong cc_default))
                                           (Tcons Tptr (Tcons tulong (Tcons tulong (Tcons tulong Tnil)))) tulong cc_default).
    Local Opaque table_destroy3_spec.

    Variable b_granule_unlock: block.
    Hypothesis h_granule_unlock_s : Genv.find_symbol ge _granule_unlock = Some b_granule_unlock.
    Hypothesis h_granule_unlock_p : Genv.find_funct_ptr ge b_granule_unlock
                                    = Some (External (EF_external _granule_unlock
                                                     (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                           (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_unlock_spec.

    Lemma smc_rtt_destroy_body_correct:
      forall m d d' env le rtt_addr rd_addr map_addr level res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrtt_addr: PTree.get _rtt_addr le = Some (Vlong rtt_addr))
             (HPTrd_addr: PTree.get _rd_addr le = Some (Vlong rd_addr))
             (HPTmap_addr: PTree.get _map_addr le = Some (Vlong map_addr))
             (HPTlevel: PTree.get _level le = Some (Vlong level))
             (Hspec: smc_rtt_destroy_spec0 (VZ64 (Int64.unsigned rtt_addr)) (VZ64 (Int64.unsigned rd_addr)) (VZ64 (Int64.unsigned map_addr)) (VZ64 (Int64.unsigned level)) d = Some (d', VZ64 (Int64.unsigned res))),
           exists le', (exec_stmt ge env le ((m, d): mem) smc_rtt_destroy_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
    Proof.
      solve_code_proof Hspec smc_rtt_destroy_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
