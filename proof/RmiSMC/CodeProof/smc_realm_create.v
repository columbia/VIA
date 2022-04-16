Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import RmiAux.Spec.
Require Import AbsAccessor.Spec.
Require Import RmiOps.Spec.
Require Import RmiOps.Layer.
Require Import RmiSMC.Code.smc_realm_create.

Require Import RmiSMC.LowSpecs.smc_realm_create.

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
    _get_realm_params ↦ gensem get_realm_params_spec
      ⊕ _validate_realm_params ↦ gensem validate_realm_params_spec
      ⊕ _get_realm_params_rtt_addr ↦ gensem get_realm_params_rtt_addr_spec
      ⊕ _get_realm_params_rec_list_addr ↦ gensem get_realm_params_rec_list_addr_spec
      ⊕ _find_lock_three_delegated_granules ↦ gensem find_lock_three_delegated_granules_spec
      ⊕ _realm_create_ops ↦ gensem realm_create_ops_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_get_realm_params: block.
    Hypothesis h_get_realm_params_s : Genv.find_symbol ge _get_realm_params = Some b_get_realm_params.
    Hypothesis h_get_realm_params_p : Genv.find_funct_ptr ge b_get_realm_params
                                      = Some (External (EF_external _get_realm_params
                                                       (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                             (Tcons tulong Tnil) tuint cc_default).
    Local Opaque get_realm_params_spec.

    Variable b_validate_realm_params: block.
    Hypothesis h_validate_realm_params_s : Genv.find_symbol ge _validate_realm_params = Some b_validate_realm_params.
    Hypothesis h_validate_realm_params_p : Genv.find_funct_ptr ge b_validate_realm_params
                                           = Some (External (EF_external _validate_realm_params
                                                            (signature_of_type Tnil tulong cc_default))
                                                  Tnil tulong cc_default).
    Local Opaque validate_realm_params_spec.

    Variable b_get_realm_params_rtt_addr: block.
    Hypothesis h_get_realm_params_rtt_addr_s : Genv.find_symbol ge _get_realm_params_rtt_addr = Some b_get_realm_params_rtt_addr.
    Hypothesis h_get_realm_params_rtt_addr_p : Genv.find_funct_ptr ge b_get_realm_params_rtt_addr
                                               = Some (External (EF_external _get_realm_params_rtt_addr
                                                                (signature_of_type Tnil tulong cc_default))
                                                      Tnil tulong cc_default).
    Local Opaque get_realm_params_rtt_addr_spec.

    Variable b_get_realm_params_rec_list_addr: block.
    Hypothesis h_get_realm_params_rec_list_addr_s : Genv.find_symbol ge _get_realm_params_rec_list_addr = Some b_get_realm_params_rec_list_addr.
    Hypothesis h_get_realm_params_rec_list_addr_p : Genv.find_funct_ptr ge b_get_realm_params_rec_list_addr
                                                    = Some (External (EF_external _get_realm_params_rec_list_addr
                                                                     (signature_of_type Tnil tulong cc_default))
                                                           Tnil tulong cc_default).
    Local Opaque get_realm_params_rec_list_addr_spec.

    Variable b_find_lock_three_delegated_granules: block.
    Hypothesis h_find_lock_three_delegated_granules_s : Genv.find_symbol ge _find_lock_three_delegated_granules = Some b_find_lock_three_delegated_granules.
    Hypothesis h_find_lock_three_delegated_granules_p : Genv.find_funct_ptr ge b_find_lock_three_delegated_granules
                                                        = Some (External (EF_external _find_lock_three_delegated_granules
                                                                         (signature_of_type (Tcons tulong (Tcons tulong (Tcons tulong Tnil))) tuint cc_default))
                                                               (Tcons tulong (Tcons tulong (Tcons tulong Tnil))) tuint cc_default).
    Local Opaque find_lock_three_delegated_granules_spec.

    Variable b_realm_create_ops: block.
    Hypothesis h_realm_create_ops_s : Genv.find_symbol ge _realm_create_ops = Some b_realm_create_ops.
    Hypothesis h_realm_create_ops_p : Genv.find_funct_ptr ge b_realm_create_ops
                                      = Some (External (EF_external _realm_create_ops
                                                       (signature_of_type Tnil tvoid cc_default))
                                             Tnil tvoid cc_default).
    Local Opaque realm_create_ops_spec.

    Lemma smc_realm_create_body_correct:
      forall m d d' env le rd_addr realm_params_addr res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrd_addr: PTree.get _rd_addr le = Some (Vlong rd_addr))
             (HPTrealm_params_addr: PTree.get _realm_params_addr le = Some (Vlong realm_params_addr))
             (Hspec: smc_realm_create_spec0 (VZ64 (Int64.unsigned rd_addr)) (VZ64 (Int64.unsigned realm_params_addr)) d = Some (d', VZ64 (Int64.unsigned res))),
           exists le', (exec_stmt ge env le ((m, d): mem) smc_realm_create_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
    Proof.
      solve_code_proof Hspec smc_realm_create_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
