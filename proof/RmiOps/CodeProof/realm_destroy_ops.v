Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiAux2.Layer.
Require Import RmiOps.Code.realm_destroy_ops.

Require Import RmiOps.LowSpecs.realm_destroy_ops.

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
    _granule_lock ↦ gensem granule_lock_spec
      ⊕ _null_ptr ↦ gensem null_ptr_spec
      ⊕ _set_g_rtt_rd ↦ gensem set_g_rtt_rd_spec
      ⊕ _granule_memzero ↦ gensem granule_memzero_spec
      ⊕ _granule_set_state ↦ gensem granule_set_state_spec
      ⊕ _granule_unlock ↦ gensem granule_unlock_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_granule_lock: block.
    Hypothesis h_granule_lock_s : Genv.find_symbol ge _granule_lock = Some b_granule_lock.
    Hypothesis h_granule_lock_p : Genv.find_funct_ptr ge b_granule_lock
                                  = Some (External (EF_external _granule_lock
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_lock_spec.

    Variable b_null_ptr: block.
    Hypothesis h_null_ptr_s : Genv.find_symbol ge _null_ptr = Some b_null_ptr.
    Hypothesis h_null_ptr_p : Genv.find_funct_ptr ge b_null_ptr
                              = Some (External (EF_external _null_ptr
                                               (signature_of_type Tnil Tptr cc_default))
                                     Tnil Tptr cc_default).
    Local Opaque null_ptr_spec.

    Variable b_set_g_rtt_rd: block.
    Hypothesis h_set_g_rtt_rd_s : Genv.find_symbol ge _set_g_rtt_rd = Some b_set_g_rtt_rd.
    Hypothesis h_set_g_rtt_rd_p : Genv.find_funct_ptr ge b_set_g_rtt_rd
                                  = Some (External (EF_external _set_g_rtt_rd
                                                   (signature_of_type (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default))
                                         (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque set_g_rtt_rd_spec.

    Variable b_granule_memzero: block.
    Hypothesis h_granule_memzero_s : Genv.find_symbol ge _granule_memzero = Some b_granule_memzero.
    Hypothesis h_granule_memzero_p : Genv.find_funct_ptr ge b_granule_memzero
                                     = Some (External (EF_external _granule_memzero
                                                      (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                            (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque granule_memzero_spec.

    Variable b_granule_set_state: block.
    Hypothesis h_granule_set_state_s : Genv.find_symbol ge _granule_set_state = Some b_granule_set_state.
    Hypothesis h_granule_set_state_p : Genv.find_funct_ptr ge b_granule_set_state
                                       = Some (External (EF_external _granule_set_state
                                                        (signature_of_type (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default))
                                              (Tcons Tptr (Tcons tuint Tnil)) tvoid cc_default).
    Local Opaque granule_set_state_spec.

    Variable b_granule_unlock: block.
    Hypothesis h_granule_unlock_s : Genv.find_symbol ge _granule_unlock = Some b_granule_unlock.
    Hypothesis h_granule_unlock_p : Genv.find_funct_ptr ge b_granule_unlock
                                    = Some (External (EF_external _granule_unlock
                                                     (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                           (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_unlock_spec.

    Lemma realm_destroy_ops_body_correct:
      forall m d d' env le g_rtt_base g_rtt_offset g_rec_list_base g_rec_list_offset g_rd_base g_rd_offset
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTg_rtt: PTree.get _g_rtt le = Some (Vptr g_rtt_base (Int.repr g_rtt_offset)))
             (HPTg_rec_list: PTree.get _g_rec_list le = Some (Vptr g_rec_list_base (Int.repr g_rec_list_offset)))
             (HPTg_rd: PTree.get _g_rd le = Some (Vptr g_rd_base (Int.repr g_rd_offset)))
             (Hspec: realm_destroy_ops_spec0 (g_rtt_base, g_rtt_offset) (g_rec_list_base, g_rec_list_offset) (g_rd_base, g_rd_offset) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) realm_destroy_ops_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec realm_destroy_ops_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
