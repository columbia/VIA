Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiSMC.Layer.
Require Import PSCIAux.Code.find_lock_rec.

Require Import PSCIAux.LowSpecs.find_lock_rec.

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
    _realm_get_rec_entry ↦ gensem realm_get_rec_entry_spec
      ⊕ _is_null ↦ gensem is_null_spec
      ⊕ _granule_lock ↦ gensem granule_lock_spec
      ⊕ _granule_get ↦ gensem granule_get_spec
      ⊕ _granule_get_state ↦ gensem granule_get_state_spec
      ⊕ _ptr_eq ↦ gensem ptr_eq_spec
      ⊕ _get_g_rec_rd ↦ gensem get_g_rec_rd_spec
      ⊕ _granule_unlock ↦ gensem granule_unlock_spec
      ⊕ _null_ptr ↦ gensem null_ptr_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_realm_get_rec_entry: block.
    Hypothesis h_realm_get_rec_entry_s : Genv.find_symbol ge _realm_get_rec_entry = Some b_realm_get_rec_entry.
    Hypothesis h_realm_get_rec_entry_p : Genv.find_funct_ptr ge b_realm_get_rec_entry
                                         = Some (External (EF_external _realm_get_rec_entry
                                                          (signature_of_type (Tcons tulong (Tcons Tptr Tnil)) Tptr cc_default))
                                                (Tcons tulong (Tcons Tptr Tnil)) Tptr cc_default).
    Local Opaque realm_get_rec_entry_spec.

    Variable b_is_null: block.
    Hypothesis h_is_null_s : Genv.find_symbol ge _is_null = Some b_is_null.
    Hypothesis h_is_null_p : Genv.find_funct_ptr ge b_is_null
                             = Some (External (EF_external _is_null
                                              (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                    (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque is_null_spec.

    Variable b_granule_lock: block.
    Hypothesis h_granule_lock_s : Genv.find_symbol ge _granule_lock = Some b_granule_lock.
    Hypothesis h_granule_lock_p : Genv.find_funct_ptr ge b_granule_lock
                                  = Some (External (EF_external _granule_lock
                                                   (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                         (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_lock_spec.

    Variable b_granule_get: block.
    Hypothesis h_granule_get_s : Genv.find_symbol ge _granule_get = Some b_granule_get.
    Hypothesis h_granule_get_p : Genv.find_funct_ptr ge b_granule_get
                                 = Some (External (EF_external _granule_get
                                                  (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                        (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_get_spec.

    Variable b_granule_get_state: block.
    Hypothesis h_granule_get_state_s : Genv.find_symbol ge _granule_get_state = Some b_granule_get_state.
    Hypothesis h_granule_get_state_p : Genv.find_funct_ptr ge b_granule_get_state
                                       = Some (External (EF_external _granule_get_state
                                                        (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                              (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque granule_get_state_spec.

    Variable b_ptr_eq: block.
    Hypothesis h_ptr_eq_s : Genv.find_symbol ge _ptr_eq = Some b_ptr_eq.
    Hypothesis h_ptr_eq_p : Genv.find_funct_ptr ge b_ptr_eq
                            = Some (External (EF_external _ptr_eq
                                             (signature_of_type (Tcons Tptr (Tcons Tptr Tnil)) tuint cc_default))
                                   (Tcons Tptr (Tcons Tptr Tnil)) tuint cc_default).
    Local Opaque ptr_eq_spec.

    Variable b_get_g_rec_rd: block.
    Hypothesis h_get_g_rec_rd_s : Genv.find_symbol ge _get_g_rec_rd = Some b_get_g_rec_rd.
    Hypothesis h_get_g_rec_rd_p : Genv.find_funct_ptr ge b_get_g_rec_rd
                                  = Some (External (EF_external _get_g_rec_rd
                                                   (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                         (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_g_rec_rd_spec.

    Variable b_granule_unlock: block.
    Hypothesis h_granule_unlock_s : Genv.find_symbol ge _granule_unlock = Some b_granule_unlock.
    Hypothesis h_granule_unlock_p : Genv.find_funct_ptr ge b_granule_unlock
                                    = Some (External (EF_external _granule_unlock
                                                     (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                           (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_unlock_spec.

    Variable b_null_ptr: block.
    Hypothesis h_null_ptr_s : Genv.find_symbol ge _null_ptr = Some b_null_ptr.
    Hypothesis h_null_ptr_p : Genv.find_funct_ptr ge b_null_ptr
                              = Some (External (EF_external _null_ptr
                                               (signature_of_type Tnil Tptr cc_default))
                                     Tnil Tptr cc_default).
    Local Opaque null_ptr_spec.

    Lemma find_lock_rec_body_correct:
      forall m d d' env le g_rd_base g_rd_offset rec_list_base rec_list_offset rec_idx res_base res_offset
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTg_rd: PTree.get _g_rd le = Some (Vptr g_rd_base (Int.repr g_rd_offset)))
             (HPTrec_list: PTree.get _rec_list le = Some (Vptr rec_list_base (Int.repr rec_list_offset)))
             (HPTrec_idx: PTree.get _rec_idx le = Some (Vlong rec_idx))
             (Hspec: find_lock_rec_spec0 (g_rd_base, g_rd_offset) (rec_list_base, rec_list_offset) (VZ64 (Int64.unsigned rec_idx)) d = Some (d', (res_base, res_offset))),
           exists le', (exec_stmt ge env le ((m, d): mem) find_lock_rec_body E0 le' (m, d') (Out_return (Some (Vptr res_base (Int.repr res_offset), Tptr)))).
    Proof.
      solve_code_proof Hspec find_lock_rec_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
