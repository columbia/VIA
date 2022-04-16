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
Require Import TableAux2.Code.table_create_init_absent.

Require Import TableAux2.LowSpecs.table_create_init_absent.

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
    _entry_to_phys ↦ gensem entry_to_phys_spec
      ⊕ _granule_fill_table ↦ gensem granule_fill_table_spec
      ⊕ _granule_refcount_inc ↦ gensem granule_refcount_inc_spec
      ⊕ _assert_cond ↦ gensem assert_cond_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_entry_to_phys: block.
    Hypothesis h_entry_to_phys_s : Genv.find_symbol ge _entry_to_phys = Some b_entry_to_phys.
    Hypothesis h_entry_to_phys_p : Genv.find_funct_ptr ge b_entry_to_phys
                                   = Some (External (EF_external _entry_to_phys
                                                    (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
                                          (Tcons tulong (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque entry_to_phys_spec.

    Variable b_granule_fill_table: block.
    Hypothesis h_granule_fill_table_s : Genv.find_symbol ge _granule_fill_table = Some b_granule_fill_table.
    Hypothesis h_granule_fill_table_p : Genv.find_funct_ptr ge b_granule_fill_table
                                        = Some (External (EF_external _granule_fill_table
                                                         (signature_of_type (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                               (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque granule_fill_table_spec.

    Variable b_granule_refcount_inc: block.
    Hypothesis h_granule_refcount_inc_s : Genv.find_symbol ge _granule_refcount_inc = Some b_granule_refcount_inc.
    Hypothesis h_granule_refcount_inc_p : Genv.find_funct_ptr ge b_granule_refcount_inc
                                          = Some (External (EF_external _granule_refcount_inc
                                                           (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                                 (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque granule_refcount_inc_spec.

    Variable b_assert_cond: block.
    Hypothesis h_assert_cond_s : Genv.find_symbol ge _assert_cond = Some b_assert_cond.
    Hypothesis h_assert_cond_p : Genv.find_funct_ptr ge b_assert_cond
                                 = Some (External (EF_external _assert_cond
                                                               (signature_of_type (Tcons tuint Tnil) tvoid cc_default))
                                                  (Tcons tuint Tnil) tvoid cc_default).
    Local Opaque assert_cond_spec.


    Lemma table_create_init_absent_body_correct:
      forall m d d' env le level llt_pte pte_base pte_offset g_rtt_base g_rtt_offset
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTlevel: PTree.get _level le = Some (Vlong level))
             (HPTllt_pte: PTree.get _llt_pte le = Some (Vlong llt_pte))
             (HPTpte: PTree.get _pte le = Some (Vptr pte_base (Int.repr pte_offset)))
             (HPTg_rtt: PTree.get _g_rtt le = Some (Vptr g_rtt_base (Int.repr g_rtt_offset)))
             (Hspec: table_create_init_absent_spec0 (VZ64 (Int64.unsigned level)) (VZ64 (Int64.unsigned llt_pte)) (pte_base, pte_offset) (g_rtt_base, g_rtt_offset) d = Some d'),
      exists le', (exec_stmt ge env le ((m, d): mem) table_create_init_absent_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec table_create_init_absent_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
