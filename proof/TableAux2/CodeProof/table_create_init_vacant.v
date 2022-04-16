Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import TableAux.Spec.
Require Import AbsAccessor.Spec.
Require Import TableAux.Layer.
Require Import TableAux2.Code.table_create_init_vacant.

Require Import TableAux2.LowSpecs.table_create_init_vacant.

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
    _granule_fill_table ↦ gensem granule_fill_table_spec
      ⊕ _granule_get ↦ gensem granule_get_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_granule_fill_table: block.
    Hypothesis h_granule_fill_table_s : Genv.find_symbol ge _granule_fill_table = Some b_granule_fill_table.
    Hypothesis h_granule_fill_table_p : Genv.find_funct_ptr ge b_granule_fill_table
                                        = Some (External (EF_external _granule_fill_table
                                                         (signature_of_type (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
                                               (Tcons Tptr (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque granule_fill_table_spec.

    Variable b_granule_get: block.
    Hypothesis h_granule_get_s : Genv.find_symbol ge _granule_get = Some b_granule_get.
    Hypothesis h_granule_get_p : Genv.find_funct_ptr ge b_granule_get
                                 = Some (External (EF_external _granule_get
                                                  (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                        (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_get_spec.

    Lemma table_create_init_vacant_body_correct:
      forall m d d' env le ipa_state pte_base pte_offset g_llt_base g_llt_offset
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTipa_state: PTree.get _ipa_state le = Some (Vlong ipa_state))
             (HPTpte: PTree.get _pte le = Some (Vptr pte_base (Int.repr pte_offset)))
             (HPTg_llt: PTree.get _g_llt le = Some (Vptr g_llt_base (Int.repr g_llt_offset)))
             (Hspec: table_create_init_vacant_spec0 (VZ64 (Int64.unsigned ipa_state)) (pte_base, pte_offset) (g_llt_base, g_llt_offset) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) table_create_init_vacant_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec table_create_init_vacant_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
