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
Require Import TableAux2.Code.table_delete.

Require Import TableAux2.LowSpecs.table_delete.

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
    _table_has_destroyed ↦ gensem table_has_destroyed_spec
      ⊕ _granule_put ↦ gensem granule_put_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_table_has_destroyed: block.
    Hypothesis h_table_has_destroyed_s : Genv.find_symbol ge _table_has_destroyed = Some b_table_has_destroyed.
    Hypothesis h_table_has_destroyed_p : Genv.find_funct_ptr ge b_table_has_destroyed
                                         = Some (External (EF_external _table_has_destroyed
                                                          (signature_of_type (Tcons Tptr Tnil) tuint cc_default))
                                                (Tcons Tptr Tnil) tuint cc_default).
    Local Opaque table_has_destroyed_spec.

    Variable b_granule_put: block.
    Hypothesis h_granule_put_s : Genv.find_symbol ge _granule_put = Some b_granule_put.
    Hypothesis h_granule_put_p : Genv.find_funct_ptr ge b_granule_put
                                 = Some (External (EF_external _granule_put
                                                  (signature_of_type (Tcons Tptr Tnil) tvoid cc_default))
                                        (Tcons Tptr Tnil) tvoid cc_default).
    Local Opaque granule_put_spec.

    Lemma table_delete_body_correct:
      forall m d d' env le table_base table_offset g_llt_base g_llt_offset res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTtable: PTree.get _table le = Some (Vptr table_base (Int.repr table_offset)))
             (HPTg_llt: PTree.get _g_llt le = Some (Vptr g_llt_base (Int.repr g_llt_offset)))
             (Hspec: table_delete_spec0 (table_base, table_offset) (g_llt_base, g_llt_offset) d = Some (d', VZ64 (Int64.unsigned res))),
           exists le', (exec_stmt ge env le ((m, d): mem) table_delete_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
    Proof.
      solve_code_proof Hspec table_delete_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
