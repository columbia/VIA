Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import TableDataOpsIntro.Spec.
Require Import TableDataOpsIntro.Layer.
Require Import TableDataOpsRef1.Code.data_create1.

Require Import TableDataOpsRef1.LowSpecs.data_create1.

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
    _data_create ↦ gensem data_create_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_data_create: block.
    Hypothesis h_data_create_s : Genv.find_symbol ge _data_create = Some b_data_create.
    Hypothesis h_data_create_p : Genv.find_funct_ptr ge b_data_create
                                 = Some (External (EF_external _data_create
                                                  (signature_of_type (Tcons Tptr (Tcons tulong (Tcons tulong (Tcons Tptr (Tcons Tptr Tnil))))) tulong cc_default))
                                        (Tcons Tptr (Tcons tulong (Tcons tulong (Tcons Tptr (Tcons Tptr Tnil))))) tulong cc_default).
    Local Opaque data_create_spec.

    Lemma data_create1_body_correct:
      forall m d d' env le g_rd_base g_rd_offset data_addr map_addr g_data_base g_data_offset g_src_base g_src_offset res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTg_rd: PTree.get _g_rd le = Some (Vptr g_rd_base (Int.repr g_rd_offset)))
             (HPTdata_addr: PTree.get _data_addr le = Some (Vlong data_addr))
             (HPTmap_addr: PTree.get _map_addr le = Some (Vlong map_addr))
             (HPTg_data: PTree.get _g_data le = Some (Vptr g_data_base (Int.repr g_data_offset)))
             (HPTg_src: PTree.get _g_src le = Some (Vptr g_src_base (Int.repr g_src_offset)))
             (Hspec: data_create1_spec0 (g_rd_base, g_rd_offset) (VZ64 (Int64.unsigned data_addr)) (VZ64 (Int64.unsigned map_addr)) (g_data_base, g_data_offset) (g_src_base, g_src_offset) d = Some (d', VZ64 (Int64.unsigned res))),
           exists le', (exec_stmt ge env le ((m, d): mem) data_create1_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
    Proof.
      solve_code_proof Hspec data_create1_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
