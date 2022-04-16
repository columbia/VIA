Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import TableDataOpsIntro.Spec.
Require Import TableDataOpsRef2.Spec.
Require Import TableDataOpsRef2.Layer.
Require Import TableDataOpsRef3.Code.data_destroy3.

Require Import TableDataOpsRef3.LowSpecs.data_destroy3.

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
    _data_destroy ↦ gensem data_destroy_spec
      ⊕ _data_destroy2 ↦ gensem data_destroy2_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_data_destroy: block.
    Hypothesis h_data_destroy_s : Genv.find_symbol ge _data_destroy = Some b_data_destroy.
    Hypothesis h_data_destroy_p : Genv.find_funct_ptr ge b_data_destroy
                                  = Some (External (EF_external _data_destroy
                                                   (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tulong cc_default))
                                         (Tcons Tptr (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque data_destroy_spec.

    Variable b_data_destroy2: block.
    Hypothesis h_data_destroy2_s : Genv.find_symbol ge _data_destroy2 = Some b_data_destroy2.
    Hypothesis h_data_destroy2_p : Genv.find_funct_ptr ge b_data_destroy2
                                   = Some (External (EF_external _data_destroy2
                                                    (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tulong cc_default))
                                          (Tcons Tptr (Tcons tulong Tnil)) tulong cc_default).
    Local Opaque data_destroy2_spec.

    Lemma data_destroy3_body_correct:
      forall m d d' env le g_rd_base g_rd_offset map_addr res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTg_rd: PTree.get _g_rd le = Some (Vptr g_rd_base (Int.repr g_rd_offset)))
             (HPTmap_addr: PTree.get _map_addr le = Some (Vlong map_addr))
             (Hspec: data_destroy3_spec0 (g_rd_base, g_rd_offset) (VZ64 (Int64.unsigned map_addr)) d = Some (d', VZ64 (Int64.unsigned res))),
           exists le', (exec_stmt ge env le ((m, d): mem) data_destroy3_body E0 le' (m, d') (Out_return (Some (Vlong res, tulong)))).
    Proof.
      solve_code_proof Hspec data_destroy3_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
