Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import BaremoreSMC.Layer.
Require Import RmiAux.Code.init_common_sysregs.

Require Import RmiAux.LowSpecs.init_common_sysregs.

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
    _set_rec_common_sysregs ↦ gensem set_rec_common_sysregs_spec
      ⊕ _get_rd_g_rtt ↦ gensem get_rd_g_rtt_spec
      ⊕ _granule_addr ↦ gensem granule_addr_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_set_rec_common_sysregs: block.
    Hypothesis h_set_rec_common_sysregs_s : Genv.find_symbol ge _set_rec_common_sysregs = Some b_set_rec_common_sysregs.
    Hypothesis h_set_rec_common_sysregs_p : Genv.find_funct_ptr ge b_set_rec_common_sysregs
                                            = Some (External (EF_external _set_rec_common_sysregs
                                                             (signature_of_type (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default))
                                                   (Tcons Tptr (Tcons tuint (Tcons tulong Tnil))) tvoid cc_default).
    Local Opaque set_rec_common_sysregs_spec.

    Variable b_get_rd_g_rtt: block.
    Hypothesis h_get_rd_g_rtt_s : Genv.find_symbol ge _get_rd_g_rtt = Some b_get_rd_g_rtt.
    Hypothesis h_get_rd_g_rtt_p : Genv.find_funct_ptr ge b_get_rd_g_rtt
                                  = Some (External (EF_external _get_rd_g_rtt
                                                   (signature_of_type (Tcons Tptr Tnil) Tptr cc_default))
                                         (Tcons Tptr Tnil) Tptr cc_default).
    Local Opaque get_rd_g_rtt_spec.

    Variable b_granule_addr: block.
    Hypothesis h_granule_addr_s : Genv.find_symbol ge _granule_addr = Some b_granule_addr.
    Hypothesis h_granule_addr_p : Genv.find_funct_ptr ge b_granule_addr
                                  = Some (External (EF_external _granule_addr
                                                   (signature_of_type (Tcons Tptr Tnil) tulong cc_default))
                                         (Tcons Tptr Tnil) tulong cc_default).
    Local Opaque granule_addr_spec.

    Lemma init_common_sysregs_body_correct:
      forall m d d' env le rec_base rec_offset rd_base rd_offset
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTrd: PTree.get _rd le = Some (Vptr rd_base (Int.repr rd_offset)))
             (Hspec: init_common_sysregs_spec0 (rec_base, rec_offset) (rd_base, rd_offset) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) init_common_sysregs_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec init_common_sysregs_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
