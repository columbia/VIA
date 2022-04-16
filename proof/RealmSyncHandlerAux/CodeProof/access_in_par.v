Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RealmTimerHandler.Layer.
Require Import RealmSyncHandlerAux.Code.access_in_par.

Require Import RealmSyncHandlerAux.LowSpecs.access_in_par.

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
    _get_rec_par_end ↦ gensem get_rec_par_end_spec
      ⊕ _access_len ↦ gensem access_len_spec
      ⊕ _get_rec_par_base ↦ gensem get_rec_par_base_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_get_rec_par_end: block.
    Hypothesis h_get_rec_par_end_s : Genv.find_symbol ge _get_rec_par_end = Some b_get_rec_par_end.
    Hypothesis h_get_rec_par_end_p : Genv.find_funct_ptr ge b_get_rec_par_end
                                     = Some (External (EF_external _get_rec_par_end
                                                      (signature_of_type (Tcons Tptr Tnil) tulong cc_default))
                                            (Tcons Tptr Tnil) tulong cc_default).
    Local Opaque get_rec_par_end_spec.

    Variable b_access_len: block.
    Hypothesis h_access_len_s : Genv.find_symbol ge _access_len = Some b_access_len.
    Hypothesis h_access_len_p : Genv.find_funct_ptr ge b_access_len
                                = Some (External (EF_external _access_len
                                                 (signature_of_type (Tcons tulong Tnil) tuint cc_default))
                                       (Tcons tulong Tnil) tuint cc_default).
    Local Opaque access_len_spec.

    Variable b_get_rec_par_base: block.
    Hypothesis h_get_rec_par_base_s : Genv.find_symbol ge _get_rec_par_base = Some b_get_rec_par_base.
    Hypothesis h_get_rec_par_base_p : Genv.find_funct_ptr ge b_get_rec_par_base
                                      = Some (External (EF_external _get_rec_par_base
                                                       (signature_of_type (Tcons Tptr Tnil) tulong cc_default))
                                             (Tcons Tptr Tnil) tulong cc_default).
    Local Opaque get_rec_par_base_spec.

    Lemma access_in_par_body_correct:
      forall m d env le rec_base rec_offset address esr res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTaddress: PTree.get _address le = Some (Vlong address))
             (HPTesr: PTree.get _esr le = Some (Vlong esr))
             (Hspec: access_in_par_spec0 (rec_base, rec_offset) (VZ64 (Int64.unsigned address)) (VZ64 (Int64.unsigned esr)) d = Some (Int.unsigned res)),
           exists le', (exec_stmt ge env le ((m, d): mem) access_in_par_body E0 le' (m, d) (Out_return (Some (Vint res, tuint)))).
    Proof.
      solve_code_proof Hspec access_in_par_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
