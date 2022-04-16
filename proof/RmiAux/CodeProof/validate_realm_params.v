Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import BaremoreSMC.Layer.
Require Import RmiAux.Code.validate_realm_params.

Require Import RmiAux.LowSpecs.validate_realm_params.

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
    _get_realm_params_par_base ↦ gensem get_realm_params_par_base_spec
      ⊕ _get_realm_params_par_size ↦ gensem get_realm_params_par_size_spec
      ⊕ _max_ipa_size ↦ gensem max_ipa_size_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_get_realm_params_par_base: block.
    Hypothesis h_get_realm_params_par_base_s : Genv.find_symbol ge _get_realm_params_par_base = Some b_get_realm_params_par_base.
    Hypothesis h_get_realm_params_par_base_p : Genv.find_funct_ptr ge b_get_realm_params_par_base
                                               = Some (External (EF_external _get_realm_params_par_base
                                                                (signature_of_type Tnil tulong cc_default))
                                                      Tnil tulong cc_default).
    Local Opaque get_realm_params_par_base_spec.

    Variable b_get_realm_params_par_size: block.
    Hypothesis h_get_realm_params_par_size_s : Genv.find_symbol ge _get_realm_params_par_size = Some b_get_realm_params_par_size.
    Hypothesis h_get_realm_params_par_size_p : Genv.find_funct_ptr ge b_get_realm_params_par_size
                                               = Some (External (EF_external _get_realm_params_par_size
                                                                (signature_of_type Tnil tulong cc_default))
                                                      Tnil tulong cc_default).
    Local Opaque get_realm_params_par_size_spec.

    Variable b_max_ipa_size: block.
    Hypothesis h_max_ipa_size_s : Genv.find_symbol ge _max_ipa_size = Some b_max_ipa_size.
    Hypothesis h_max_ipa_size_p : Genv.find_funct_ptr ge b_max_ipa_size
                                  = Some (External (EF_external _max_ipa_size
                                                   (signature_of_type Tnil tulong cc_default))
                                         Tnil tulong cc_default).
    Local Opaque max_ipa_size_spec.

    Lemma validate_realm_params_body_correct:
      forall m d env le  res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (Hspec: validate_realm_params_spec0  d = Some (VZ64 (Int64.unsigned res))),
           exists le', (exec_stmt ge env le ((m, d): mem) validate_realm_params_body E0 le' (m, d) (Out_return (Some (Vlong res, tulong)))).
    Proof.
      solve_code_proof Hspec validate_realm_params_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
