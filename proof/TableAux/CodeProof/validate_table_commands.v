Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RunSMC.Layer.
Require Import TableAux.Code.validate_table_commands.

Require Import TableAux.LowSpecs.validate_table_commands.

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
    _addr_is_level_aligned ↦ gensem addr_is_level_aligned_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_addr_is_level_aligned: block.
    Hypothesis h_addr_is_level_aligned_s : Genv.find_symbol ge _addr_is_level_aligned = Some b_addr_is_level_aligned.
    Hypothesis h_addr_is_level_aligned_p : Genv.find_funct_ptr ge b_addr_is_level_aligned
                                           = Some (External (EF_external _addr_is_level_aligned
                                                            (signature_of_type (Tcons tulong (Tcons tulong Tnil)) tuint cc_default))
                                                  (Tcons tulong (Tcons tulong Tnil)) tuint cc_default).
    Local Opaque addr_is_level_aligned_spec.

    Lemma validate_table_commands_body_correct:
      forall m d env le map_addr level min_level max_level index res
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTmap_addr: PTree.get _map_addr le = Some (Vlong map_addr))
             (HPTlevel: PTree.get _level le = Some (Vlong level))
             (HPTmin_level: PTree.get _min_level le = Some (Vlong min_level))
             (HPTmax_level: PTree.get _max_level le = Some (Vlong max_level))
             (HPTindex: PTree.get _index le = Some (Vlong index))
             (Hspec: validate_table_commands_spec0 (VZ64 (Int64.unsigned map_addr)) (VZ64 (Int64.unsigned level)) (VZ64 (Int64.unsigned min_level)) (VZ64 (Int64.unsigned max_level)) (VZ64 (Int64.unsigned index)) d = Some (Int.unsigned res)),
           exists le', (exec_stmt ge env le ((m, d): mem) validate_table_commands_body E0 le' (m, d) (Out_return (Some (Vint res, tuint)))).
    Proof.
      solve_code_proof Hspec validate_table_commands_body; eexists; solve_proof_low. solve_proof_low.
      rewrite <- H0. solve_proof_low. solve_proof_low. solve_proof_low. solve_proof_low.
      rewrite <- H0. solve_proof_low. rewrite <- H0. solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
