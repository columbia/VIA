Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiAux.Layer.
Require Import RmiAux2.Code.rec_granule_measure.

Require Import RmiAux2.LowSpecs.rec_granule_measure.

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
    _measurement_extend_rec_header ↦ gensem measurement_extend_rec_header_spec
      ⊕ _measurement_extend_rec_regs ↦ gensem measurement_extend_rec_regs_spec
      ⊕ _measurement_extend_rec_pstate ↦ gensem measurement_extend_rec_pstate_spec
      ⊕ _measurement_extend_rec_sysregs ↦ gensem measurement_extend_rec_sysregs_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_measurement_extend_rec_header: block.
    Hypothesis h_measurement_extend_rec_header_s : Genv.find_symbol ge _measurement_extend_rec_header = Some b_measurement_extend_rec_header.
    Hypothesis h_measurement_extend_rec_header_p : Genv.find_funct_ptr ge b_measurement_extend_rec_header
                                                   = Some (External (EF_external _measurement_extend_rec_header
                                                                    (signature_of_type (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default))
                                                          (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque measurement_extend_rec_header_spec.

    Variable b_measurement_extend_rec_regs: block.
    Hypothesis h_measurement_extend_rec_regs_s : Genv.find_symbol ge _measurement_extend_rec_regs = Some b_measurement_extend_rec_regs.
    Hypothesis h_measurement_extend_rec_regs_p : Genv.find_funct_ptr ge b_measurement_extend_rec_regs
                                                 = Some (External (EF_external _measurement_extend_rec_regs
                                                                  (signature_of_type (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default))
                                                        (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque measurement_extend_rec_regs_spec.

    Variable b_measurement_extend_rec_pstate: block.
    Hypothesis h_measurement_extend_rec_pstate_s : Genv.find_symbol ge _measurement_extend_rec_pstate = Some b_measurement_extend_rec_pstate.
    Hypothesis h_measurement_extend_rec_pstate_p : Genv.find_funct_ptr ge b_measurement_extend_rec_pstate
                                                   = Some (External (EF_external _measurement_extend_rec_pstate
                                                                    (signature_of_type (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default))
                                                          (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque measurement_extend_rec_pstate_spec.

    Variable b_measurement_extend_rec_sysregs: block.
    Hypothesis h_measurement_extend_rec_sysregs_s : Genv.find_symbol ge _measurement_extend_rec_sysregs = Some b_measurement_extend_rec_sysregs.
    Hypothesis h_measurement_extend_rec_sysregs_p : Genv.find_funct_ptr ge b_measurement_extend_rec_sysregs
                                                    = Some (External (EF_external _measurement_extend_rec_sysregs
                                                                     (signature_of_type (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default))
                                                           (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque measurement_extend_rec_sysregs_spec.

    Lemma rec_granule_measure_body_correct:
      forall m d d' env le rd_base rd_offset rec_base rec_offset data_size
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrd: PTree.get _rd le = Some (Vptr rd_base (Int.repr rd_offset)))
             (HPTrec: PTree.get _rec le = Some (Vptr rec_base (Int.repr rec_offset)))
             (HPTdata_size: PTree.get _data_size le = Some (Vlong data_size))
             (Hspec: rec_granule_measure_spec0 (rd_base, rd_offset) (rec_base, rec_offset) (VZ64 (Int64.unsigned data_size)) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) rec_granule_measure_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec rec_granule_measure_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
