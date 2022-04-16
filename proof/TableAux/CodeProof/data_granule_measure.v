Require Import CodeProofDeps.
Require Import Ident.
Require Import Constants.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RunSMC.Layer.
Require Import TableAux.Code.data_granule_measure.

Require Import TableAux.LowSpecs.data_granule_measure.

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
    _measurement_extend_data ↦ gensem measurement_extend_data_spec
      ⊕ _measurement_extend_data_header ↦ gensem measurement_extend_data_header_spec
  .

  Local Instance: ExternalCallsOps mem := CompatExternalCalls.compatlayer_extcall_ops L.
  Local Instance: CompilerConfigOps mem := CompatExternalCalls.compatlayer_compiler_config_ops L.

  Section BodyProof.

    Context `{Hwb: WritableBlockOps}.
    Variable (sc: stencil).
    Variables (ge: genv) (STENCIL_MATCHES: stencil_matches sc ge).

    Variable b_measurement_extend_data: block.
    Hypothesis h_measurement_extend_data_s : Genv.find_symbol ge _measurement_extend_data = Some b_measurement_extend_data.
    Hypothesis h_measurement_extend_data_p : Genv.find_funct_ptr ge b_measurement_extend_data
                                             = Some (External (EF_external _measurement_extend_data
                                                              (signature_of_type (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default))
                                                    (Tcons Tptr (Tcons Tptr Tnil)) tvoid cc_default).
    Local Opaque measurement_extend_data_spec.

    Variable b_measurement_extend_data_header: block.
    Hypothesis h_measurement_extend_data_header_s : Genv.find_symbol ge _measurement_extend_data_header = Some b_measurement_extend_data_header.
    Hypothesis h_measurement_extend_data_header_p : Genv.find_funct_ptr ge b_measurement_extend_data_header
                                                    = Some (External (EF_external _measurement_extend_data_header
                                                                     (signature_of_type (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default))
                                                           (Tcons Tptr (Tcons tulong Tnil)) tvoid cc_default).
    Local Opaque measurement_extend_data_header_spec.

    Lemma data_granule_measure_body_correct:
      forall m d d' env le rd_base rd_offset data_base data_offset offset data_size
             (Henv: env = PTree.empty _)
             (Hinv: high_level_invariant d)
             (HPTrd: PTree.get _rd le = Some (Vptr rd_base (Int.repr rd_offset)))
             (HPTdata: PTree.get _data le = Some (Vptr data_base (Int.repr data_offset)))
             (HPToffset: PTree.get _offset le = Some (Vlong offset))
             (HPTdata_size: PTree.get _data_size le = Some (Vlong data_size))
             (Hspec: data_granule_measure_spec0 (rd_base, rd_offset) (data_base, data_offset) (VZ64 (Int64.unsigned offset)) (VZ64 (Int64.unsigned data_size)) d = Some d'),
           exists le', (exec_stmt ge env le ((m, d): mem) data_granule_measure_body E0 le' (m, d') Out_normal).
    Proof.
      solve_code_proof Hspec data_granule_measure_body; eexists; solve_proof_low.
    Qed.

  End BodyProof.

End CodeProof.
