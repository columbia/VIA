Require Import LayerDeps.
Require Import Ident.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RMMHandler.Spec.

Local Open Scope Z_scope.

Section Layer.

  Context `{real_params: RealParams}.

  Section InvDef.

    Record high_level_invariant (adt: RData) :=
      mkInvariants { }.

    Global Instance RMMHandler_ops : CompatDataOps RData :=
      {
        empty_data := empty_adt;
        high_level_invariant := high_level_invariant;
        low_level_invariant := fun (b: block) (d: RData) => True;
        kernel_mode adt := True
      }.

  End InvDef.

  Section InvInit.

    Global Instance RMMHandler_prf : CompatData RData.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvInit.

  Context `{Hstencil: Stencil}.
  Context `{Hmem: Mem.MemoryModelX}.
  Context `{Hmwd: UseMemWithData mem}.

  Section InvProof.

    Global Instance rmm_handler_inv: PreservesInvariants rmm_handler_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

    Global Instance realm_ns_step_inv: PreservesInvariants realm_ns_step_spec.
    Proof.
      constructor; intros; simpl; eauto.
      constructor.
    Qed.

  End InvProof.

  Section LayerDef.

    Definition RMMHandler_fresh : compatlayer (cdata RData) :=
      _rmm_handler ↦ gensem rmm_handler_spec
        ⊕ _realm_ns_step ↦ gensem realm_ns_step_spec
      .

    Definition RMMHandler_passthrough : compatlayer (cdata RData) :=
      ∅.

    Definition RMMHandler := RMMHandler_fresh ⊕ RMMHandler_passthrough.

  End LayerDef.

End Layer.
