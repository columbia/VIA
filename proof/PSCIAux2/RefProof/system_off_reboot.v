Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import PSCIAux.Spec.
Require Import PSCIAux2.Specs.system_off_reboot.
Require Import PSCIAux2.LowSpecs.system_off_reboot.
Require Import PSCIAux2.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       get_rec_g_rec_spec
       get_rec_g_rd_spec
       get_rec_rec_idx_spec
       get_rec_g_rec_list_spec
       granule_lock_spec
       set_rec_runnable_spec
       granule_unlock_spec
       granule_map_spec
       is_null_spec
       buffer_unmap_spec
    .

  Lemma system_off_reboot_spec_exists:
    forall habd habd'  labd rec
           (Hspec: system_off_reboot_spec rec habd = Some habd')
            (Hrel: relate_RData habd labd),
    exists labd', system_off_reboot_spec0 rec labd = Some labd' /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq system_off_reboot_loop system_off_reboot_loop0 find_lock_rec_spec.
    intros. destruct rec. inv Hrel.
    unfold system_off_reboot_spec, system_off_reboot_spec0 in *.
    repeat autounfold in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; bool_rel; simpl in *; srewrite;
        repeat (simpl_htarget; grewrite; simpl in * ).
    match goal with
    | [H: system_off_reboot_loop ?n 0 ?a ?b ?c ?d = Some _
      |- context[system_off_reboot_loop0 ?n 0 ?e ?f ?g ?h]] =>
      assert(forall N i d' (HN: 0 <= Z.of_nat N <= 512) (Hspec: system_off_reboot_loop N 0 a b c d = Some (i, d')),
                exists d'', system_off_reboot_loop0 N 0 e f g h = Some (d'', i) /\ i = Z.of_nat N /\ d' = d'')
    end.
    {
      induction N.
      Local Transparent system_off_reboot_loop system_off_reboot_loop0.
      simpl. intros. inversion Hspec. eexists. split. reflexivity.
      split. reflexivity. rewrite <- C12. repeat (repeat simpl_field; repeat swap_fields). reflexivity.
      intros. rewrite Nat2Z.inj_succ in *. rewrite succ_plus_1 in *.
      simpl. simpl in Hspec. repeat autounfold in *.
      hsimpl_hyp Hspec; inversion Hspec; exploit IHN; try omega; try reflexivity;
        intros (d'' & Hd'' & Hi & Hdeq); rewrite Hd''; clear C1 IHN Hd'';
          simpl_query_oracle; extract_prop_dec; repeat destruct_con; bool_rel.
      - solve_bool_range. repeat srewrite. simpl_bool_eq.
        eexists. eauto.
      - solve_bool_range. repeat srewrite. simpl. destruct_if. bool_rel; contra.
        eexists. repeat split; reflexivity.
      - solve_bool_range. repeat srewrite. simpl. destruct_if. bool_rel; contra.
        repeat (simpl_htarget; grewrite; simpl).
        rewrite <- Prop1; repeat (repeat simpl_field; repeat swap_fields).
        eexists. repeat split; try reflexivity. rewrite <- H1. reflexivity.
    }
    exploit H; try eapply C13. simpl. omega.
    intros (d'' & Hd'' & Hi & Hdeq); rewrite Hd''. grewrite. simpl.
    eexists; split. reflexivity. constructor. reflexivity.
  Qed.

End Refine.

