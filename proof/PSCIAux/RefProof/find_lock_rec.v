Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import RefTactics.
Require Import AbsAccessor.Spec.
Require Import PSCIAux.Specs.find_lock_rec.
Require Import PSCIAux.LowSpecs.find_lock_rec.
Require Import PSCIAux.RefProof.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Section Refine.

  Hint Unfold
       realm_get_rec_entry_spec
       is_null_spec
       granule_lock_spec
       granule_get_spec
       granule_get_state_spec
       ptr_eq_spec
       get_g_rec_rd_spec
       granule_unlock_spec
       null_ptr_spec
    .

  Lemma find_lock_rec_spec_exists:
    forall habd habd'  labd g_rd rec_list rec_idx res
           (Hspec: find_lock_rec_spec g_rd rec_list rec_idx habd = Some (habd', res))
            (Hrel: relate_RData habd labd),
    exists labd', find_lock_rec_spec0 g_rd rec_list rec_idx labd = Some (labd', res) /\ relate_RData habd' labd'.
  Proof.
    Local Opaque ptr_eq.
    intros. destruct Hrel. destruct g_rd, rec_list.
    unfold find_lock_rec_spec, find_lock_rec_spec0 in *.
    repeat autounfold in *. simpl in *.
    hsimpl_hyp Hspec; inv Hspec; simpl_query_oracle; extract_prop_dec;
      repeat destruct_con; simpl in *; srewrite.
    - repeat (grewrite; try simpl_htarget; simpl in * ).
      eexists; split. reflexivity. constructor. reflexivity.
    - repeat (grewrite; try simpl_htarget; simpl in * ).
      ptr_ne 3%positive 1%positive. simpl. repeat (simpl_htarget; grewrite; simpl in * ).
      bool_rel; srewrite; autounfold. repeat (simpl_htarget; grewrite; simpl in * ).
      repeat (solve_bool_range; grewrite).
      eexists; split. reflexivity. constructor. reflexivity.
    - repeat (grewrite; try simpl_htarget; simpl in * ).
      ptr_ne 3%positive 1%positive; simpl. repeat (simpl_htarget; grewrite; simpl in * ).
      repeat (solve_bool_range; grewrite).
      destruct_if. ptr_ne 1%positive 3%positive. simpl.
      bool_rel; srewrite; autounfold. repeat (simpl_htarget; grewrite; simpl in * ).
      erewrite lock_held_query_oracle_lock_held; try eassumption.
      repeat (simpl_htarget; grewrite; simpl in * ).
      eexists; split. reflexivity. constructor.
      rewrite <- C14. repeat (repeat simpl_field; repeat swap_fields).
      reflexivity.
      match type of C3 with
      | repl labd (oracle labd ?l) ?st = _ =>
        instantiate (1:= labd {log: l} {share: st})
      end.
      simpl. rewrite ZMap.gss. reflexivity.
      simpl. assumption.
      ptr_ne 3%positive 3%positive. inversion e3. bool_rel; srewrite; contra. simpl.
      repeat (solve_bool_range; grewrite).
      bool_rel; srewrite.
      erewrite lock_held_query_oracle_lock_held; try eassumption. simpl_htarget.
      eexists; split. reflexivity. constructor.
      rewrite <- C14. repeat (repeat simpl_field; repeat swap_fields).
      reflexivity.
      match type of C3 with
      | repl labd (oracle labd ?l) ?st = _ =>
        instantiate (1:= labd {log: l} {share: st})
      end.
      simpl. rewrite ZMap.gss. reflexivity.
      simpl. assumption.
    - repeat (grewrite; try simpl_htarget; simpl in * ).
      ptr_ne 3%positive 1%positive. simpl.
      repeat (solve_bool_range; grewrite).
      eexists; split. reflexivity. constructor.
      bool_rel. rewrite <- Prop0, <- C13 in *. repeat (repeat simpl_field; repeat swap_fields).
      rewrite zmap_set_id. simpl_field. reflexivity.
    - repeat (grewrite; try simpl_htarget; simpl in * ).
      ptr_ne 3%positive 1%positive. simpl.
      repeat (solve_bool_range; grewrite).
      eexists; split. reflexivity. constructor.
      bool_rel; rewrite <- Prop0, <- C12 in *. repeat (repeat simpl_field; repeat swap_fields).
      rewrite zmap_set_id. simpl_field. reflexivity.
  Qed.

End Refine.

