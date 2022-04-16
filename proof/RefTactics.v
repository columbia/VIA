Require Import RefProofDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Lemma prop_dec_to_prop:
  forall P: Prop,
    match prop_dec P with
    | left _ => P
    | right _ => ~ P
    end.
Proof.
  intros. destruct (prop_dec P); assumption.
Qed.

Ltac extract_prop_dec :=
  repeat
    match goal with
    | [H: context[prop_dec ?P] |- _] =>
      let PP := fresh "Prop" in
      assert(PP: P) by (pose proof (prop_dec_to_prop P) as TPP;
                        destruct (prop_dec P); [assumption|inversion H]);
        clear H
    end.

Lemma eq_eqb:
  forall a b, a = b -> a =? b = true.
Proof.
  intros; bool_rel; assumption.
Qed.

Lemma neq_neqb:
  forall a b, a <> b -> a =? b = false.
Proof.
  intros; bool_rel; assumption.
Qed.

Lemma le_leb:
  forall a b, a <= b -> a <=? b = true.
Proof.
  intros; bool_rel; assumption.
Qed.

Lemma le_ngtb:
  forall a b, a <= b -> a >? b = false.
Proof.
  intros; bool_rel; assumption.
Qed.

Lemma lt_ltb:
  forall a b, a < b -> a <? b = true.
Proof.
  intros; bool_rel; assumption.
Qed.

Lemma lt_ngeb:
  forall a b, a < b -> a >=? b = false.
Proof.
  intros; bool_rel; assumption.
Qed.

Lemma ge_geb:
  forall a b, a >= b -> a >=? b = true.
Proof.
  intros; bool_rel. omega.
Qed.

Lemma ge_nltb:
  forall a b, a >= b -> a <? b = false.
Proof.
  intros; bool_rel. omega.
Qed.

Lemma gt_gtb:
  forall a b, a > b -> a >? b = true.
Proof.
  intros; bool_rel. omega.
Qed.

Lemma gt_nleb:
  forall a b, a > b -> a <=? b = false.
Proof.
  intros; bool_rel. omega.
Qed.

Hypothesis a_plus_16:
forall n b, 0 <= n < 16 -> b >= 0 -> Z.land (n + (Z.shiftl b 4)) 15 = n.

Hypothesis a_plus_16':
forall n b, 0 <= n < 16 -> b >= 0 -> Z.shiftr (n + (Z.shiftl b 4)) 4 = b.

Ltac simpl_htarget :=
  repeat
   match goal with
   | H:?a = ?b |- context [?a =? ?b] => let tmp := fresh "tmpif" in
                                        assert ((a =? b) = true) as tmp by (apply eq_eqb; apply H); rewrite tmp; clear tmp
   | H:?a <> ?b |- context [?a =? ?b] => let tmp := fresh "tmpif" in
                                         assert ((a =? b) = false) as tmp by (apply zeq_false_ne; apply H); rewrite tmp; clear tmp
   | H:?b <> ?a |- context [?a =? ?b] => let tmp := fresh "tmpif" in
                                         let T := fresh "T" in
                                         assert ((a =? b) = false) as tmp by (apply zeq_false_ne; red; intro T; rewrite T in *; contra); rewrite tmp; clear tmp
   | H:?a <= ?b |- context [?a <=? ?b] => let tmp := fresh "tmpif" in
                                          assert ((a <=? b) = true) as tmp by (apply le_leb; apply H); rewrite tmp; clear tmp
   | H:?a <= ?b |- context [?b >=? ?a] => let tmp := fresh "tmpif" in
                                          assert ((b >=? a) = true) as tmp by (apply Z.geb_le; apply H); rewrite tmp; clear tmp
   | H:?a < ?b |- context [?a <? ?b] => let tmp := fresh "tmpif" in
                                        assert ((a <? b) = true) as tmp by (apply Z.ltb_lt; apply H); rewrite tmp; clear tmp
   | H:?a < ?b |- context [?b >? ?a] => let tmp := fresh "tmpif" in
                                        assert ((b >? a) = true) as tmp by (apply Z.gtb_lt; apply H); rewrite tmp; clear tmp
   | H:?P |- context [prop_dec ?P] => let tmp := fresh "He" in
                                      destruct (prop_dec P) as [tmp| tmp]; [ simpl; clear tmp | apply tmp in H; inversion H ]
   | |- context [ptr_eq ?p ?p] => let He := fresh "He" in
                                  destruct (ptr_eq p p) as [He| He]; [ clear He | contra ]
   | |- context [?x =? ?x] => simpl_bool_eq
   | |- context [prop_dec (?a = ?a)] => destruct (prop_dec (a = a)); [ simpl | contra ]
   | |- context [peq ?a ?a] => destruct (peq a a); [ simpl | contra ]
   | |- context [(?map # ?key == ?val) @ ?key] => rewrite ZMap.gss
   | H:?key1 <> ?key2 |- context [(?map # ?key2 == ?val) @ ?key1] => rewrite (ZMap.gso _ _ H)
   | H:?key2 <> ?key1
     |- context [(?map # ?key2 == ?val) @ ?key1] => let T := fresh "tmp" in
                                                  let X := fresh "tmp" in
                                                  assert (key1 <> key2) as T by (red; intro X; rewrite X in *; contra); rewrite (ZMap.gso _ _ T); clear T
   | |- context [(?map # ?key == ?val) # ?key == ?val2] => rewrite ZMap.set2
   | |- context [?map # ?key == (?map @ ?key)] => rewrite zmap_set_id
   | H:?m @ ?a = ?v |- context [?m # ?a == ?v] => rewrite <- H; rewrite zmap_set_id
   | H:negb ?x = true |- _ => apply negb_true_iff in H
   | H:negb ?x = false |- _ => apply negb_false_iff in H
   | H:context [?a + 1 - 1] |- _ => replace (a + 1 - 1) with a in H by omega
   | H:context [?a - 1 + 1] |- _ => replace (a - 1 + 1) with a in H by omega
   | |- context [?a + 1 - 1] => replace (a + 1 - 1) with a by omega
   | |- context [?a - 1 + 1] => replace (a - 1 + 1) with a by omega
   | H:?a = ?b -> False |- _ => let T := fresh "T" in
                                assert (a <> b) as T by (red; apply H); clear H; rename T into H
   end.

Ltac solve_ptr_eq :=
  match goal with
  | [|- context[ptr_eq ?a ?b]] =>
    let pt := fresh "Hptr" in
    destruct (ptr_eq a b) eqn:pt; try solve[inversion pt]
  end.

Ltac solve_peq :=
  match goal with
  | |- context [peq ?a ?b] =>
    let pt := fresh "Hptr" in
    destruct (peq a b) eqn:pt; try (solve [ inversion pt ])
  end.

Hypothesis lock_held_query_oracle_ns:
  forall d gidx ginfo' st'
    (Hns: gtype ((gs (share d)) @ gidx) = GRANULE_STATE_NS)
    (Hlock: glock ((gs (share d)) @ gidx) = Some CPU_ID)
    (Horacle: (repl d (oracle d (log d)) (share d)) = Some st'),
    repl d (oracle d (log d)) ((share d) {gs: (gs (share d)) # gidx == (((gs (share d)) @ gidx) {ginfo: ginfo'})}) =
    Some (st' {gs: (gs st') # gidx == (((gs st') @ gidx) {ginfo: ginfo'})}).

Hypothesis lock_held_query_oracle_lock_held:
  forall d gidx st'
    (Hlock: glock ((gs (share d)) @ gidx) = Some CPU_ID)
    (Horacle: (repl d (oracle d (log d)) (share d)) = Some st'),
    glock ((gs st') @ gidx) = Some CPU_ID.

Ltac destruct_log H :=
  let st := fresh "st" in
  let P := fresh "Lr" in
  let P2 := fresh "Lr" in
  let E := fresh "Er" in
  match type of H with
  | replay _ (?e :: ?l) _ _ = Some (_, _) =>
    pose proof (replay_some_ind _ _ _ _ _ _ _ H) as P; destruct P as (st & ? & P & E); destruct_log P
  | replay _ ((oracle _ _) ++ ?l2) _ _ = Some (_, _) =>
    pose proof (replay_some_ind2 _ _ _ _ _ _ _ H) as P; destruct P as (st & ? & P & P2); destruct_log P; destruct_log P2
  | _ => idtac
  end.

Ltac clear_log :=
  repeat
    match goal with
    | [H1: replay ?lv ?l ?em ?r = Some (_, _), H2: replay ?lv ?l ?em ?r = Some (_, _) |- _] =>
      rewrite H1 in H2; inversion H2; clear H2
    | [H1: ereplay ?lv ?st ?e ?r = Some (_, _), H2: ereplay ?lv ?st ?e ?r = Some (_, _) |- _] =>
      rewrite H1 in H2; inversion H2; clear H2
    end.

Ltac remember_evt :=
  repeat
    let evt := fresh "e" in
    let eqevt := fresh "Eq" in
    match goal with
    | [H: context[(EVT ?c ?e) :: _] |- _ ] =>
      remember (EVT c e) as evt eqn:eqevt; symmetry in eqevt
    end.

Ltac remember_gidx :=
  repeat
    match goal with
    | [H: context[ACQ (?a ?b)] |- _ ] =>
      let name := fresh "gidx" in
      let Hname := fresh "Hgidx" in
      remember (a b) as name eqn:Hname; symmetry in Hname
    | [H: context[REL (?a ?b)] |- _ ] =>
      let name := fresh "gidx" in
      let Hname := fresh "Hgidx" in
      remember (a b) as name eqn:Hname; symmetry in Hname
    end.

Hypothesis ACQ_RightMover:
  forall lvl gidx cid,
      IsRightMover lvl (EVT cid (ACQ gidx)).

Hypothesis walk_right :
   forall lvl cpu root_gidx map_addr level,
      lvl >= 2 -> level < lvl ->
      IsRightMover lvl (EVT cpu (RTT_WALK root_gidx map_addr level)).

Hypothesis zero_not_table:
  __entry_is_table 0 = false.

Lemma ACQ_OracleElim:
  forall d lvl l c g,
    ValidOracle lvl (oracle d) -> oracle d (EVT c (ACQ g) :: oracle d l ++ l) = nil.
Proof.
  intros. destruct H.
  eapply Hright_log_nil. eapply RightLogMover.
  apply ACQ_RightMover. apply RightLogOracle.
Qed.

Ltac simpl_ACQ :=
  match goal with
  | [|- context[oracle ?d (EVT ?c (ACQ ?g) :: oracle ?d ?l ++ ?l)]] =>
    erewrite ACQ_OracleElim; try eassumption
  end.

Ltac extract_oracle_log :=
  repeat
    let Lg := fresh "Lg" in
    let eqLg := fresh "Leq" in
    match goal with
    | [H: context[oracle _ _ ++ ?e :: ?l] |- _] =>
      remember (e::l) as Lg eqn:eqLg; symmetry in eqLg
    | [ |- context[oracle _ _ ++ ?e :: ?l] ] =>
      remember (e::l) as Lg eqn:eqLg; symmetry in eqLg
    | [H: context[oracle _ _ ++ ?e ++ ?l] |- _] =>
      remember (e ++ l) as Lg eqn:eqLg; symmetry in eqLg
    | [ |- context[oracle _ _ ++ ?e ++ ?l] ] =>
      remember (e ++ l) as Lg eqn:eqLg; symmetry in eqLg
    end.

Ltac simpl_same_update :=
  repeat
    match goal with
    | [|-context[?f ?a (?r ?a)]] =>
      replace (f a (r a)) with a by (destruct a; reflexivity)
    end.

Ltac simpl_erewrite :=
  match goal with
  | [H: EVT ?c ?f = ?e |- context[ereplay _ _ ?e]] =>
    rewrite <- H; simpl (ereplay _ _ (EVT c f))
  end.

Ltac finish_oracle_rel :=
  let O := fresh "Orc" in
  intros O; srewrite' O; hsimpl_hyp O; inv O.

Ltac remember_gevt :=
  repeat
    let evt := fresh "e'" in
    let eqevt := fresh "Eq'" in
    match goal with
    | [ |- context[(EVT ?c ?e) :: _] ] =>
      remember (EVT c e) as evt eqn:eqevt; symmetry in eqevt
    end.

Ltac prep_log H :=
  destruct_log H; clear_log; subst; unfold ereplay in *; remember_evt.

Create HintDb Replay.

Hint Unfold
     repl Repl repl_acq repl_rel
     repl_recro repl_recl
     repl_acq_gpt repl_rel_gpt: Replay.

Ltac simpl_hcases :=
  repeat
    match goal with
    | [ |- context [peq ?x ?y]] =>
      let H := fresh "Cpeq" in destruct (peq x y) as [H|H]; try solve [inversion H]; contra
    | [|-context[ptr_eq ?a ?b]] =>
      let H := fresh "Cptreq" in destruct (ptr_eq a b) as [H|H]; try solve [inversion H]; contra
    | [|-context[?x =? ?x]] => simpl_bool_eq
    | [|-context[ZMap.get ?key (ZMap.set ?key ?val ?map)]] => rewrite ZMap.gss
    | [|-context[ZMap.set ?key ?val2 (ZMap.set ?key ?val ?map)]] => rewrite ZMap.set2
    | [|-context[ZMap.set ?key (ZMap.get ?key ?map) ?map]] => rewrite zmap_set_id
    | [H: context[ZMap.get ?key (ZMap.set ?key ?val ?map)] |- _] => rewrite ZMap.gss in H
    | [H: context[ZMap.set ?key ?val2 (ZMap.set ?key ?val ?map)] |- _] => rewrite ZMap.set2 in H
    | [H: context[ZMap.set ?key (ZMap.get ?key ?map) ?map] |- _] => rewrite zmap_set_id in H
    | H:EVT ?c ?f = ?e |- context [ereplay _ _ ?e] => rewrite <- H; simpl (ereplay _ _ (EVT c f))
    | |- context [?f (?f ?a ?b) ?bb] =>
      replace (f (f a b) bb) with (f a bb) by reflexivity; simpl
    | |- context [?f ?a (?r ?a)] => replace (f a (r a)) with a by (destruct a; reflexivity)
    | [H: context [?f (?f ?a ?b) ?bb] |- _] =>
      replace (f (f a b) bb) with (f a bb) in H by reflexivity; simpl
    | [H: context [?f ?a (?r ?a)] |- _] => replace (f a (r a)) with a in H by (destruct a; reflexivity)
    end; simpl.

Ltac simpl_hgoals :=
  repeat (grewrite; autounfold; autounfold with Replay; simpl; simpl_hcases).

Ltac construct_relate :=
  constructor; simpl; autounfold with Replay; simpl; grewrite; try assumption; try reflexivity; simpl_hgoals.

Hypothesis or_le_64:
  forall a b (Ha: 0 <= a) (Ha': a <= 18446744073709551615) (Hb: 0 <= b) (Hb': b <= 18446744073709551615),
    Z.lor a b <= 18446744073709551615.

Ltac simpl_query_oracle :=
  repeat match goal with
          | H:query_oracle ?d = Some ?d' |- _ => try unfold query_oracle; unfold query_oracle in H; autounfold in H; repeat simpl_hyp H; inv H; simpl in *
          end.

Ltac ptr_ne x y :=
  match goal with
  | [|- context[ptr_eq (x, ?a) (y, ?b)]] =>
    let t := fresh "T" in
    destruct (ptr_eq (x, a) (y, b)) eqn:t; [inv t|clear t]
  end.

Ltac simpl_loop_add :=
  match goal with
  | |- context[0 + ?x] => rewrite Z.add_0_l
  | |- context[1 + 1] => replace (1 + 1) with 2 by reflexivity
  | |- context[2 + 1] => replace (2 + 1) with 3 by reflexivity
  | |- context[3 + 1] => replace (3 + 1) with 4 by reflexivity
  | |- context[4 + 1] => replace (4 + 1) with 5 by reflexivity
  | |- context[5 + 1] => replace (5 + 1) with 6 by reflexivity
  | |- context[6 + 1] => replace (6 + 1) with 7 by reflexivity
  | |- context[7 + 1] => replace (7 + 1) with 8 by reflexivity
  | |- context[8 + 1] => replace (8 + 1) with 9 by reflexivity
  | _ => idtac
  end.

Ltac elim_negb :=
  repeat
    match goal with
    | [H: negb ?x = true |- _] => apply negb_true_iff in H
    | [H: negb ?x = false |- _] => apply negb_false_iff in H
    end.

Ltac solve_bool_range :=
    extract_if; [bool_rel_all; apply andb_true_iff; split; bool_rel; somega|].

Ltac simpl_get_set_reg_other n m :=
  match goal with
  | [ |- context[get_reg n (set_reg m ?val ?regs)]] =>
    replace (get_reg n (set_reg m val regs)) with (get_reg n regs) by reflexivity
  end.

Ltac simpl_get_set_reg_same m :=
  match goal with
  | [ |- context[get_reg m (set_reg m ?val ?regs)]] =>
    replace (get_reg m (set_reg m val regs)) with val by reflexivity
  end.

Ltac extract_match_rec T :=
  match T with
  | context[match ?f with Some _ => _ | None => None end] => extract_match_rec f
  | _ =>
      let F := fresh "F" in
      let eqF := fresh "EqF" in
      let eqF' := fresh "EqF'" in
      remember T as F eqn:eqF; symmetry in eqF; pose proof eqF as eqF'; generalize dependent eqF'
  end.

Ltac extract_match :=
  match goal with
  | [|- context[match ?f with Some _ => _ | None => None end] ] => extract_match_rec f
  end.

Ltac collect_res :=
  let X := fresh "X" in
  intro X; rewrite <- X in *; clear X.

Ltac simpl_hgoals' := repeat (simpl_hcases; autounfold; try unfold repl; grewrite).

Lemma prop_dec_rely:
  forall P: Prop, P -> (proj_sumbool (prop_dec P) = true).
Proof.
  intros. destruct (prop_dec P). reflexivity. auto.
Qed.

Ltac simpl_hcond H :=
  repeat (match type of H with
          | context[ZMap.get ?key (ZMap.set ?key ?val ?map)] => rewrite ZMap.gss in H
          | context[ZMap.set ?key ?val2 (ZMap.set ?key ?val ?map)] => rewrite ZMap.set2 in H
          | context[ZMap.set ?key (ZMap.get ?key ?map) ?map] => rewrite zmap_set_id in H
          | context [?f (?f ?a ?b) ?bb] =>
            replace (f (f a b) bb) with (f a bb) in H by reflexivity; simpl
          | context [?f ?a (?r ?a)] => replace (f a (r a)) with a in H by (destruct a; reflexivity)
          | negb ?x = true  => apply negb_true_iff in H
          | negb ?x = false => apply negb_false_iff in H
          | _ => idtac
          end; simpl in H).

Ltac simpl_all_cond :=
  (repeat
      let T := fresh "tmp" in
      match goal with
      | [H: context[_ = _] |- _] =>
        simpl_hcond H;
        match type of H with
        | ?p => assert(T: True -> p) by (intros; apply H); clear H; rename T into H
        end
      end);
  (repeat
      let E := fresh "tmp" in
      match goal with
      | [H: True -> ?p |- _] => assert(E: p) by (apply H; constructor); clear H; rename E into H
      end).

Ltac simpl_hgoals0' :=
  repeat (autounfold; try unfold repl; try unfold Repl; simpl_htarget; repeat grewrite).

Ltac simpl_hgoals0 :=
  repeat (autounfold; autounfold with Replay; simpl_htarget; repeat grewrite).

Ltac clear_rewrite H :=
  rewrite H; clear H.

Ltac destruct_zmap' H :=
  let Heq := fresh "Heq" in
  match type of H with
  | context [(?m # ?b == ?c) @ ?a] => destruct (a =? b) eqn:Heq; bool_rel; [ rewrite Heq in *; repeat rewrite ZMap.gss in *| repeat rewrite (ZMap.gso _ _ H) in * ]
  end.

Ltac simpl_query_oracle' H :=
  unfold query_oracle in H; autounfold in H; repeat simpl_hyp H; inv H; simpl in *.

Hypothesis table_a5:
  forall n, (0 <=? n) && (n <=? 18446744073709551615) = true ->
       (0 <=? Z.land n 504403158265495552) && (Z.land n 504403158265495552 <=? 18446744073709551615) = true.

Hypothesis table_a5_d7:
  forall n, (0 <=? n) && (n <=? 18446744073709551615) = true ->
       (0 <=? Z.land n 504403158265495552 / 72057594037927936) &&
       (Z.land n 504403158265495552 / 72057594037927936 <=? 18446744073709551615) = true.

Hypothesis table_a5_d7_m7:
  forall n, (0 <=? n) && (n <=? 18446744073709551615) = true ->
       (0 <=? Z.land n 504403158265495552 / 72057594037927936 * 72057594037927936) &&
       (Z.land n 504403158265495552 / 72057594037927936 * 72057594037927936 <=? 18446744073709551615) = true.

Hypothesis table_a5_d7_m7_p4:
  forall n, (0 <=? n) && (n <=? 18446744073709551615) = true ->
       (0 <=? Z.land n 504403158265495552 / 72057594037927936 * 72057594037927936 + 4096 * 512) &&
       (Z.land n 504403158265495552 / 72057594037927936 * 72057594037927936 + 4096 * 512 <=? 18446744073709551615) = true.

Hypothesis entry_to_phys_range:
  forall n l, (0 <=? n) && (n <=? 18446744073709551615) = true ->
         (0 <=? __entry_to_phys n l) && (__entry_to_phys n l <=? 18446744073709551615) = true.

Hypothesis orb_64_range:
  forall a b, (0 <=? a) && (a <=? 18446744073709551615) = true ->
         (0 <=? b) && (b <=? 18446744073709551615) = true ->
         (0 <=? Z.lor a b) && (Z.lor a b <=? 18446744073709551615) = true.

Hypothesis addr_to_idx_range:
  forall n a, (0 <=? n) && (n <=? 18446744073709551615) = true ->
         (0 <=? (__addr_to_idx n a)) && ((__addr_to_idx n a) <=? 18446744073709551615) = true.

Hypothesis entry_to_gidx_range:
  forall n a,  (0 <=? n) && (n <=? 18446744073709551615) = true ->
          (0 <=? __addr_to_gidx (__entry_to_phys n a)) && (__addr_to_gidx (__entry_to_phys n a) <=? 4294967295) = true.

Hypothesis PTE_PA_mod_4096:
  forall n, (0 <=? n) && (n <=? 18446744073709551615) = true ->
       (Z.land n 281474976706560) mod 4096 =? 0 = true.

Ltac solve_table_range :=
  repeat
    match goal with
    | [H: (0 <=? ?n) && (?n <=? 18446744073709551615) = true
       |- context[(0 <=? Z.land ?n 504403158265495552) && (Z.land ?n 504403158265495552 <=? 18446744073709551615)]] =>
      rewrite (table_a5 n H)
    | [H: (0 <=? ?n) && (?n <=? 18446744073709551615) = true
       |- context[(0 <=? Z.land ?n 504403158265495552) && (Z.land ?n 504403158265495552 <=? 18446744073709551615)]] =>
      rewrite (table_a5 n H)
    | [H: (0 <=? ?n) && (?n <=? 18446744073709551615) = true
       |- context[(0 <=? Z.land ?n 504403158265495552 / 72057594037927936) &&
                 (Z.land ?n 504403158265495552 / 72057594037927936 <=? 18446744073709551615)]] =>
      rewrite (table_a5_d7 n H)
    | [H: (0 <=? ?n) && (?n <=? 18446744073709551615) = true
       |- context[(0 <=? Z.land ?n 504403158265495552 / 72057594037927936 * 72057594037927936) &&
                 (Z.land ?n 504403158265495552 / 72057594037927936 * 72057594037927936 <=? 18446744073709551615)]] =>
      rewrite (table_a5_d7_m7 n H)
    | [H: (0 <=? ?n) && (?n <=? 18446744073709551615) = true
       |- context[(0 <=? Z.land ?n 504403158265495552 / 72057594037927936 * 72057594037927936 + 4096 * 512) &&
                 (Z.land ?n 504403158265495552 / 72057594037927936 * 72057594037927936 + 4096 * 512 <=? 18446744073709551615)]] =>
      rewrite (table_a5_d7_m7_p4 n H)
    | [H: (0 <=? ?n) && (?n <=? 18446744073709551615) = true
       |- context[(0 <=? __entry_to_phys ?n ?l) && (__entry_to_phys ?n ?l <=? 18446744073709551615)]] =>
      rewrite (entry_to_phys_range n l H)

    | [H1: (0 <=? ?a) && (?a <=? 18446744073709551615) = true,
           H2: (0 <=? ?b) && (?b <=? 18446744073709551615) = true |-
       context[(0 <=? Z.lor ?a ?b) && (Z.lor ?a ?b <=? 18446744073709551615)]] =>
      rewrite (orb_64_range _ _ H1 H2)
    | [H: (0 <=? ?n) && (?n <=? 18446744073709551615) = true |-
       context[(0 <=? (__addr_to_idx ?n ?a)) && ((__addr_to_idx ?n ?a) <=? 18446744073709551615)]] =>
      rewrite (addr_to_idx_range _ _ H)
    | [H: (0 <=? ?n) && (?n <=? 18446744073709551615) = true |-
       context[(0 <=? __addr_to_gidx (__entry_to_phys ?n ?a)) && (__addr_to_gidx (__entry_to_phys ?n ?a) <=? 4294967295)]] =>
      rewrite (entry_to_gidx_range _ _ H)
    | [H: (0 <=? ?n) && (?n <=? 18446744073709551615) = true |-
       context[(Z.land ?n 281474976706560) mod 4096 =? 0]] =>
      rewrite (PTE_PA_mod_4096 _ H)
    end.

Hypothesis addr_to_gidx_not_0:
  forall n, (0 <=? n) && (n <=? 18446744073709551615) = true -> __addr_to_gidx n =? 0 = false.

Hypothesis IPA_PTE_IPA:
  forall n e l k,
    is_int64 n = true ->
    is_int64 e = true ->
    0 <= k < 72057594037927936 ->
    Z.land (Z.lor (Z.lor (Z.land n 504403158265495552 / 72057594037927936 * 72057594037927936) (__entry_to_phys e l)) k) 504403158265495552 / 72057594037927936 = Z.land n 504403158265495552 / 72057594037927936.

Hypothesis IPA_PTE_IPA2:
  forall n e l,
    is_int64 n = true ->
    is_int64 e = true ->
    Z.land (Z.lor (Z.land n 504403158265495552 / 72057594037927936 * 72057594037927936) (__entry_to_phys e l)) 504403158265495552 / 72057594037927936 = Z.land n 504403158265495552 / 72057594037927936.

Hypothesis pte_4096_range:
  forall n l a,  (0 <=? n) && (n <=? 18446744073709551615) = true -> 0 <= a < 4 ->
            (0 <=? Z.lor (a * 72057594037927936) (__entry_to_phys n l) + 4096 * 512) &&
            (Z.lor (a * 72057594037927936) (__entry_to_phys n l) + 4096 * 512 <=? 18446744073709551615) = true.

Hypothesis pte_2011_4096_range:
  forall n l a, (0 <=? n) && (n <=? 18446744073709551615) = true -> 0 <= a < 4 ->
           (0 <=? Z.lor (Z.lor (a * 72057594037927936) (__entry_to_phys n l)) 2011 + 4096 * 512) &&
           (Z.lor (Z.lor (a * 72057594037927936) (__entry_to_phys n l)) 2011 + 4096 * 512 <=? 18446744073709551615) = true.

Ltac destruct_if' H :=
  let H := fresh "Case" in
  match type of H with
  | context [if ?c then _ else _] => destruct c eqn:H; simpl
  end.

Ltac specialize_trivial H :=
  match type of H with
  | ?x = ?x -> ?P =>
    let T := fresh "tmp" in
    assert(T: P) by (apply H; reflexivity); clear H; rename T into H
  end.

Hypothesis addr_eq_gidx_offs:
  forall addr1 addr2, __addr_to_gidx addr1 = __addr_to_gidx addr2 /\ addr1 mod 4096 = addr2 mod 4096 <-> addr1 = addr2.

Hypothesis ISS_RT_range: forall esr, 0 <= __ESR_EL2_SYSREG_ISS_RT esr <= 30.

Hypothesis esr_srt_range: forall esr, 0 <= __esr_srt esr <= 30.


Lemma get_reg_0: forall regs, get_reg 0 regs = r_x0 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_1: forall regs, get_reg 1 regs = r_x1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_2: forall regs, get_reg 2 regs = r_x2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_3: forall regs, get_reg 3 regs = r_x3 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_4: forall regs, get_reg 4 regs = r_x4 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_5: forall regs, get_reg 5 regs = r_x5 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_6: forall regs, get_reg 6 regs = r_x6 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_7: forall regs, get_reg 7 regs = r_x7 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_8: forall regs, get_reg 8 regs = r_x8 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_9: forall regs, get_reg 9 regs = r_x9 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_10: forall regs, get_reg 10 regs = r_x10 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_11: forall regs, get_reg 11 regs = r_x11 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_12: forall regs, get_reg 12 regs = r_x12 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_13: forall regs, get_reg 13 regs = r_x13 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_14: forall regs, get_reg 14 regs = r_x14 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_15: forall regs, get_reg 15 regs = r_x15 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_16: forall regs, get_reg 16 regs = r_x16 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_17: forall regs, get_reg 17 regs = r_x17 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_18: forall regs, get_reg 18 regs = r_x18 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_19: forall regs, get_reg 19 regs = r_x19 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_20: forall regs, get_reg 20 regs = r_x20 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_21: forall regs, get_reg 21 regs = r_x21 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_22: forall regs, get_reg 22 regs = r_x22 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_23: forall regs, get_reg 23 regs = r_x23 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_24: forall regs, get_reg 24 regs = r_x24 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_25: forall regs, get_reg 25 regs = r_x25 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_26: forall regs, get_reg 26 regs = r_x26 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_27: forall regs, get_reg 27 regs = r_x27 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_28: forall regs, get_reg 28 regs = r_x28 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_29: forall regs, get_reg 29 regs = r_x29 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_30: forall regs, get_reg 30 regs = r_x30 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_31: forall regs, get_reg 31 regs = r_lr regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_32: forall regs, get_reg 32 regs = r_cntp_ctl_el0 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_33: forall regs, get_reg 33 regs = r_cntp_cval_el0 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_34: forall regs, get_reg 34 regs = r_cntp_tval_el0 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_35: forall regs, get_reg 35 regs = r_cntv_ctl_el0 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_36: forall regs, get_reg 36 regs = r_cntv_cval_el0 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_37: forall regs, get_reg 37 regs = r_cntv_tval_el0 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_38: forall regs, get_reg 38 regs = r_sp_el0 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_39: forall regs, get_reg 39 regs = r_pmcr_el0 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_40: forall regs, get_reg 40 regs = r_pmuserenr_el0 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_41: forall regs, get_reg 41 regs = r_tpidrro_el0 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_42: forall regs, get_reg 42 regs = r_tpidr_el0 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_43: forall regs, get_reg 43 regs = r_sp_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_44: forall regs, get_reg 44 regs = r_elr_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_45: forall regs, get_reg 45 regs = r_spsr_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_46: forall regs, get_reg 46 regs = r_csselr_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_47: forall regs, get_reg 47 regs = r_sctlr_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_48: forall regs, get_reg 48 regs = r_actlr_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_49: forall regs, get_reg 49 regs = r_cpacr_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_50: forall regs, get_reg 50 regs = r_zcr_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_51: forall regs, get_reg 51 regs = r_ttbr0_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_52: forall regs, get_reg 52 regs = r_ttbr1_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_53: forall regs, get_reg 53 regs = r_tcr_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_54: forall regs, get_reg 54 regs = r_esr_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_55: forall regs, get_reg 55 regs = r_afsr0_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_56: forall regs, get_reg 56 regs = r_afsr1_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_57: forall regs, get_reg 57 regs = r_far_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_58: forall regs, get_reg 58 regs = r_mair_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_59: forall regs, get_reg 59 regs = r_vbar_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_60: forall regs, get_reg 60 regs = r_contextidr_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_61: forall regs, get_reg 61 regs = r_tpidr_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_62: forall regs, get_reg 62 regs = r_amair_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_63: forall regs, get_reg 63 regs = r_cntkctl_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_64: forall regs, get_reg 64 regs = r_par_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_65: forall regs, get_reg 65 regs = r_mdscr_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_66: forall regs, get_reg 66 regs = r_mdccint_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_67: forall regs, get_reg 67 regs = r_disr_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_68: forall regs, get_reg 68 regs = r_mpam0_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_69: forall regs, get_reg 69 regs = r_cnthctl_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_70: forall regs, get_reg 70 regs = r_cntvoff_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_71: forall regs, get_reg 71 regs = r_cntpoff_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_72: forall regs, get_reg 72 regs = r_vmpidr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_73: forall regs, get_reg 73 regs = r_vttbr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_74: forall regs, get_reg 74 regs = r_vtcr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_75: forall regs, get_reg 75 regs = r_hcr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_76: forall regs, get_reg 76 regs = r_actlr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_77: forall regs, get_reg 77 regs = r_afsr0_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_78: forall regs, get_reg 78 regs = r_afsr1_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_79: forall regs, get_reg 79 regs = r_amair_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_80: forall regs, get_reg 80 regs = r_cptr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_81: forall regs, get_reg 81 regs = r_elr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_82: forall regs, get_reg 82 regs = r_esr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_83: forall regs, get_reg 83 regs = r_far_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_84: forall regs, get_reg 84 regs = r_hacr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_85: forall regs, get_reg 85 regs = r_hpfar_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_86: forall regs, get_reg 86 regs = r_hstr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_87: forall regs, get_reg 87 regs = r_mair_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_88: forall regs, get_reg 88 regs = r_mpam_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_89: forall regs, get_reg 89 regs = r_mpamhcr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_90: forall regs, get_reg 90 regs = r_pmscr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_91: forall regs, get_reg 91 regs = r_sctlr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_92: forall regs, get_reg 92 regs = r_scxtnum_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_93: forall regs, get_reg 93 regs = r_sp_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_94: forall regs, get_reg 94 regs = r_spsr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_95: forall regs, get_reg 95 regs = r_tcr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_96: forall regs, get_reg 96 regs = r_tfsr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_97: forall regs, get_reg 97 regs = r_tpidr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_98: forall regs, get_reg 98 regs = r_trfcr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_99: forall regs, get_reg 99 regs = r_ttbr0_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_100: forall regs, get_reg 100 regs = r_ttbr1_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_101: forall regs, get_reg 101 regs = r_vbar_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_102: forall regs, get_reg 102 regs = r_vdisr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_103: forall regs, get_reg 103 regs = r_vncr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_104: forall regs, get_reg 104 regs = r_vpidr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_105: forall regs, get_reg 105 regs = r_vsesr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_106: forall regs, get_reg 106 regs = r_vstcr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_107: forall regs, get_reg 107 regs = r_vsttbr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_108: forall regs, get_reg 108 regs = r_zcr_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_109: forall regs, get_reg 109 regs = r_icc_sre_el2 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_110: forall regs, get_reg 110 regs = r_icc_hppir1_el1 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_111: forall regs, get_reg 111 regs = r_spsr_el3 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_112: forall regs, get_reg 112 regs = r_elr_el3 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_113: forall regs, get_reg 113 regs = r_tpidr_el3 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_114: forall regs, get_reg 114 regs = r_esr_el3 regs. Proof. intros; reflexivity. Qed.
Lemma get_reg_115: forall regs, get_reg 115 regs = r_scr_el3 regs. Proof. intros; reflexivity. Qed.
Lemma set_reg_0: forall regs val, set_reg 0 val regs = regs {r_x0: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_1: forall regs val, set_reg 1 val regs = regs {r_x1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_2: forall regs val, set_reg 2 val regs = regs {r_x2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_3: forall regs val, set_reg 3 val regs = regs {r_x3: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_4: forall regs val, set_reg 4 val regs = regs {r_x4: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_5: forall regs val, set_reg 5 val regs = regs {r_x5: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_6: forall regs val, set_reg 6 val regs = regs {r_x6: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_7: forall regs val, set_reg 7 val regs = regs {r_x7: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_8: forall regs val, set_reg 8 val regs = regs {r_x8: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_9: forall regs val, set_reg 9 val regs = regs {r_x9: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_10: forall regs val, set_reg 10 val regs = regs {r_x10: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_11: forall regs val, set_reg 11 val regs = regs {r_x11: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_12: forall regs val, set_reg 12 val regs = regs {r_x12: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_13: forall regs val, set_reg 13 val regs = regs {r_x13: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_14: forall regs val, set_reg 14 val regs = regs {r_x14: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_15: forall regs val, set_reg 15 val regs = regs {r_x15: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_16: forall regs val, set_reg 16 val regs = regs {r_x16: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_17: forall regs val, set_reg 17 val regs = regs {r_x17: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_18: forall regs val, set_reg 18 val regs = regs {r_x18: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_19: forall regs val, set_reg 19 val regs = regs {r_x19: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_20: forall regs val, set_reg 20 val regs = regs {r_x20: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_21: forall regs val, set_reg 21 val regs = regs {r_x21: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_22: forall regs val, set_reg 22 val regs = regs {r_x22: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_23: forall regs val, set_reg 23 val regs = regs {r_x23: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_24: forall regs val, set_reg 24 val regs = regs {r_x24: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_25: forall regs val, set_reg 25 val regs = regs {r_x25: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_26: forall regs val, set_reg 26 val regs = regs {r_x26: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_27: forall regs val, set_reg 27 val regs = regs {r_x27: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_28: forall regs val, set_reg 28 val regs = regs {r_x28: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_29: forall regs val, set_reg 29 val regs = regs {r_x29: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_30: forall regs val, set_reg 30 val regs = regs {r_x30: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_31: forall regs val, set_reg 31 val regs = regs {r_lr: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_32: forall regs val, set_reg 32 val regs = regs {r_cntp_ctl_el0: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_33: forall regs val, set_reg 33 val regs = regs {r_cntp_cval_el0: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_34: forall regs val, set_reg 34 val regs = regs {r_cntp_tval_el0: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_35: forall regs val, set_reg 35 val regs = regs {r_cntv_ctl_el0: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_36: forall regs val, set_reg 36 val regs = regs {r_cntv_cval_el0: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_37: forall regs val, set_reg 37 val regs = regs {r_cntv_tval_el0: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_38: forall regs val, set_reg 38 val regs = regs {r_sp_el0: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_39: forall regs val, set_reg 39 val regs = regs {r_pmcr_el0: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_40: forall regs val, set_reg 40 val regs = regs {r_pmuserenr_el0: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_41: forall regs val, set_reg 41 val regs = regs {r_tpidrro_el0: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_42: forall regs val, set_reg 42 val regs = regs {r_tpidr_el0: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_43: forall regs val, set_reg 43 val regs = regs {r_sp_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_44: forall regs val, set_reg 44 val regs = regs {r_elr_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_45: forall regs val, set_reg 45 val regs = regs {r_spsr_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_46: forall regs val, set_reg 46 val regs = regs {r_csselr_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_47: forall regs val, set_reg 47 val regs = regs {r_sctlr_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_48: forall regs val, set_reg 48 val regs = regs {r_actlr_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_49: forall regs val, set_reg 49 val regs = regs {r_cpacr_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_50: forall regs val, set_reg 50 val regs = regs {r_zcr_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_51: forall regs val, set_reg 51 val regs = regs {r_ttbr0_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_52: forall regs val, set_reg 52 val regs = regs {r_ttbr1_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_53: forall regs val, set_reg 53 val regs = regs {r_tcr_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_54: forall regs val, set_reg 54 val regs = regs {r_esr_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_55: forall regs val, set_reg 55 val regs = regs {r_afsr0_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_56: forall regs val, set_reg 56 val regs = regs {r_afsr1_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_57: forall regs val, set_reg 57 val regs = regs {r_far_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_58: forall regs val, set_reg 58 val regs = regs {r_mair_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_59: forall regs val, set_reg 59 val regs = regs {r_vbar_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_60: forall regs val, set_reg 60 val regs = regs {r_contextidr_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_61: forall regs val, set_reg 61 val regs = regs {r_tpidr_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_62: forall regs val, set_reg 62 val regs = regs {r_amair_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_63: forall regs val, set_reg 63 val regs = regs {r_cntkctl_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_64: forall regs val, set_reg 64 val regs = regs {r_par_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_65: forall regs val, set_reg 65 val regs = regs {r_mdscr_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_66: forall regs val, set_reg 66 val regs = regs {r_mdccint_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_67: forall regs val, set_reg 67 val regs = regs {r_disr_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_68: forall regs val, set_reg 68 val regs = regs {r_mpam0_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_69: forall regs val, set_reg 69 val regs = regs {r_cnthctl_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_70: forall regs val, set_reg 70 val regs = regs {r_cntvoff_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_71: forall regs val, set_reg 71 val regs = regs {r_cntpoff_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_72: forall regs val, set_reg 72 val regs = regs {r_vmpidr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_73: forall regs val, set_reg 73 val regs = regs {r_vttbr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_74: forall regs val, set_reg 74 val regs = regs {r_vtcr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_75: forall regs val, set_reg 75 val regs = regs {r_hcr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_76: forall regs val, set_reg 76 val regs = regs {r_actlr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_77: forall regs val, set_reg 77 val regs = regs {r_afsr0_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_78: forall regs val, set_reg 78 val regs = regs {r_afsr1_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_79: forall regs val, set_reg 79 val regs = regs {r_amair_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_80: forall regs val, set_reg 80 val regs = regs {r_cptr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_81: forall regs val, set_reg 81 val regs = regs {r_elr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_82: forall regs val, set_reg 82 val regs = regs {r_esr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_83: forall regs val, set_reg 83 val regs = regs {r_far_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_84: forall regs val, set_reg 84 val regs = regs {r_hacr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_85: forall regs val, set_reg 85 val regs = regs {r_hpfar_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_86: forall regs val, set_reg 86 val regs = regs {r_hstr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_87: forall regs val, set_reg 87 val regs = regs {r_mair_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_88: forall regs val, set_reg 88 val regs = regs {r_mpam_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_89: forall regs val, set_reg 89 val regs = regs {r_mpamhcr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_90: forall regs val, set_reg 90 val regs = regs {r_pmscr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_91: forall regs val, set_reg 91 val regs = regs {r_sctlr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_92: forall regs val, set_reg 92 val regs = regs {r_scxtnum_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_93: forall regs val, set_reg 93 val regs = regs {r_sp_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_94: forall regs val, set_reg 94 val regs = regs {r_spsr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_95: forall regs val, set_reg 95 val regs = regs {r_tcr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_96: forall regs val, set_reg 96 val regs = regs {r_tfsr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_97: forall regs val, set_reg 97 val regs = regs {r_tpidr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_98: forall regs val, set_reg 98 val regs = regs {r_trfcr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_99: forall regs val, set_reg 99 val regs = regs {r_ttbr0_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_100: forall regs val, set_reg 100 val regs = regs {r_ttbr1_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_101: forall regs val, set_reg 101 val regs = regs {r_vbar_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_102: forall regs val, set_reg 102 val regs = regs {r_vdisr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_103: forall regs val, set_reg 103 val regs = regs {r_vncr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_104: forall regs val, set_reg 104 val regs = regs {r_vpidr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_105: forall regs val, set_reg 105 val regs = regs {r_vsesr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_106: forall regs val, set_reg 106 val regs = regs {r_vstcr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_107: forall regs val, set_reg 107 val regs = regs {r_vsttbr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_108: forall regs val, set_reg 108 val regs = regs {r_zcr_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_109: forall regs val, set_reg 109 val regs = regs {r_icc_sre_el2: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_110: forall regs val, set_reg 110 val regs = regs {r_icc_hppir1_el1: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_111: forall regs val, set_reg 111 val regs = regs {r_spsr_el3: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_112: forall regs val, set_reg 112 val regs = regs {r_elr_el3: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_113: forall regs val, set_reg 113 val regs = regs {r_tpidr_el3: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_114: forall regs val, set_reg 114 val regs = regs {r_esr_el3: val}. Proof. intros; reflexivity. Qed.
Lemma set_reg_115: forall regs val, set_reg 115 val regs = regs {r_scr_el3: val}. Proof. intros; reflexivity. Qed.
Ltac simpl_update_reg :=
  match goal with
  | [|- context[get_reg 0 ?reg]] => rewrite (get_reg_0 reg)
  | [|- context[set_reg 0 ?val ?reg]] => rewrite (set_reg_0 reg val)
  | [|- context[get_reg 1 ?reg]] => rewrite (get_reg_1 reg)
  | [|- context[set_reg 1 ?val ?reg]] => rewrite (set_reg_1 reg val)
  | [|- context[get_reg 2 ?reg]] => rewrite (get_reg_2 reg)
  | [|- context[set_reg 2 ?val ?reg]] => rewrite (set_reg_2 reg val)
  | [|- context[get_reg 3 ?reg]] => rewrite (get_reg_3 reg)
  | [|- context[set_reg 3 ?val ?reg]] => rewrite (set_reg_3 reg val)
  | [|- context[get_reg 4 ?reg]] => rewrite (get_reg_4 reg)
  | [|- context[set_reg 4 ?val ?reg]] => rewrite (set_reg_4 reg val)
  | [|- context[get_reg 5 ?reg]] => rewrite (get_reg_5 reg)
  | [|- context[set_reg 5 ?val ?reg]] => rewrite (set_reg_5 reg val)
  | [|- context[get_reg 6 ?reg]] => rewrite (get_reg_6 reg)
  | [|- context[set_reg 6 ?val ?reg]] => rewrite (set_reg_6 reg val)
  | [|- context[get_reg 7 ?reg]] => rewrite (get_reg_7 reg)
  | [|- context[set_reg 7 ?val ?reg]] => rewrite (set_reg_7 reg val)
  | [|- context[get_reg 8 ?reg]] => rewrite (get_reg_8 reg)
  | [|- context[set_reg 8 ?val ?reg]] => rewrite (set_reg_8 reg val)
  | [|- context[get_reg 9 ?reg]] => rewrite (get_reg_9 reg)
  | [|- context[set_reg 9 ?val ?reg]] => rewrite (set_reg_9 reg val)
  | [|- context[get_reg 10 ?reg]] => rewrite (get_reg_10 reg)
  | [|- context[set_reg 10 ?val ?reg]] => rewrite (set_reg_10 reg val)
  | [|- context[get_reg 11 ?reg]] => rewrite (get_reg_11 reg)
  | [|- context[set_reg 11 ?val ?reg]] => rewrite (set_reg_11 reg val)
  | [|- context[get_reg 12 ?reg]] => rewrite (get_reg_12 reg)
  | [|- context[set_reg 12 ?val ?reg]] => rewrite (set_reg_12 reg val)
  | [|- context[get_reg 13 ?reg]] => rewrite (get_reg_13 reg)
  | [|- context[set_reg 13 ?val ?reg]] => rewrite (set_reg_13 reg val)
  | [|- context[get_reg 14 ?reg]] => rewrite (get_reg_14 reg)
  | [|- context[set_reg 14 ?val ?reg]] => rewrite (set_reg_14 reg val)
  | [|- context[get_reg 15 ?reg]] => rewrite (get_reg_15 reg)
  | [|- context[set_reg 15 ?val ?reg]] => rewrite (set_reg_15 reg val)
  | [|- context[get_reg 16 ?reg]] => rewrite (get_reg_16 reg)
  | [|- context[set_reg 16 ?val ?reg]] => rewrite (set_reg_16 reg val)
  | [|- context[get_reg 17 ?reg]] => rewrite (get_reg_17 reg)
  | [|- context[set_reg 17 ?val ?reg]] => rewrite (set_reg_17 reg val)
  | [|- context[get_reg 18 ?reg]] => rewrite (get_reg_18 reg)
  | [|- context[set_reg 18 ?val ?reg]] => rewrite (set_reg_18 reg val)
  | [|- context[get_reg 19 ?reg]] => rewrite (get_reg_19 reg)
  | [|- context[set_reg 19 ?val ?reg]] => rewrite (set_reg_19 reg val)
  | [|- context[get_reg 20 ?reg]] => rewrite (get_reg_20 reg)
  | [|- context[set_reg 20 ?val ?reg]] => rewrite (set_reg_20 reg val)
  | [|- context[get_reg 21 ?reg]] => rewrite (get_reg_21 reg)
  | [|- context[set_reg 21 ?val ?reg]] => rewrite (set_reg_21 reg val)
  | [|- context[get_reg 22 ?reg]] => rewrite (get_reg_22 reg)
  | [|- context[set_reg 22 ?val ?reg]] => rewrite (set_reg_22 reg val)
  | [|- context[get_reg 23 ?reg]] => rewrite (get_reg_23 reg)
  | [|- context[set_reg 23 ?val ?reg]] => rewrite (set_reg_23 reg val)
  | [|- context[get_reg 24 ?reg]] => rewrite (get_reg_24 reg)
  | [|- context[set_reg 24 ?val ?reg]] => rewrite (set_reg_24 reg val)
  | [|- context[get_reg 25 ?reg]] => rewrite (get_reg_25 reg)
  | [|- context[set_reg 25 ?val ?reg]] => rewrite (set_reg_25 reg val)
  | [|- context[get_reg 26 ?reg]] => rewrite (get_reg_26 reg)
  | [|- context[set_reg 26 ?val ?reg]] => rewrite (set_reg_26 reg val)
  | [|- context[get_reg 27 ?reg]] => rewrite (get_reg_27 reg)
  | [|- context[set_reg 27 ?val ?reg]] => rewrite (set_reg_27 reg val)
  | [|- context[get_reg 28 ?reg]] => rewrite (get_reg_28 reg)
  | [|- context[set_reg 28 ?val ?reg]] => rewrite (set_reg_28 reg val)
  | [|- context[get_reg 29 ?reg]] => rewrite (get_reg_29 reg)
  | [|- context[set_reg 29 ?val ?reg]] => rewrite (set_reg_29 reg val)
  | [|- context[get_reg 30 ?reg]] => rewrite (get_reg_30 reg)
  | [|- context[set_reg 30 ?val ?reg]] => rewrite (set_reg_30 reg val)
  | [|- context[get_reg 31 ?reg]] => rewrite (get_reg_31 reg)
  | [|- context[set_reg 31 ?val ?reg]] => rewrite (set_reg_31 reg val)
  | [|- context[get_reg 32 ?reg]] => rewrite (get_reg_32 reg)
  | [|- context[set_reg 32 ?val ?reg]] => rewrite (set_reg_32 reg val)
  | [|- context[get_reg 33 ?reg]] => rewrite (get_reg_33 reg)
  | [|- context[set_reg 33 ?val ?reg]] => rewrite (set_reg_33 reg val)
  | [|- context[get_reg 34 ?reg]] => rewrite (get_reg_34 reg)
  | [|- context[set_reg 34 ?val ?reg]] => rewrite (set_reg_34 reg val)
  | [|- context[get_reg 35 ?reg]] => rewrite (get_reg_35 reg)
  | [|- context[set_reg 35 ?val ?reg]] => rewrite (set_reg_35 reg val)
  | [|- context[get_reg 36 ?reg]] => rewrite (get_reg_36 reg)
  | [|- context[set_reg 36 ?val ?reg]] => rewrite (set_reg_36 reg val)
  | [|- context[get_reg 37 ?reg]] => rewrite (get_reg_37 reg)
  | [|- context[set_reg 37 ?val ?reg]] => rewrite (set_reg_37 reg val)
  | [|- context[get_reg 38 ?reg]] => rewrite (get_reg_38 reg)
  | [|- context[set_reg 38 ?val ?reg]] => rewrite (set_reg_38 reg val)
  | [|- context[get_reg 39 ?reg]] => rewrite (get_reg_39 reg)
  | [|- context[set_reg 39 ?val ?reg]] => rewrite (set_reg_39 reg val)
  | [|- context[get_reg 40 ?reg]] => rewrite (get_reg_40 reg)
  | [|- context[set_reg 40 ?val ?reg]] => rewrite (set_reg_40 reg val)
  | [|- context[get_reg 41 ?reg]] => rewrite (get_reg_41 reg)
  | [|- context[set_reg 41 ?val ?reg]] => rewrite (set_reg_41 reg val)
  | [|- context[get_reg 42 ?reg]] => rewrite (get_reg_42 reg)
  | [|- context[set_reg 42 ?val ?reg]] => rewrite (set_reg_42 reg val)
  | [|- context[get_reg 43 ?reg]] => rewrite (get_reg_43 reg)
  | [|- context[set_reg 43 ?val ?reg]] => rewrite (set_reg_43 reg val)
  | [|- context[get_reg 44 ?reg]] => rewrite (get_reg_44 reg)
  | [|- context[set_reg 44 ?val ?reg]] => rewrite (set_reg_44 reg val)
  | [|- context[get_reg 45 ?reg]] => rewrite (get_reg_45 reg)
  | [|- context[set_reg 45 ?val ?reg]] => rewrite (set_reg_45 reg val)
  | [|- context[get_reg 46 ?reg]] => rewrite (get_reg_46 reg)
  | [|- context[set_reg 46 ?val ?reg]] => rewrite (set_reg_46 reg val)
  | [|- context[get_reg 47 ?reg]] => rewrite (get_reg_47 reg)
  | [|- context[set_reg 47 ?val ?reg]] => rewrite (set_reg_47 reg val)
  | [|- context[get_reg 48 ?reg]] => rewrite (get_reg_48 reg)
  | [|- context[set_reg 48 ?val ?reg]] => rewrite (set_reg_48 reg val)
  | [|- context[get_reg 49 ?reg]] => rewrite (get_reg_49 reg)
  | [|- context[set_reg 49 ?val ?reg]] => rewrite (set_reg_49 reg val)
  | [|- context[get_reg 50 ?reg]] => rewrite (get_reg_50 reg)
  | [|- context[set_reg 50 ?val ?reg]] => rewrite (set_reg_50 reg val)
  | [|- context[get_reg 51 ?reg]] => rewrite (get_reg_51 reg)
  | [|- context[set_reg 51 ?val ?reg]] => rewrite (set_reg_51 reg val)
  | [|- context[get_reg 52 ?reg]] => rewrite (get_reg_52 reg)
  | [|- context[set_reg 52 ?val ?reg]] => rewrite (set_reg_52 reg val)
  | [|- context[get_reg 53 ?reg]] => rewrite (get_reg_53 reg)
  | [|- context[set_reg 53 ?val ?reg]] => rewrite (set_reg_53 reg val)
  | [|- context[get_reg 54 ?reg]] => rewrite (get_reg_54 reg)
  | [|- context[set_reg 54 ?val ?reg]] => rewrite (set_reg_54 reg val)
  | [|- context[get_reg 55 ?reg]] => rewrite (get_reg_55 reg)
  | [|- context[set_reg 55 ?val ?reg]] => rewrite (set_reg_55 reg val)
  | [|- context[get_reg 56 ?reg]] => rewrite (get_reg_56 reg)
  | [|- context[set_reg 56 ?val ?reg]] => rewrite (set_reg_56 reg val)
  | [|- context[get_reg 57 ?reg]] => rewrite (get_reg_57 reg)
  | [|- context[set_reg 57 ?val ?reg]] => rewrite (set_reg_57 reg val)
  | [|- context[get_reg 58 ?reg]] => rewrite (get_reg_58 reg)
  | [|- context[set_reg 58 ?val ?reg]] => rewrite (set_reg_58 reg val)
  | [|- context[get_reg 59 ?reg]] => rewrite (get_reg_59 reg)
  | [|- context[set_reg 59 ?val ?reg]] => rewrite (set_reg_59 reg val)
  | [|- context[get_reg 60 ?reg]] => rewrite (get_reg_60 reg)
  | [|- context[set_reg 60 ?val ?reg]] => rewrite (set_reg_60 reg val)
  | [|- context[get_reg 61 ?reg]] => rewrite (get_reg_61 reg)
  | [|- context[set_reg 61 ?val ?reg]] => rewrite (set_reg_61 reg val)
  | [|- context[get_reg 62 ?reg]] => rewrite (get_reg_62 reg)
  | [|- context[set_reg 62 ?val ?reg]] => rewrite (set_reg_62 reg val)
  | [|- context[get_reg 63 ?reg]] => rewrite (get_reg_63 reg)
  | [|- context[set_reg 63 ?val ?reg]] => rewrite (set_reg_63 reg val)
  | [|- context[get_reg 64 ?reg]] => rewrite (get_reg_64 reg)
  | [|- context[set_reg 64 ?val ?reg]] => rewrite (set_reg_64 reg val)
  | [|- context[get_reg 65 ?reg]] => rewrite (get_reg_65 reg)
  | [|- context[set_reg 65 ?val ?reg]] => rewrite (set_reg_65 reg val)
  | [|- context[get_reg 66 ?reg]] => rewrite (get_reg_66 reg)
  | [|- context[set_reg 66 ?val ?reg]] => rewrite (set_reg_66 reg val)
  | [|- context[get_reg 67 ?reg]] => rewrite (get_reg_67 reg)
  | [|- context[set_reg 67 ?val ?reg]] => rewrite (set_reg_67 reg val)
  | [|- context[get_reg 68 ?reg]] => rewrite (get_reg_68 reg)
  | [|- context[set_reg 68 ?val ?reg]] => rewrite (set_reg_68 reg val)
  | [|- context[get_reg 69 ?reg]] => rewrite (get_reg_69 reg)
  | [|- context[set_reg 69 ?val ?reg]] => rewrite (set_reg_69 reg val)
  | [|- context[get_reg 70 ?reg]] => rewrite (get_reg_70 reg)
  | [|- context[set_reg 70 ?val ?reg]] => rewrite (set_reg_70 reg val)
  | [|- context[get_reg 71 ?reg]] => rewrite (get_reg_71 reg)
  | [|- context[set_reg 71 ?val ?reg]] => rewrite (set_reg_71 reg val)
  | [|- context[get_reg 72 ?reg]] => rewrite (get_reg_72 reg)
  | [|- context[set_reg 72 ?val ?reg]] => rewrite (set_reg_72 reg val)
  | [|- context[get_reg 73 ?reg]] => rewrite (get_reg_73 reg)
  | [|- context[set_reg 73 ?val ?reg]] => rewrite (set_reg_73 reg val)
  | [|- context[get_reg 74 ?reg]] => rewrite (get_reg_74 reg)
  | [|- context[set_reg 74 ?val ?reg]] => rewrite (set_reg_74 reg val)
  | [|- context[get_reg 75 ?reg]] => rewrite (get_reg_75 reg)
  | [|- context[set_reg 75 ?val ?reg]] => rewrite (set_reg_75 reg val)
  | [|- context[get_reg 76 ?reg]] => rewrite (get_reg_76 reg)
  | [|- context[set_reg 76 ?val ?reg]] => rewrite (set_reg_76 reg val)
  | [|- context[get_reg 77 ?reg]] => rewrite (get_reg_77 reg)
  | [|- context[set_reg 77 ?val ?reg]] => rewrite (set_reg_77 reg val)
  | [|- context[get_reg 78 ?reg]] => rewrite (get_reg_78 reg)
  | [|- context[set_reg 78 ?val ?reg]] => rewrite (set_reg_78 reg val)
  | [|- context[get_reg 79 ?reg]] => rewrite (get_reg_79 reg)
  | [|- context[set_reg 79 ?val ?reg]] => rewrite (set_reg_79 reg val)
  | [|- context[get_reg 80 ?reg]] => rewrite (get_reg_80 reg)
  | [|- context[set_reg 80 ?val ?reg]] => rewrite (set_reg_80 reg val)
  | [|- context[get_reg 81 ?reg]] => rewrite (get_reg_81 reg)
  | [|- context[set_reg 81 ?val ?reg]] => rewrite (set_reg_81 reg val)
  | [|- context[get_reg 82 ?reg]] => rewrite (get_reg_82 reg)
  | [|- context[set_reg 82 ?val ?reg]] => rewrite (set_reg_82 reg val)
  | [|- context[get_reg 83 ?reg]] => rewrite (get_reg_83 reg)
  | [|- context[set_reg 83 ?val ?reg]] => rewrite (set_reg_83 reg val)
  | [|- context[get_reg 84 ?reg]] => rewrite (get_reg_84 reg)
  | [|- context[set_reg 84 ?val ?reg]] => rewrite (set_reg_84 reg val)
  | [|- context[get_reg 85 ?reg]] => rewrite (get_reg_85 reg)
  | [|- context[set_reg 85 ?val ?reg]] => rewrite (set_reg_85 reg val)
  | [|- context[get_reg 86 ?reg]] => rewrite (get_reg_86 reg)
  | [|- context[set_reg 86 ?val ?reg]] => rewrite (set_reg_86 reg val)
  | [|- context[get_reg 87 ?reg]] => rewrite (get_reg_87 reg)
  | [|- context[set_reg 87 ?val ?reg]] => rewrite (set_reg_87 reg val)
  | [|- context[get_reg 88 ?reg]] => rewrite (get_reg_88 reg)
  | [|- context[set_reg 88 ?val ?reg]] => rewrite (set_reg_88 reg val)
  | [|- context[get_reg 89 ?reg]] => rewrite (get_reg_89 reg)
  | [|- context[set_reg 89 ?val ?reg]] => rewrite (set_reg_89 reg val)
  | [|- context[get_reg 90 ?reg]] => rewrite (get_reg_90 reg)
  | [|- context[set_reg 90 ?val ?reg]] => rewrite (set_reg_90 reg val)
  | [|- context[get_reg 91 ?reg]] => rewrite (get_reg_91 reg)
  | [|- context[set_reg 91 ?val ?reg]] => rewrite (set_reg_91 reg val)
  | [|- context[get_reg 92 ?reg]] => rewrite (get_reg_92 reg)
  | [|- context[set_reg 92 ?val ?reg]] => rewrite (set_reg_92 reg val)
  | [|- context[get_reg 93 ?reg]] => rewrite (get_reg_93 reg)
  | [|- context[set_reg 93 ?val ?reg]] => rewrite (set_reg_93 reg val)
  | [|- context[get_reg 94 ?reg]] => rewrite (get_reg_94 reg)
  | [|- context[set_reg 94 ?val ?reg]] => rewrite (set_reg_94 reg val)
  | [|- context[get_reg 95 ?reg]] => rewrite (get_reg_95 reg)
  | [|- context[set_reg 95 ?val ?reg]] => rewrite (set_reg_95 reg val)
  | [|- context[get_reg 96 ?reg]] => rewrite (get_reg_96 reg)
  | [|- context[set_reg 96 ?val ?reg]] => rewrite (set_reg_96 reg val)
  | [|- context[get_reg 97 ?reg]] => rewrite (get_reg_97 reg)
  | [|- context[set_reg 97 ?val ?reg]] => rewrite (set_reg_97 reg val)
  | [|- context[get_reg 98 ?reg]] => rewrite (get_reg_98 reg)
  | [|- context[set_reg 98 ?val ?reg]] => rewrite (set_reg_98 reg val)
  | [|- context[get_reg 99 ?reg]] => rewrite (get_reg_99 reg)
  | [|- context[set_reg 99 ?val ?reg]] => rewrite (set_reg_99 reg val)
  | [|- context[get_reg 100 ?reg]] => rewrite (get_reg_100 reg)
  | [|- context[set_reg 100 ?val ?reg]] => rewrite (set_reg_100 reg val)
  | [|- context[get_reg 101 ?reg]] => rewrite (get_reg_101 reg)
  | [|- context[set_reg 101 ?val ?reg]] => rewrite (set_reg_101 reg val)
  | [|- context[get_reg 102 ?reg]] => rewrite (get_reg_102 reg)
  | [|- context[set_reg 102 ?val ?reg]] => rewrite (set_reg_102 reg val)
  | [|- context[get_reg 103 ?reg]] => rewrite (get_reg_103 reg)
  | [|- context[set_reg 103 ?val ?reg]] => rewrite (set_reg_103 reg val)
  | [|- context[get_reg 104 ?reg]] => rewrite (get_reg_104 reg)
  | [|- context[set_reg 104 ?val ?reg]] => rewrite (set_reg_104 reg val)
  | [|- context[get_reg 105 ?reg]] => rewrite (get_reg_105 reg)
  | [|- context[set_reg 105 ?val ?reg]] => rewrite (set_reg_105 reg val)
  | [|- context[get_reg 106 ?reg]] => rewrite (get_reg_106 reg)
  | [|- context[set_reg 106 ?val ?reg]] => rewrite (set_reg_106 reg val)
  | [|- context[get_reg 107 ?reg]] => rewrite (get_reg_107 reg)
  | [|- context[set_reg 107 ?val ?reg]] => rewrite (set_reg_107 reg val)
  | [|- context[get_reg 108 ?reg]] => rewrite (get_reg_108 reg)
  | [|- context[set_reg 108 ?val ?reg]] => rewrite (set_reg_108 reg val)
  | [|- context[get_reg 109 ?reg]] => rewrite (get_reg_109 reg)
  | [|- context[set_reg 109 ?val ?reg]] => rewrite (set_reg_109 reg val)
  | [|- context[get_reg 110 ?reg]] => rewrite (get_reg_110 reg)
  | [|- context[set_reg 110 ?val ?reg]] => rewrite (set_reg_110 reg val)
  | [|- context[get_reg 111 ?reg]] => rewrite (get_reg_111 reg)
  | [|- context[set_reg 111 ?val ?reg]] => rewrite (set_reg_111 reg val)
  | [|- context[get_reg 112 ?reg]] => rewrite (get_reg_112 reg)
  | [|- context[set_reg 112 ?val ?reg]] => rewrite (set_reg_112 reg val)
  | [|- context[get_reg 113 ?reg]] => rewrite (get_reg_113 reg)
  | [|- context[set_reg 113 ?val ?reg]] => rewrite (set_reg_113 reg val)
  | [|- context[get_reg 114 ?reg]] => rewrite (get_reg_114 reg)
  | [|- context[set_reg 114 ?val ?reg]] => rewrite (set_reg_114 reg val)
  | [|- context[get_reg 115 ?reg]] => rewrite (get_reg_115 reg)
  | [|- context[set_reg 115 ?val ?reg]] => rewrite (set_reg_115 reg val)
  end.

Lemma double_update_r_x0: forall d a b, d {r_x0: a} {r_x0: b} = d {r_x0: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x0: forall d, d {r_x0: (r_x0 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x1: forall d a b, d {r_x1: a} {r_x1: b} = d {r_x1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x1: forall d, d {r_x1: (r_x1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x2: forall d a b, d {r_x2: a} {r_x2: b} = d {r_x2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x2: forall d, d {r_x2: (r_x2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x3: forall d a b, d {r_x3: a} {r_x3: b} = d {r_x3: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x3: forall d, d {r_x3: (r_x3 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x4: forall d a b, d {r_x4: a} {r_x4: b} = d {r_x4: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x4: forall d, d {r_x4: (r_x4 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x5: forall d a b, d {r_x5: a} {r_x5: b} = d {r_x5: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x5: forall d, d {r_x5: (r_x5 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x6: forall d a b, d {r_x6: a} {r_x6: b} = d {r_x6: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x6: forall d, d {r_x6: (r_x6 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x7: forall d a b, d {r_x7: a} {r_x7: b} = d {r_x7: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x7: forall d, d {r_x7: (r_x7 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x8: forall d a b, d {r_x8: a} {r_x8: b} = d {r_x8: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x8: forall d, d {r_x8: (r_x8 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x9: forall d a b, d {r_x9: a} {r_x9: b} = d {r_x9: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x9: forall d, d {r_x9: (r_x9 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x10: forall d a b, d {r_x10: a} {r_x10: b} = d {r_x10: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x10: forall d, d {r_x10: (r_x10 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x11: forall d a b, d {r_x11: a} {r_x11: b} = d {r_x11: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x11: forall d, d {r_x11: (r_x11 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x12: forall d a b, d {r_x12: a} {r_x12: b} = d {r_x12: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x12: forall d, d {r_x12: (r_x12 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x13: forall d a b, d {r_x13: a} {r_x13: b} = d {r_x13: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x13: forall d, d {r_x13: (r_x13 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x14: forall d a b, d {r_x14: a} {r_x14: b} = d {r_x14: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x14: forall d, d {r_x14: (r_x14 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x15: forall d a b, d {r_x15: a} {r_x15: b} = d {r_x15: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x15: forall d, d {r_x15: (r_x15 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x16: forall d a b, d {r_x16: a} {r_x16: b} = d {r_x16: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x16: forall d, d {r_x16: (r_x16 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x17: forall d a b, d {r_x17: a} {r_x17: b} = d {r_x17: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x17: forall d, d {r_x17: (r_x17 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x18: forall d a b, d {r_x18: a} {r_x18: b} = d {r_x18: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x18: forall d, d {r_x18: (r_x18 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x19: forall d a b, d {r_x19: a} {r_x19: b} = d {r_x19: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x19: forall d, d {r_x19: (r_x19 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x20: forall d a b, d {r_x20: a} {r_x20: b} = d {r_x20: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x20: forall d, d {r_x20: (r_x20 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x21: forall d a b, d {r_x21: a} {r_x21: b} = d {r_x21: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x21: forall d, d {r_x21: (r_x21 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x22: forall d a b, d {r_x22: a} {r_x22: b} = d {r_x22: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x22: forall d, d {r_x22: (r_x22 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x23: forall d a b, d {r_x23: a} {r_x23: b} = d {r_x23: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x23: forall d, d {r_x23: (r_x23 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x24: forall d a b, d {r_x24: a} {r_x24: b} = d {r_x24: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x24: forall d, d {r_x24: (r_x24 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x25: forall d a b, d {r_x25: a} {r_x25: b} = d {r_x25: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x25: forall d, d {r_x25: (r_x25 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x26: forall d a b, d {r_x26: a} {r_x26: b} = d {r_x26: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x26: forall d, d {r_x26: (r_x26 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x27: forall d a b, d {r_x27: a} {r_x27: b} = d {r_x27: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x27: forall d, d {r_x27: (r_x27 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x28: forall d a b, d {r_x28: a} {r_x28: b} = d {r_x28: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x28: forall d, d {r_x28: (r_x28 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x29: forall d a b, d {r_x29: a} {r_x29: b} = d {r_x29: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x29: forall d, d {r_x29: (r_x29 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_x30: forall d a b, d {r_x30: a} {r_x30: b} = d {r_x30: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_x30: forall d, d {r_x30: (r_x30 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_lr: forall d a b, d {r_lr: a} {r_lr: b} = d {r_lr: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_lr: forall d, d {r_lr: (r_lr d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_cntp_ctl_el0: forall d a b, d {r_cntp_ctl_el0: a} {r_cntp_ctl_el0: b} = d {r_cntp_ctl_el0: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_cntp_ctl_el0: forall d, d {r_cntp_ctl_el0: (r_cntp_ctl_el0 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_cntp_cval_el0: forall d a b, d {r_cntp_cval_el0: a} {r_cntp_cval_el0: b} = d {r_cntp_cval_el0: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_cntp_cval_el0: forall d, d {r_cntp_cval_el0: (r_cntp_cval_el0 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_cntp_tval_el0: forall d a b, d {r_cntp_tval_el0: a} {r_cntp_tval_el0: b} = d {r_cntp_tval_el0: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_cntp_tval_el0: forall d, d {r_cntp_tval_el0: (r_cntp_tval_el0 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_cntv_ctl_el0: forall d a b, d {r_cntv_ctl_el0: a} {r_cntv_ctl_el0: b} = d {r_cntv_ctl_el0: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_cntv_ctl_el0: forall d, d {r_cntv_ctl_el0: (r_cntv_ctl_el0 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_cntv_cval_el0: forall d a b, d {r_cntv_cval_el0: a} {r_cntv_cval_el0: b} = d {r_cntv_cval_el0: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_cntv_cval_el0: forall d, d {r_cntv_cval_el0: (r_cntv_cval_el0 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_cntv_tval_el0: forall d a b, d {r_cntv_tval_el0: a} {r_cntv_tval_el0: b} = d {r_cntv_tval_el0: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_cntv_tval_el0: forall d, d {r_cntv_tval_el0: (r_cntv_tval_el0 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_sp_el0: forall d a b, d {r_sp_el0: a} {r_sp_el0: b} = d {r_sp_el0: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_sp_el0: forall d, d {r_sp_el0: (r_sp_el0 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_pmcr_el0: forall d a b, d {r_pmcr_el0: a} {r_pmcr_el0: b} = d {r_pmcr_el0: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_pmcr_el0: forall d, d {r_pmcr_el0: (r_pmcr_el0 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_pmuserenr_el0: forall d a b, d {r_pmuserenr_el0: a} {r_pmuserenr_el0: b} = d {r_pmuserenr_el0: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_pmuserenr_el0: forall d, d {r_pmuserenr_el0: (r_pmuserenr_el0 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_tpidrro_el0: forall d a b, d {r_tpidrro_el0: a} {r_tpidrro_el0: b} = d {r_tpidrro_el0: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_tpidrro_el0: forall d, d {r_tpidrro_el0: (r_tpidrro_el0 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_tpidr_el0: forall d a b, d {r_tpidr_el0: a} {r_tpidr_el0: b} = d {r_tpidr_el0: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_tpidr_el0: forall d, d {r_tpidr_el0: (r_tpidr_el0 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_sp_el1: forall d a b, d {r_sp_el1: a} {r_sp_el1: b} = d {r_sp_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_sp_el1: forall d, d {r_sp_el1: (r_sp_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_elr_el1: forall d a b, d {r_elr_el1: a} {r_elr_el1: b} = d {r_elr_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_elr_el1: forall d, d {r_elr_el1: (r_elr_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_spsr_el1: forall d a b, d {r_spsr_el1: a} {r_spsr_el1: b} = d {r_spsr_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_spsr_el1: forall d, d {r_spsr_el1: (r_spsr_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_csselr_el1: forall d a b, d {r_csselr_el1: a} {r_csselr_el1: b} = d {r_csselr_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_csselr_el1: forall d, d {r_csselr_el1: (r_csselr_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_sctlr_el1: forall d a b, d {r_sctlr_el1: a} {r_sctlr_el1: b} = d {r_sctlr_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_sctlr_el1: forall d, d {r_sctlr_el1: (r_sctlr_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_actlr_el1: forall d a b, d {r_actlr_el1: a} {r_actlr_el1: b} = d {r_actlr_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_actlr_el1: forall d, d {r_actlr_el1: (r_actlr_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_cpacr_el1: forall d a b, d {r_cpacr_el1: a} {r_cpacr_el1: b} = d {r_cpacr_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_cpacr_el1: forall d, d {r_cpacr_el1: (r_cpacr_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_zcr_el1: forall d a b, d {r_zcr_el1: a} {r_zcr_el1: b} = d {r_zcr_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_zcr_el1: forall d, d {r_zcr_el1: (r_zcr_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_ttbr0_el1: forall d a b, d {r_ttbr0_el1: a} {r_ttbr0_el1: b} = d {r_ttbr0_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_ttbr0_el1: forall d, d {r_ttbr0_el1: (r_ttbr0_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_ttbr1_el1: forall d a b, d {r_ttbr1_el1: a} {r_ttbr1_el1: b} = d {r_ttbr1_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_ttbr1_el1: forall d, d {r_ttbr1_el1: (r_ttbr1_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_tcr_el1: forall d a b, d {r_tcr_el1: a} {r_tcr_el1: b} = d {r_tcr_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_tcr_el1: forall d, d {r_tcr_el1: (r_tcr_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_esr_el1: forall d a b, d {r_esr_el1: a} {r_esr_el1: b} = d {r_esr_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_esr_el1: forall d, d {r_esr_el1: (r_esr_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_afsr0_el1: forall d a b, d {r_afsr0_el1: a} {r_afsr0_el1: b} = d {r_afsr0_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_afsr0_el1: forall d, d {r_afsr0_el1: (r_afsr0_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_afsr1_el1: forall d a b, d {r_afsr1_el1: a} {r_afsr1_el1: b} = d {r_afsr1_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_afsr1_el1: forall d, d {r_afsr1_el1: (r_afsr1_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_far_el1: forall d a b, d {r_far_el1: a} {r_far_el1: b} = d {r_far_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_far_el1: forall d, d {r_far_el1: (r_far_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_mair_el1: forall d a b, d {r_mair_el1: a} {r_mair_el1: b} = d {r_mair_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_mair_el1: forall d, d {r_mair_el1: (r_mair_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_vbar_el1: forall d a b, d {r_vbar_el1: a} {r_vbar_el1: b} = d {r_vbar_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_vbar_el1: forall d, d {r_vbar_el1: (r_vbar_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_contextidr_el1: forall d a b, d {r_contextidr_el1: a} {r_contextidr_el1: b} = d {r_contextidr_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_contextidr_el1: forall d, d {r_contextidr_el1: (r_contextidr_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_tpidr_el1: forall d a b, d {r_tpidr_el1: a} {r_tpidr_el1: b} = d {r_tpidr_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_tpidr_el1: forall d, d {r_tpidr_el1: (r_tpidr_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_amair_el1: forall d a b, d {r_amair_el1: a} {r_amair_el1: b} = d {r_amair_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_amair_el1: forall d, d {r_amair_el1: (r_amair_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_cntkctl_el1: forall d a b, d {r_cntkctl_el1: a} {r_cntkctl_el1: b} = d {r_cntkctl_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_cntkctl_el1: forall d, d {r_cntkctl_el1: (r_cntkctl_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_par_el1: forall d a b, d {r_par_el1: a} {r_par_el1: b} = d {r_par_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_par_el1: forall d, d {r_par_el1: (r_par_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_mdscr_el1: forall d a b, d {r_mdscr_el1: a} {r_mdscr_el1: b} = d {r_mdscr_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_mdscr_el1: forall d, d {r_mdscr_el1: (r_mdscr_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_mdccint_el1: forall d a b, d {r_mdccint_el1: a} {r_mdccint_el1: b} = d {r_mdccint_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_mdccint_el1: forall d, d {r_mdccint_el1: (r_mdccint_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_disr_el1: forall d a b, d {r_disr_el1: a} {r_disr_el1: b} = d {r_disr_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_disr_el1: forall d, d {r_disr_el1: (r_disr_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_mpam0_el1: forall d a b, d {r_mpam0_el1: a} {r_mpam0_el1: b} = d {r_mpam0_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_mpam0_el1: forall d, d {r_mpam0_el1: (r_mpam0_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_cnthctl_el2: forall d a b, d {r_cnthctl_el2: a} {r_cnthctl_el2: b} = d {r_cnthctl_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_cnthctl_el2: forall d, d {r_cnthctl_el2: (r_cnthctl_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_cntvoff_el2: forall d a b, d {r_cntvoff_el2: a} {r_cntvoff_el2: b} = d {r_cntvoff_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_cntvoff_el2: forall d, d {r_cntvoff_el2: (r_cntvoff_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_cntpoff_el2: forall d a b, d {r_cntpoff_el2: a} {r_cntpoff_el2: b} = d {r_cntpoff_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_cntpoff_el2: forall d, d {r_cntpoff_el2: (r_cntpoff_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_vmpidr_el2: forall d a b, d {r_vmpidr_el2: a} {r_vmpidr_el2: b} = d {r_vmpidr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_vmpidr_el2: forall d, d {r_vmpidr_el2: (r_vmpidr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_vttbr_el2: forall d a b, d {r_vttbr_el2: a} {r_vttbr_el2: b} = d {r_vttbr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_vttbr_el2: forall d, d {r_vttbr_el2: (r_vttbr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_vtcr_el2: forall d a b, d {r_vtcr_el2: a} {r_vtcr_el2: b} = d {r_vtcr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_vtcr_el2: forall d, d {r_vtcr_el2: (r_vtcr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_hcr_el2: forall d a b, d {r_hcr_el2: a} {r_hcr_el2: b} = d {r_hcr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_hcr_el2: forall d, d {r_hcr_el2: (r_hcr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_actlr_el2: forall d a b, d {r_actlr_el2: a} {r_actlr_el2: b} = d {r_actlr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_actlr_el2: forall d, d {r_actlr_el2: (r_actlr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_afsr0_el2: forall d a b, d {r_afsr0_el2: a} {r_afsr0_el2: b} = d {r_afsr0_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_afsr0_el2: forall d, d {r_afsr0_el2: (r_afsr0_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_afsr1_el2: forall d a b, d {r_afsr1_el2: a} {r_afsr1_el2: b} = d {r_afsr1_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_afsr1_el2: forall d, d {r_afsr1_el2: (r_afsr1_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_amair_el2: forall d a b, d {r_amair_el2: a} {r_amair_el2: b} = d {r_amair_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_amair_el2: forall d, d {r_amair_el2: (r_amair_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_cptr_el2: forall d a b, d {r_cptr_el2: a} {r_cptr_el2: b} = d {r_cptr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_cptr_el2: forall d, d {r_cptr_el2: (r_cptr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_elr_el2: forall d a b, d {r_elr_el2: a} {r_elr_el2: b} = d {r_elr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_elr_el2: forall d, d {r_elr_el2: (r_elr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_esr_el2: forall d a b, d {r_esr_el2: a} {r_esr_el2: b} = d {r_esr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_esr_el2: forall d, d {r_esr_el2: (r_esr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_far_el2: forall d a b, d {r_far_el2: a} {r_far_el2: b} = d {r_far_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_far_el2: forall d, d {r_far_el2: (r_far_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_hacr_el2: forall d a b, d {r_hacr_el2: a} {r_hacr_el2: b} = d {r_hacr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_hacr_el2: forall d, d {r_hacr_el2: (r_hacr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_hpfar_el2: forall d a b, d {r_hpfar_el2: a} {r_hpfar_el2: b} = d {r_hpfar_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_hpfar_el2: forall d, d {r_hpfar_el2: (r_hpfar_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_hstr_el2: forall d a b, d {r_hstr_el2: a} {r_hstr_el2: b} = d {r_hstr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_hstr_el2: forall d, d {r_hstr_el2: (r_hstr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_mair_el2: forall d a b, d {r_mair_el2: a} {r_mair_el2: b} = d {r_mair_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_mair_el2: forall d, d {r_mair_el2: (r_mair_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_mpam_el2: forall d a b, d {r_mpam_el2: a} {r_mpam_el2: b} = d {r_mpam_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_mpam_el2: forall d, d {r_mpam_el2: (r_mpam_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_mpamhcr_el2: forall d a b, d {r_mpamhcr_el2: a} {r_mpamhcr_el2: b} = d {r_mpamhcr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_mpamhcr_el2: forall d, d {r_mpamhcr_el2: (r_mpamhcr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_pmscr_el2: forall d a b, d {r_pmscr_el2: a} {r_pmscr_el2: b} = d {r_pmscr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_pmscr_el2: forall d, d {r_pmscr_el2: (r_pmscr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_sctlr_el2: forall d a b, d {r_sctlr_el2: a} {r_sctlr_el2: b} = d {r_sctlr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_sctlr_el2: forall d, d {r_sctlr_el2: (r_sctlr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_scxtnum_el2: forall d a b, d {r_scxtnum_el2: a} {r_scxtnum_el2: b} = d {r_scxtnum_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_scxtnum_el2: forall d, d {r_scxtnum_el2: (r_scxtnum_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_sp_el2: forall d a b, d {r_sp_el2: a} {r_sp_el2: b} = d {r_sp_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_sp_el2: forall d, d {r_sp_el2: (r_sp_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_spsr_el2: forall d a b, d {r_spsr_el2: a} {r_spsr_el2: b} = d {r_spsr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_spsr_el2: forall d, d {r_spsr_el2: (r_spsr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_tcr_el2: forall d a b, d {r_tcr_el2: a} {r_tcr_el2: b} = d {r_tcr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_tcr_el2: forall d, d {r_tcr_el2: (r_tcr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_tfsr_el2: forall d a b, d {r_tfsr_el2: a} {r_tfsr_el2: b} = d {r_tfsr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_tfsr_el2: forall d, d {r_tfsr_el2: (r_tfsr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_tpidr_el2: forall d a b, d {r_tpidr_el2: a} {r_tpidr_el2: b} = d {r_tpidr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_tpidr_el2: forall d, d {r_tpidr_el2: (r_tpidr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_trfcr_el2: forall d a b, d {r_trfcr_el2: a} {r_trfcr_el2: b} = d {r_trfcr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_trfcr_el2: forall d, d {r_trfcr_el2: (r_trfcr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_ttbr0_el2: forall d a b, d {r_ttbr0_el2: a} {r_ttbr0_el2: b} = d {r_ttbr0_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_ttbr0_el2: forall d, d {r_ttbr0_el2: (r_ttbr0_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_ttbr1_el2: forall d a b, d {r_ttbr1_el2: a} {r_ttbr1_el2: b} = d {r_ttbr1_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_ttbr1_el2: forall d, d {r_ttbr1_el2: (r_ttbr1_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_vbar_el2: forall d a b, d {r_vbar_el2: a} {r_vbar_el2: b} = d {r_vbar_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_vbar_el2: forall d, d {r_vbar_el2: (r_vbar_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_vdisr_el2: forall d a b, d {r_vdisr_el2: a} {r_vdisr_el2: b} = d {r_vdisr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_vdisr_el2: forall d, d {r_vdisr_el2: (r_vdisr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_vncr_el2: forall d a b, d {r_vncr_el2: a} {r_vncr_el2: b} = d {r_vncr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_vncr_el2: forall d, d {r_vncr_el2: (r_vncr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_vpidr_el2: forall d a b, d {r_vpidr_el2: a} {r_vpidr_el2: b} = d {r_vpidr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_vpidr_el2: forall d, d {r_vpidr_el2: (r_vpidr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_vsesr_el2: forall d a b, d {r_vsesr_el2: a} {r_vsesr_el2: b} = d {r_vsesr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_vsesr_el2: forall d, d {r_vsesr_el2: (r_vsesr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_vstcr_el2: forall d a b, d {r_vstcr_el2: a} {r_vstcr_el2: b} = d {r_vstcr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_vstcr_el2: forall d, d {r_vstcr_el2: (r_vstcr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_vsttbr_el2: forall d a b, d {r_vsttbr_el2: a} {r_vsttbr_el2: b} = d {r_vsttbr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_vsttbr_el2: forall d, d {r_vsttbr_el2: (r_vsttbr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_zcr_el2: forall d a b, d {r_zcr_el2: a} {r_zcr_el2: b} = d {r_zcr_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_zcr_el2: forall d, d {r_zcr_el2: (r_zcr_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_icc_sre_el2: forall d a b, d {r_icc_sre_el2: a} {r_icc_sre_el2: b} = d {r_icc_sre_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_icc_sre_el2: forall d, d {r_icc_sre_el2: (r_icc_sre_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_icc_hppir1_el1: forall d a b, d {r_icc_hppir1_el1: a} {r_icc_hppir1_el1: b} = d {r_icc_hppir1_el1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_icc_hppir1_el1: forall d, d {r_icc_hppir1_el1: (r_icc_hppir1_el1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_spsr_el3: forall d a b, d {r_spsr_el3: a} {r_spsr_el3: b} = d {r_spsr_el3: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_spsr_el3: forall d, d {r_spsr_el3: (r_spsr_el3 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_elr_el3: forall d a b, d {r_elr_el3: a} {r_elr_el3: b} = d {r_elr_el3: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_elr_el3: forall d, d {r_elr_el3: (r_elr_el3 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_esr_el3: forall d a b, d {r_esr_el3: a} {r_esr_el3: b} = d {r_esr_el3: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_esr_el3: forall d, d {r_esr_el3: (r_esr_el3 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_scr_el3: forall d a b, d {r_scr_el3: a} {r_scr_el3: b} = d {r_scr_el3: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_scr_el3: forall d, d {r_scr_el3: (r_scr_el3 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_tpidr_el3: forall d a b, d {r_tpidr_el3: a} {r_tpidr_el3: b} = d {r_tpidr_el3: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_tpidr_el3: forall d, d {r_tpidr_el3: (r_tpidr_el3 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_a_CN: forall d a b, d {a_CN: a} {a_CN: b} = d {a_CN: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_a_CN: forall d, d {a_CN: (a_CN d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_a_CZ: forall d a b, d {a_CZ: a} {a_CZ: b} = d {a_CZ: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_a_CZ: forall d, d {a_CZ: (a_CZ d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_a_CC: forall d a b, d {a_CC: a} {a_CC: b} = d {a_CC: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_a_CC: forall d, d {a_CC: (a_CC d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_a_CV: forall d a b, d {a_CV: a} {a_CV: b} = d {a_CV: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_a_CV: forall d, d {a_CV: (a_CV d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_a_DAIFCLR: forall d a b, d {a_DAIFCLR: a} {a_DAIFCLR: b} = d {a_DAIFCLR: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_a_DAIFCLR: forall d, d {a_DAIFCLR: (a_DAIFCLR d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_a_SP: forall d a b, d {a_SP: a} {a_SP: b} = d {a_SP: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_a_SP: forall d, d {a_SP: (a_SP d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_a_PC: forall d a b, d {a_PC: a} {a_PC: b} = d {a_PC: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_a_PC: forall d, d {a_PC: (a_PC d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_a_EL3: forall d a b, d {a_EL3: a} {a_EL3: b} = d {a_EL3: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_a_EL3: forall d, d {a_EL3: (a_EL3 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_t_masked: forall d a b, d {t_masked: a} {t_masked: b} = d {t_masked: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_t_masked: forall d, d {t_masked: (t_masked d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_t_asserted: forall d a b, d {t_asserted: a} {t_asserted: b} = d {t_asserted: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_t_asserted: forall d, d {t_asserted: (t_asserted d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_tag: forall d a b, d {g_tag: a} {g_tag: b} = d {g_tag: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_tag: forall d, d {g_tag: (g_tag d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_refcount: forall d a b, d {g_refcount: a} {g_refcount: b} = d {g_refcount: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_refcount: forall d, d {g_refcount: (g_refcount d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_rd: forall d a b, d {g_rd: a} {g_rd: b} = d {g_rd: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_rd: forall d, d {g_rd: (g_rd d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_map_addr: forall d a b, d {g_map_addr: a} {g_map_addr: b} = d {g_map_addr: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_map_addr: forall d, d {g_map_addr: (g_map_addr d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_rvic_enabled: forall d a b, d {r_rvic_enabled: a} {r_rvic_enabled: b} = d {r_rvic_enabled: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_rvic_enabled: forall d, d {r_rvic_enabled: (r_rvic_enabled d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_mask_bits: forall d a b, d {r_mask_bits: a} {r_mask_bits: b} = d {r_mask_bits: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_mask_bits: forall d, d {r_mask_bits: (r_mask_bits d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_r_pending_bits: forall d a b, d {r_pending_bits: a} {r_pending_bits: b} = d {r_pending_bits: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_r_pending_bits: forall d, d {r_pending_bits: (r_pending_bits d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_data: forall d a b, d {g_data: a} {g_data: b} = d {g_data: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_data: forall d, d {g_data: (g_data d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_realm_state: forall d a b, d {g_realm_state: a} {g_realm_state: b} = d {g_realm_state: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_realm_state: forall d, d {g_realm_state: (g_realm_state d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_par_base: forall d a b, d {g_par_base: a} {g_par_base: b} = d {g_par_base: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_par_base: forall d, d {g_par_base: (g_par_base d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_par_end: forall d a b, d {g_par_end: a} {g_par_end: b} = d {g_par_end: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_par_end: forall d, d {g_par_end: (g_par_end d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_rec_list: forall d a b, d {g_rec_list: a} {g_rec_list: b} = d {g_rec_list: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_rec_list: forall d, d {g_rec_list: (g_rec_list d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_rtt: forall d a b, d {g_rtt: a} {g_rtt: b} = d {g_rtt: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_rtt: forall d, d {g_rtt: (g_rtt d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_measurement_algo: forall d a b, d {g_measurement_algo: a} {g_measurement_algo: b} = d {g_measurement_algo: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_measurement_algo: forall d, d {g_measurement_algo: (g_measurement_algo d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_measurement_ctx: forall d a b, d {g_measurement_ctx: a} {g_measurement_ctx: b} = d {g_measurement_ctx: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_measurement_ctx: forall d, d {g_measurement_ctx: (g_measurement_ctx d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_measurement: forall d a b, d {g_measurement: a} {g_measurement: b} = d {g_measurement: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_measurement: forall d, d {g_measurement: (g_measurement d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_recs: forall d a b, d {g_recs: a} {g_recs: b} = d {g_recs: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_recs: forall d, d {g_recs: (g_recs d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_rvic: forall d a b, d {g_rvic: a} {g_rvic: b} = d {g_rvic: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_rvic: forall d, d {g_rvic: (g_rvic d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_runnable: forall d a b, d {g_runnable: a} {g_runnable: b} = d {g_runnable: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_runnable: forall d, d {g_runnable: (g_runnable d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_regs: forall d a b, d {g_regs: a} {g_regs: b} = d {g_regs: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_regs: forall d, d {g_regs: (g_regs d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_pc: forall d a b, d {g_pc: a} {g_pc: b} = d {g_pc: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_pc: forall d, d {g_pc: (g_pc d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_pstate: forall d a b, d {g_pstate: a} {g_pstate: b} = d {g_pstate: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_pstate: forall d, d {g_pstate: (g_pstate d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_vtimer: forall d a b, d {g_vtimer: a} {g_vtimer: b} = d {g_vtimer: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_vtimer: forall d, d {g_vtimer: (g_vtimer d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_ptimer: forall d a b, d {g_ptimer: a} {g_ptimer: b} = d {g_ptimer: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_ptimer: forall d, d {g_ptimer: (g_ptimer d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_dispose_pending: forall d a b, d {g_dispose_pending: a} {g_dispose_pending: b} = d {g_dispose_pending: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_dispose_pending: forall d, d {g_dispose_pending: (g_dispose_pending d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_dispose_addr: forall d a b, d {g_dispose_addr: a} {g_dispose_addr: b} = d {g_dispose_addr: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_dispose_addr: forall d, d {g_dispose_addr: (g_dispose_addr d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_dispose_size: forall d a b, d {g_dispose_size: a} {g_dispose_size: b} = d {g_dispose_size: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_dispose_size: forall d, d {g_dispose_size: (g_dispose_size d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_rec_rd: forall d a b, d {g_rec_rd: a} {g_rec_rd: b} = d {g_rec_rd: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_rec_rd: forall d, d {g_rec_rd: (g_rec_rd d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_rec_par_base: forall d a b, d {g_rec_par_base: a} {g_rec_par_base: b} = d {g_rec_par_base: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_rec_par_base: forall d, d {g_rec_par_base: (g_rec_par_base d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_rec_par_end: forall d a b, d {g_rec_par_end: a} {g_rec_par_end: b} = d {g_rec_par_end: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_rec_par_end: forall d, d {g_rec_par_end: (g_rec_par_end d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_rec_rec_list: forall d a b, d {g_rec_rec_list: a} {g_rec_rec_list: b} = d {g_rec_rec_list: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_rec_rec_list: forall d, d {g_rec_rec_list: (g_rec_rec_list d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_esr: forall d a b, d {g_esr: a} {g_esr: b} = d {g_esr: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_esr: forall d, d {g_esr: (g_esr d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_running: forall d a b, d {g_running: a} {g_running: b} = d {g_running: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_running: forall d, d {g_running: (g_running d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_inited: forall d a b, d {g_inited: a} {g_inited: b} = d {g_inited: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_inited: forall d, d {g_inited: (g_inited d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_rec: forall d a b, d {g_rec: a} {g_rec: b} = d {g_rec: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_rec: forall d, d {g_rec: (g_rec d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_g_rec_idx: forall d a b, d {g_rec_idx: a} {g_rec_idx: b} = d {g_rec_idx: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_g_rec_idx: forall d, d {g_rec_idx: (g_rec_idx d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_tbl_level: forall d a b, d {tbl_level: a} {tbl_level: b} = d {tbl_level: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_tbl_level: forall d, d {tbl_level: (tbl_level d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_tbl_parent: forall d a b, d {tbl_parent: a} {tbl_parent: b} = d {tbl_parent: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_tbl_parent: forall d, d {tbl_parent: (tbl_parent d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_glock: forall d a b, d {glock: a} {glock: b} = d {glock: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_glock: forall d, d {glock: (glock d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_gref: forall d a b, d {gref: a} {gref: b} = d {gref: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_gref: forall d, d {gref: (gref d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_gtype: forall d a b, d {gtype: a} {gtype: b} = d {gtype: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_gtype: forall d, d {gtype: (gtype d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_gcnt: forall d a b, d {gcnt: a} {gcnt: b} = d {gcnt: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_gcnt: forall d, d {gcnt: (gcnt d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_ginfo: forall d a b, d {ginfo: a} {ginfo: b} = d {ginfo: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_ginfo: forall d, d {ginfo: (ginfo d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_gnorm: forall d a b, d {gnorm: a} {gnorm: b} = d {gnorm: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_gnorm: forall d, d {gnorm: (gnorm d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_grec: forall d a b, d {grec: a} {grec: b} = d {grec: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_grec: forall d, d {grec: (grec d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_gro: forall d a b, d {gro: a} {gro: b} = d {gro: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_gro: forall d, d {gro: (gro d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_gaux: forall d a b, d {gaux: a} {gaux: b} = d {gaux: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_gaux: forall d, d {gaux: (gaux d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_cpu_regs: forall d a b, d {cpu_regs: a} {cpu_regs: b} = d {cpu_regs: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_cpu_regs: forall d, d {cpu_regs: (cpu_regs d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_asm_regs: forall d a b, d {asm_regs: a} {asm_regs: b} = d {asm_regs: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_asm_regs: forall d, d {asm_regs: (asm_regs d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_id_regs: forall d a b, d {id_regs: a} {id_regs: b} = d {id_regs: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_id_regs: forall d, d {id_regs: (id_regs d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_buffer: forall d a b, d {buffer: a} {buffer: b} = d {buffer: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_buffer: forall d, d {buffer: (buffer d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_ns_regs_el2: forall d a b, d {ns_regs_el2: a} {ns_regs_el2: b} = d {ns_regs_el2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_ns_regs_el2: forall d, d {ns_regs_el2: (ns_regs_el2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_realm_params: forall d a b, d {realm_params: a} {realm_params: b} = d {realm_params: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_realm_params: forall d, d {realm_params: (realm_params d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_rec_params: forall d a b, d {rec_params: a} {rec_params: b} = d {rec_params: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_rec_params: forall d, d {rec_params: (rec_params d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_rec_run: forall d a b, d {rec_run: a} {rec_run: b} = d {rec_run: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_rec_run: forall d, d {rec_run: (rec_run d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_retval: forall d a b, d {retval: a} {retval: b} = d {retval: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_retval: forall d, d {retval: (retval d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_locked_g: forall d a b, d {locked_g: a} {locked_g: b} = d {locked_g: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_locked_g: forall d, d {locked_g: (locked_g d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_wi_last_level: forall d a b, d {wi_last_level: a} {wi_last_level: b} = d {wi_last_level: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_wi_last_level: forall d, d {wi_last_level: (wi_last_level d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_wi_llt: forall d a b, d {wi_llt: a} {wi_llt: b} = d {wi_llt: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_wi_llt: forall d, d {wi_llt: (wi_llt d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_wi_index: forall d a b, d {wi_index: a} {wi_index: b} = d {wi_index: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_wi_index: forall d, d {wi_index: (wi_index d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_rvic_x0: forall d a b, d {rvic_x0: a} {rvic_x0: b} = d {rvic_x0: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_rvic_x0: forall d, d {rvic_x0: (rvic_x0 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_rvic_x1: forall d a b, d {rvic_x1: a} {rvic_x1: b} = d {rvic_x1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_rvic_x1: forall d, d {rvic_x1: (rvic_x1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_rvic_x2: forall d a b, d {rvic_x2: a} {rvic_x2: b} = d {rvic_x2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_rvic_x2: forall d, d {rvic_x2: (rvic_x2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_rvic_x3: forall d a b, d {rvic_x3: a} {rvic_x3: b} = d {rvic_x3: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_rvic_x3: forall d, d {rvic_x3: (rvic_x3 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_rvic_target: forall d a b, d {rvic_target: a} {rvic_target: b} = d {rvic_target: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_rvic_target: forall d, d {rvic_target: (rvic_target d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_rvic_ns_notify: forall d a b, d {rvic_ns_notify: a} {rvic_ns_notify: b} = d {rvic_ns_notify: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_rvic_ns_notify: forall d, d {rvic_ns_notify: (rvic_ns_notify d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_psci_x0: forall d a b, d {psci_x0: a} {psci_x0: b} = d {psci_x0: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_psci_x0: forall d, d {psci_x0: (psci_x0 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_psci_x1: forall d a b, d {psci_x1: a} {psci_x1: b} = d {psci_x1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_psci_x1: forall d, d {psci_x1: (psci_x1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_psci_x2: forall d a b, d {psci_x2: a} {psci_x2: b} = d {psci_x2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_psci_x2: forall d, d {psci_x2: (psci_x2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_psci_x3: forall d a b, d {psci_x3: a} {psci_x3: b} = d {psci_x3: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_psci_x3: forall d, d {psci_x3: (psci_x3 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {psci_forward_x0: b} = d {psci_forward_x0: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_psci_forward_x0: forall d, d {psci_forward_x0: (psci_forward_x0 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {psci_forward_x1: b} = d {psci_forward_x1: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_psci_forward_x1: forall d, d {psci_forward_x1: (psci_forward_x1 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {psci_forward_x2: b} = d {psci_forward_x2: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_psci_forward_x2: forall d, d {psci_forward_x2: (psci_forward_x2 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {psci_forward_x3: b} = d {psci_forward_x3: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_psci_forward_x3: forall d, d {psci_forward_x3: (psci_forward_x3 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {psci_forward_psci_call: b} = d {psci_forward_psci_call: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_psci_forward_psci_call: forall d, d {psci_forward_psci_call: (psci_forward_psci_call d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_target_rec: forall d a b, d {target_rec: a} {target_rec: b} = d {target_rec: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_target_rec: forall d, d {target_rec: (target_rec d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_el2_stack: forall d a b, d {el2_stack: a} {el2_stack: b} = d {el2_stack: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_el2_stack: forall d, d {el2_stack: (el2_stack d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_el3_stack: forall d a b, d {el3_stack: a} {el3_stack: b} = d {el3_stack: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_el3_stack: forall d, d {el3_stack: (el3_stack d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {ns_regs_el3: b} = d {ns_regs_el3: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_ns_regs_el3: forall d, d {ns_regs_el3: (ns_regs_el3 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {realm_regs_el3: b} = d {realm_regs_el3: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_realm_regs_el3: forall d, d {realm_regs_el3: (realm_regs_el3 d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_cur_rec: forall d a b, d {cur_rec: a} {cur_rec: b} = d {cur_rec: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_cur_rec: forall d, d {cur_rec: (cur_rec d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_mstage: forall d a b, d {mstage: a} {mstage: b} = d {mstage: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_mstage: forall d, d {mstage: (mstage d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_trap_reason: forall d a b, d {trap_reason: a} {trap_reason: b} = d {trap_reason: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_trap_reason: forall d, d {trap_reason: (trap_reason d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_sec_mem: forall d a b, d {sec_mem: a} {sec_mem: b} = d {sec_mem: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_sec_mem: forall d, d {sec_mem: (sec_mem d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_sec_regs: forall d a b, d {sec_regs: a} {sec_regs: b} = d {sec_regs: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_sec_regs: forall d, d {sec_regs: (sec_regs d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_decl_regs: forall d a b, d {decl_regs: a} {decl_regs: b} = d {decl_regs: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_decl_regs: forall d, d {decl_regs: (decl_regs d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_gs: forall d a b, d {gs: a} {gs: b} = d {gs: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_gs: forall d, d {gs: (gs d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_gpt: forall d a b, d {gpt: a} {gpt: b} = d {gpt: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_gpt: forall d, d {gpt: (gpt d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_gpt_lk: forall d a b, d {gpt_lk: a} {gpt_lk: b} = d {gpt_lk: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_gpt_lk: forall d, d {gpt_lk: (gpt_lk d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_tlbs: forall d a b, d {tlbs: a} {tlbs: b} = d {tlbs: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_tlbs: forall d, d {tlbs: (tlbs d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_rtts: forall d a b, d {rtts: a} {rtts: b} = d {rtts: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_rtts: forall d, d {rtts: (rtts d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_realms: forall d a b, d {realms: a} {realms: b} = d {realms: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_realms: forall d, d {realms: (realms d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_log: forall d a b, d {log: a} {log: b} = d {log: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_log: forall d, d {log: (log d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_oracle: forall d a b, d {oracle: a} {oracle: b} = d {oracle: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_oracle: forall d, d {oracle: (oracle d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_repl: forall d a b, d {repl: a} {repl: b} = d {repl: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_repl: forall d, d {repl: (repl d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_share: forall d a b, d {share: a} {share: b} = d {share: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_share: forall d, d {share: (share d)} = d. Proof. destruct d; reflexivity. Qed.
Lemma double_update_priv: forall d a b, d {priv: a} {priv: b} = d {priv: b}. Proof. intros; reflexivity. Qed.
Lemma self_update_priv: forall d, d {priv: (priv d)} = d. Proof. destruct d; reflexivity. Qed.

Ltac simpl_field :=
match goal with
| [|- context[?d {r_x0: ?a} {r_x0: ?b}]] => rewrite (double_update_r_x0 d a b)
| [|- context[?d {r_x0: (r_x0 ?d)}]] => rewrite (self_update_r_x0 d)
| [|- context[?d {r_x1: ?a} {r_x1: ?b}]] => rewrite (double_update_r_x1 d a b)
| [|- context[?d {r_x1: (r_x1 ?d)}]] => rewrite (self_update_r_x1 d)
| [|- context[?d {r_x2: ?a} {r_x2: ?b}]] => rewrite (double_update_r_x2 d a b)
| [|- context[?d {r_x2: (r_x2 ?d)}]] => rewrite (self_update_r_x2 d)
| [|- context[?d {r_x3: ?a} {r_x3: ?b}]] => rewrite (double_update_r_x3 d a b)
| [|- context[?d {r_x3: (r_x3 ?d)}]] => rewrite (self_update_r_x3 d)
| [|- context[?d {r_x4: ?a} {r_x4: ?b}]] => rewrite (double_update_r_x4 d a b)
| [|- context[?d {r_x4: (r_x4 ?d)}]] => rewrite (self_update_r_x4 d)
| [|- context[?d {r_x5: ?a} {r_x5: ?b}]] => rewrite (double_update_r_x5 d a b)
| [|- context[?d {r_x5: (r_x5 ?d)}]] => rewrite (self_update_r_x5 d)
| [|- context[?d {r_x6: ?a} {r_x6: ?b}]] => rewrite (double_update_r_x6 d a b)
| [|- context[?d {r_x6: (r_x6 ?d)}]] => rewrite (self_update_r_x6 d)
| [|- context[?d {r_x7: ?a} {r_x7: ?b}]] => rewrite (double_update_r_x7 d a b)
| [|- context[?d {r_x7: (r_x7 ?d)}]] => rewrite (self_update_r_x7 d)
| [|- context[?d {r_x8: ?a} {r_x8: ?b}]] => rewrite (double_update_r_x8 d a b)
| [|- context[?d {r_x8: (r_x8 ?d)}]] => rewrite (self_update_r_x8 d)
| [|- context[?d {r_x9: ?a} {r_x9: ?b}]] => rewrite (double_update_r_x9 d a b)
| [|- context[?d {r_x9: (r_x9 ?d)}]] => rewrite (self_update_r_x9 d)
| [|- context[?d {r_x10: ?a} {r_x10: ?b}]] => rewrite (double_update_r_x10 d a b)
| [|- context[?d {r_x10: (r_x10 ?d)}]] => rewrite (self_update_r_x10 d)
| [|- context[?d {r_x11: ?a} {r_x11: ?b}]] => rewrite (double_update_r_x11 d a b)
| [|- context[?d {r_x11: (r_x11 ?d)}]] => rewrite (self_update_r_x11 d)
| [|- context[?d {r_x12: ?a} {r_x12: ?b}]] => rewrite (double_update_r_x12 d a b)
| [|- context[?d {r_x12: (r_x12 ?d)}]] => rewrite (self_update_r_x12 d)
| [|- context[?d {r_x13: ?a} {r_x13: ?b}]] => rewrite (double_update_r_x13 d a b)
| [|- context[?d {r_x13: (r_x13 ?d)}]] => rewrite (self_update_r_x13 d)
| [|- context[?d {r_x14: ?a} {r_x14: ?b}]] => rewrite (double_update_r_x14 d a b)
| [|- context[?d {r_x14: (r_x14 ?d)}]] => rewrite (self_update_r_x14 d)
| [|- context[?d {r_x15: ?a} {r_x15: ?b}]] => rewrite (double_update_r_x15 d a b)
| [|- context[?d {r_x15: (r_x15 ?d)}]] => rewrite (self_update_r_x15 d)
| [|- context[?d {r_x16: ?a} {r_x16: ?b}]] => rewrite (double_update_r_x16 d a b)
| [|- context[?d {r_x16: (r_x16 ?d)}]] => rewrite (self_update_r_x16 d)
| [|- context[?d {r_x17: ?a} {r_x17: ?b}]] => rewrite (double_update_r_x17 d a b)
| [|- context[?d {r_x17: (r_x17 ?d)}]] => rewrite (self_update_r_x17 d)
| [|- context[?d {r_x18: ?a} {r_x18: ?b}]] => rewrite (double_update_r_x18 d a b)
| [|- context[?d {r_x18: (r_x18 ?d)}]] => rewrite (self_update_r_x18 d)
| [|- context[?d {r_x19: ?a} {r_x19: ?b}]] => rewrite (double_update_r_x19 d a b)
| [|- context[?d {r_x19: (r_x19 ?d)}]] => rewrite (self_update_r_x19 d)
| [|- context[?d {r_x20: ?a} {r_x20: ?b}]] => rewrite (double_update_r_x20 d a b)
| [|- context[?d {r_x20: (r_x20 ?d)}]] => rewrite (self_update_r_x20 d)
| [|- context[?d {r_x21: ?a} {r_x21: ?b}]] => rewrite (double_update_r_x21 d a b)
| [|- context[?d {r_x21: (r_x21 ?d)}]] => rewrite (self_update_r_x21 d)
| [|- context[?d {r_x22: ?a} {r_x22: ?b}]] => rewrite (double_update_r_x22 d a b)
| [|- context[?d {r_x22: (r_x22 ?d)}]] => rewrite (self_update_r_x22 d)
| [|- context[?d {r_x23: ?a} {r_x23: ?b}]] => rewrite (double_update_r_x23 d a b)
| [|- context[?d {r_x23: (r_x23 ?d)}]] => rewrite (self_update_r_x23 d)
| [|- context[?d {r_x24: ?a} {r_x24: ?b}]] => rewrite (double_update_r_x24 d a b)
| [|- context[?d {r_x24: (r_x24 ?d)}]] => rewrite (self_update_r_x24 d)
| [|- context[?d {r_x25: ?a} {r_x25: ?b}]] => rewrite (double_update_r_x25 d a b)
| [|- context[?d {r_x25: (r_x25 ?d)}]] => rewrite (self_update_r_x25 d)
| [|- context[?d {r_x26: ?a} {r_x26: ?b}]] => rewrite (double_update_r_x26 d a b)
| [|- context[?d {r_x26: (r_x26 ?d)}]] => rewrite (self_update_r_x26 d)
| [|- context[?d {r_x27: ?a} {r_x27: ?b}]] => rewrite (double_update_r_x27 d a b)
| [|- context[?d {r_x27: (r_x27 ?d)}]] => rewrite (self_update_r_x27 d)
| [|- context[?d {r_x28: ?a} {r_x28: ?b}]] => rewrite (double_update_r_x28 d a b)
| [|- context[?d {r_x28: (r_x28 ?d)}]] => rewrite (self_update_r_x28 d)
| [|- context[?d {r_x29: ?a} {r_x29: ?b}]] => rewrite (double_update_r_x29 d a b)
| [|- context[?d {r_x29: (r_x29 ?d)}]] => rewrite (self_update_r_x29 d)
| [|- context[?d {r_x30: ?a} {r_x30: ?b}]] => rewrite (double_update_r_x30 d a b)
| [|- context[?d {r_x30: (r_x30 ?d)}]] => rewrite (self_update_r_x30 d)
| [|- context[?d {r_lr: ?a} {r_lr: ?b}]] => rewrite (double_update_r_lr d a b)
| [|- context[?d {r_lr: (r_lr ?d)}]] => rewrite (self_update_r_lr d)
| [|- context[?d {r_cntp_ctl_el0: ?a} {r_cntp_ctl_el0: ?b}]] => rewrite (double_update_r_cntp_ctl_el0 d a b)
| [|- context[?d {r_cntp_ctl_el0: (r_cntp_ctl_el0 ?d)}]] => rewrite (self_update_r_cntp_ctl_el0 d)
| [|- context[?d {r_cntp_cval_el0: ?a} {r_cntp_cval_el0: ?b}]] => rewrite (double_update_r_cntp_cval_el0 d a b)
| [|- context[?d {r_cntp_cval_el0: (r_cntp_cval_el0 ?d)}]] => rewrite (self_update_r_cntp_cval_el0 d)
| [|- context[?d {r_cntp_tval_el0: ?a} {r_cntp_tval_el0: ?b}]] => rewrite (double_update_r_cntp_tval_el0 d a b)
| [|- context[?d {r_cntp_tval_el0: (r_cntp_tval_el0 ?d)}]] => rewrite (self_update_r_cntp_tval_el0 d)
| [|- context[?d {r_cntv_ctl_el0: ?a} {r_cntv_ctl_el0: ?b}]] => rewrite (double_update_r_cntv_ctl_el0 d a b)
| [|- context[?d {r_cntv_ctl_el0: (r_cntv_ctl_el0 ?d)}]] => rewrite (self_update_r_cntv_ctl_el0 d)
| [|- context[?d {r_cntv_cval_el0: ?a} {r_cntv_cval_el0: ?b}]] => rewrite (double_update_r_cntv_cval_el0 d a b)
| [|- context[?d {r_cntv_cval_el0: (r_cntv_cval_el0 ?d)}]] => rewrite (self_update_r_cntv_cval_el0 d)
| [|- context[?d {r_cntv_tval_el0: ?a} {r_cntv_tval_el0: ?b}]] => rewrite (double_update_r_cntv_tval_el0 d a b)
| [|- context[?d {r_cntv_tval_el0: (r_cntv_tval_el0 ?d)}]] => rewrite (self_update_r_cntv_tval_el0 d)
| [|- context[?d {r_sp_el0: ?a} {r_sp_el0: ?b}]] => rewrite (double_update_r_sp_el0 d a b)
| [|- context[?d {r_sp_el0: (r_sp_el0 ?d)}]] => rewrite (self_update_r_sp_el0 d)
| [|- context[?d {r_pmcr_el0: ?a} {r_pmcr_el0: ?b}]] => rewrite (double_update_r_pmcr_el0 d a b)
| [|- context[?d {r_pmcr_el0: (r_pmcr_el0 ?d)}]] => rewrite (self_update_r_pmcr_el0 d)
| [|- context[?d {r_pmuserenr_el0: ?a} {r_pmuserenr_el0: ?b}]] => rewrite (double_update_r_pmuserenr_el0 d a b)
| [|- context[?d {r_pmuserenr_el0: (r_pmuserenr_el0 ?d)}]] => rewrite (self_update_r_pmuserenr_el0 d)
| [|- context[?d {r_tpidrro_el0: ?a} {r_tpidrro_el0: ?b}]] => rewrite (double_update_r_tpidrro_el0 d a b)
| [|- context[?d {r_tpidrro_el0: (r_tpidrro_el0 ?d)}]] => rewrite (self_update_r_tpidrro_el0 d)
| [|- context[?d {r_tpidr_el0: ?a} {r_tpidr_el0: ?b}]] => rewrite (double_update_r_tpidr_el0 d a b)
| [|- context[?d {r_tpidr_el0: (r_tpidr_el0 ?d)}]] => rewrite (self_update_r_tpidr_el0 d)
| [|- context[?d {r_sp_el1: ?a} {r_sp_el1: ?b}]] => rewrite (double_update_r_sp_el1 d a b)
| [|- context[?d {r_sp_el1: (r_sp_el1 ?d)}]] => rewrite (self_update_r_sp_el1 d)
| [|- context[?d {r_elr_el1: ?a} {r_elr_el1: ?b}]] => rewrite (double_update_r_elr_el1 d a b)
| [|- context[?d {r_elr_el1: (r_elr_el1 ?d)}]] => rewrite (self_update_r_elr_el1 d)
| [|- context[?d {r_spsr_el1: ?a} {r_spsr_el1: ?b}]] => rewrite (double_update_r_spsr_el1 d a b)
| [|- context[?d {r_spsr_el1: (r_spsr_el1 ?d)}]] => rewrite (self_update_r_spsr_el1 d)
| [|- context[?d {r_csselr_el1: ?a} {r_csselr_el1: ?b}]] => rewrite (double_update_r_csselr_el1 d a b)
| [|- context[?d {r_csselr_el1: (r_csselr_el1 ?d)}]] => rewrite (self_update_r_csselr_el1 d)
| [|- context[?d {r_sctlr_el1: ?a} {r_sctlr_el1: ?b}]] => rewrite (double_update_r_sctlr_el1 d a b)
| [|- context[?d {r_sctlr_el1: (r_sctlr_el1 ?d)}]] => rewrite (self_update_r_sctlr_el1 d)
| [|- context[?d {r_actlr_el1: ?a} {r_actlr_el1: ?b}]] => rewrite (double_update_r_actlr_el1 d a b)
| [|- context[?d {r_actlr_el1: (r_actlr_el1 ?d)}]] => rewrite (self_update_r_actlr_el1 d)
| [|- context[?d {r_cpacr_el1: ?a} {r_cpacr_el1: ?b}]] => rewrite (double_update_r_cpacr_el1 d a b)
| [|- context[?d {r_cpacr_el1: (r_cpacr_el1 ?d)}]] => rewrite (self_update_r_cpacr_el1 d)
| [|- context[?d {r_zcr_el1: ?a} {r_zcr_el1: ?b}]] => rewrite (double_update_r_zcr_el1 d a b)
| [|- context[?d {r_zcr_el1: (r_zcr_el1 ?d)}]] => rewrite (self_update_r_zcr_el1 d)
| [|- context[?d {r_ttbr0_el1: ?a} {r_ttbr0_el1: ?b}]] => rewrite (double_update_r_ttbr0_el1 d a b)
| [|- context[?d {r_ttbr0_el1: (r_ttbr0_el1 ?d)}]] => rewrite (self_update_r_ttbr0_el1 d)
| [|- context[?d {r_ttbr1_el1: ?a} {r_ttbr1_el1: ?b}]] => rewrite (double_update_r_ttbr1_el1 d a b)
| [|- context[?d {r_ttbr1_el1: (r_ttbr1_el1 ?d)}]] => rewrite (self_update_r_ttbr1_el1 d)
| [|- context[?d {r_tcr_el1: ?a} {r_tcr_el1: ?b}]] => rewrite (double_update_r_tcr_el1 d a b)
| [|- context[?d {r_tcr_el1: (r_tcr_el1 ?d)}]] => rewrite (self_update_r_tcr_el1 d)
| [|- context[?d {r_esr_el1: ?a} {r_esr_el1: ?b}]] => rewrite (double_update_r_esr_el1 d a b)
| [|- context[?d {r_esr_el1: (r_esr_el1 ?d)}]] => rewrite (self_update_r_esr_el1 d)
| [|- context[?d {r_afsr0_el1: ?a} {r_afsr0_el1: ?b}]] => rewrite (double_update_r_afsr0_el1 d a b)
| [|- context[?d {r_afsr0_el1: (r_afsr0_el1 ?d)}]] => rewrite (self_update_r_afsr0_el1 d)
| [|- context[?d {r_afsr1_el1: ?a} {r_afsr1_el1: ?b}]] => rewrite (double_update_r_afsr1_el1 d a b)
| [|- context[?d {r_afsr1_el1: (r_afsr1_el1 ?d)}]] => rewrite (self_update_r_afsr1_el1 d)
| [|- context[?d {r_far_el1: ?a} {r_far_el1: ?b}]] => rewrite (double_update_r_far_el1 d a b)
| [|- context[?d {r_far_el1: (r_far_el1 ?d)}]] => rewrite (self_update_r_far_el1 d)
| [|- context[?d {r_mair_el1: ?a} {r_mair_el1: ?b}]] => rewrite (double_update_r_mair_el1 d a b)
| [|- context[?d {r_mair_el1: (r_mair_el1 ?d)}]] => rewrite (self_update_r_mair_el1 d)
| [|- context[?d {r_vbar_el1: ?a} {r_vbar_el1: ?b}]] => rewrite (double_update_r_vbar_el1 d a b)
| [|- context[?d {r_vbar_el1: (r_vbar_el1 ?d)}]] => rewrite (self_update_r_vbar_el1 d)
| [|- context[?d {r_contextidr_el1: ?a} {r_contextidr_el1: ?b}]] => rewrite (double_update_r_contextidr_el1 d a b)
| [|- context[?d {r_contextidr_el1: (r_contextidr_el1 ?d)}]] => rewrite (self_update_r_contextidr_el1 d)
| [|- context[?d {r_tpidr_el1: ?a} {r_tpidr_el1: ?b}]] => rewrite (double_update_r_tpidr_el1 d a b)
| [|- context[?d {r_tpidr_el1: (r_tpidr_el1 ?d)}]] => rewrite (self_update_r_tpidr_el1 d)
| [|- context[?d {r_amair_el1: ?a} {r_amair_el1: ?b}]] => rewrite (double_update_r_amair_el1 d a b)
| [|- context[?d {r_amair_el1: (r_amair_el1 ?d)}]] => rewrite (self_update_r_amair_el1 d)
| [|- context[?d {r_cntkctl_el1: ?a} {r_cntkctl_el1: ?b}]] => rewrite (double_update_r_cntkctl_el1 d a b)
| [|- context[?d {r_cntkctl_el1: (r_cntkctl_el1 ?d)}]] => rewrite (self_update_r_cntkctl_el1 d)
| [|- context[?d {r_par_el1: ?a} {r_par_el1: ?b}]] => rewrite (double_update_r_par_el1 d a b)
| [|- context[?d {r_par_el1: (r_par_el1 ?d)}]] => rewrite (self_update_r_par_el1 d)
| [|- context[?d {r_mdscr_el1: ?a} {r_mdscr_el1: ?b}]] => rewrite (double_update_r_mdscr_el1 d a b)
| [|- context[?d {r_mdscr_el1: (r_mdscr_el1 ?d)}]] => rewrite (self_update_r_mdscr_el1 d)
| [|- context[?d {r_mdccint_el1: ?a} {r_mdccint_el1: ?b}]] => rewrite (double_update_r_mdccint_el1 d a b)
| [|- context[?d {r_mdccint_el1: (r_mdccint_el1 ?d)}]] => rewrite (self_update_r_mdccint_el1 d)
| [|- context[?d {r_disr_el1: ?a} {r_disr_el1: ?b}]] => rewrite (double_update_r_disr_el1 d a b)
| [|- context[?d {r_disr_el1: (r_disr_el1 ?d)}]] => rewrite (self_update_r_disr_el1 d)
| [|- context[?d {r_mpam0_el1: ?a} {r_mpam0_el1: ?b}]] => rewrite (double_update_r_mpam0_el1 d a b)
| [|- context[?d {r_mpam0_el1: (r_mpam0_el1 ?d)}]] => rewrite (self_update_r_mpam0_el1 d)
| [|- context[?d {r_cnthctl_el2: ?a} {r_cnthctl_el2: ?b}]] => rewrite (double_update_r_cnthctl_el2 d a b)
| [|- context[?d {r_cnthctl_el2: (r_cnthctl_el2 ?d)}]] => rewrite (self_update_r_cnthctl_el2 d)
| [|- context[?d {r_cntvoff_el2: ?a} {r_cntvoff_el2: ?b}]] => rewrite (double_update_r_cntvoff_el2 d a b)
| [|- context[?d {r_cntvoff_el2: (r_cntvoff_el2 ?d)}]] => rewrite (self_update_r_cntvoff_el2 d)
| [|- context[?d {r_cntpoff_el2: ?a} {r_cntpoff_el2: ?b}]] => rewrite (double_update_r_cntpoff_el2 d a b)
| [|- context[?d {r_cntpoff_el2: (r_cntpoff_el2 ?d)}]] => rewrite (self_update_r_cntpoff_el2 d)
| [|- context[?d {r_vmpidr_el2: ?a} {r_vmpidr_el2: ?b}]] => rewrite (double_update_r_vmpidr_el2 d a b)
| [|- context[?d {r_vmpidr_el2: (r_vmpidr_el2 ?d)}]] => rewrite (self_update_r_vmpidr_el2 d)
| [|- context[?d {r_vttbr_el2: ?a} {r_vttbr_el2: ?b}]] => rewrite (double_update_r_vttbr_el2 d a b)
| [|- context[?d {r_vttbr_el2: (r_vttbr_el2 ?d)}]] => rewrite (self_update_r_vttbr_el2 d)
| [|- context[?d {r_vtcr_el2: ?a} {r_vtcr_el2: ?b}]] => rewrite (double_update_r_vtcr_el2 d a b)
| [|- context[?d {r_vtcr_el2: (r_vtcr_el2 ?d)}]] => rewrite (self_update_r_vtcr_el2 d)
| [|- context[?d {r_hcr_el2: ?a} {r_hcr_el2: ?b}]] => rewrite (double_update_r_hcr_el2 d a b)
| [|- context[?d {r_hcr_el2: (r_hcr_el2 ?d)}]] => rewrite (self_update_r_hcr_el2 d)
| [|- context[?d {r_actlr_el2: ?a} {r_actlr_el2: ?b}]] => rewrite (double_update_r_actlr_el2 d a b)
| [|- context[?d {r_actlr_el2: (r_actlr_el2 ?d)}]] => rewrite (self_update_r_actlr_el2 d)
| [|- context[?d {r_afsr0_el2: ?a} {r_afsr0_el2: ?b}]] => rewrite (double_update_r_afsr0_el2 d a b)
| [|- context[?d {r_afsr0_el2: (r_afsr0_el2 ?d)}]] => rewrite (self_update_r_afsr0_el2 d)
| [|- context[?d {r_afsr1_el2: ?a} {r_afsr1_el2: ?b}]] => rewrite (double_update_r_afsr1_el2 d a b)
| [|- context[?d {r_afsr1_el2: (r_afsr1_el2 ?d)}]] => rewrite (self_update_r_afsr1_el2 d)
| [|- context[?d {r_amair_el2: ?a} {r_amair_el2: ?b}]] => rewrite (double_update_r_amair_el2 d a b)
| [|- context[?d {r_amair_el2: (r_amair_el2 ?d)}]] => rewrite (self_update_r_amair_el2 d)
| [|- context[?d {r_cptr_el2: ?a} {r_cptr_el2: ?b}]] => rewrite (double_update_r_cptr_el2 d a b)
| [|- context[?d {r_cptr_el2: (r_cptr_el2 ?d)}]] => rewrite (self_update_r_cptr_el2 d)
| [|- context[?d {r_elr_el2: ?a} {r_elr_el2: ?b}]] => rewrite (double_update_r_elr_el2 d a b)
| [|- context[?d {r_elr_el2: (r_elr_el2 ?d)}]] => rewrite (self_update_r_elr_el2 d)
| [|- context[?d {r_esr_el2: ?a} {r_esr_el2: ?b}]] => rewrite (double_update_r_esr_el2 d a b)
| [|- context[?d {r_esr_el2: (r_esr_el2 ?d)}]] => rewrite (self_update_r_esr_el2 d)
| [|- context[?d {r_far_el2: ?a} {r_far_el2: ?b}]] => rewrite (double_update_r_far_el2 d a b)
| [|- context[?d {r_far_el2: (r_far_el2 ?d)}]] => rewrite (self_update_r_far_el2 d)
| [|- context[?d {r_hacr_el2: ?a} {r_hacr_el2: ?b}]] => rewrite (double_update_r_hacr_el2 d a b)
| [|- context[?d {r_hacr_el2: (r_hacr_el2 ?d)}]] => rewrite (self_update_r_hacr_el2 d)
| [|- context[?d {r_hpfar_el2: ?a} {r_hpfar_el2: ?b}]] => rewrite (double_update_r_hpfar_el2 d a b)
| [|- context[?d {r_hpfar_el2: (r_hpfar_el2 ?d)}]] => rewrite (self_update_r_hpfar_el2 d)
| [|- context[?d {r_hstr_el2: ?a} {r_hstr_el2: ?b}]] => rewrite (double_update_r_hstr_el2 d a b)
| [|- context[?d {r_hstr_el2: (r_hstr_el2 ?d)}]] => rewrite (self_update_r_hstr_el2 d)
| [|- context[?d {r_mair_el2: ?a} {r_mair_el2: ?b}]] => rewrite (double_update_r_mair_el2 d a b)
| [|- context[?d {r_mair_el2: (r_mair_el2 ?d)}]] => rewrite (self_update_r_mair_el2 d)
| [|- context[?d {r_mpam_el2: ?a} {r_mpam_el2: ?b}]] => rewrite (double_update_r_mpam_el2 d a b)
| [|- context[?d {r_mpam_el2: (r_mpam_el2 ?d)}]] => rewrite (self_update_r_mpam_el2 d)
| [|- context[?d {r_mpamhcr_el2: ?a} {r_mpamhcr_el2: ?b}]] => rewrite (double_update_r_mpamhcr_el2 d a b)
| [|- context[?d {r_mpamhcr_el2: (r_mpamhcr_el2 ?d)}]] => rewrite (self_update_r_mpamhcr_el2 d)
| [|- context[?d {r_pmscr_el2: ?a} {r_pmscr_el2: ?b}]] => rewrite (double_update_r_pmscr_el2 d a b)
| [|- context[?d {r_pmscr_el2: (r_pmscr_el2 ?d)}]] => rewrite (self_update_r_pmscr_el2 d)
| [|- context[?d {r_sctlr_el2: ?a} {r_sctlr_el2: ?b}]] => rewrite (double_update_r_sctlr_el2 d a b)
| [|- context[?d {r_sctlr_el2: (r_sctlr_el2 ?d)}]] => rewrite (self_update_r_sctlr_el2 d)
| [|- context[?d {r_scxtnum_el2: ?a} {r_scxtnum_el2: ?b}]] => rewrite (double_update_r_scxtnum_el2 d a b)
| [|- context[?d {r_scxtnum_el2: (r_scxtnum_el2 ?d)}]] => rewrite (self_update_r_scxtnum_el2 d)
| [|- context[?d {r_sp_el2: ?a} {r_sp_el2: ?b}]] => rewrite (double_update_r_sp_el2 d a b)
| [|- context[?d {r_sp_el2: (r_sp_el2 ?d)}]] => rewrite (self_update_r_sp_el2 d)
| [|- context[?d {r_spsr_el2: ?a} {r_spsr_el2: ?b}]] => rewrite (double_update_r_spsr_el2 d a b)
| [|- context[?d {r_spsr_el2: (r_spsr_el2 ?d)}]] => rewrite (self_update_r_spsr_el2 d)
| [|- context[?d {r_tcr_el2: ?a} {r_tcr_el2: ?b}]] => rewrite (double_update_r_tcr_el2 d a b)
| [|- context[?d {r_tcr_el2: (r_tcr_el2 ?d)}]] => rewrite (self_update_r_tcr_el2 d)
| [|- context[?d {r_tfsr_el2: ?a} {r_tfsr_el2: ?b}]] => rewrite (double_update_r_tfsr_el2 d a b)
| [|- context[?d {r_tfsr_el2: (r_tfsr_el2 ?d)}]] => rewrite (self_update_r_tfsr_el2 d)
| [|- context[?d {r_tpidr_el2: ?a} {r_tpidr_el2: ?b}]] => rewrite (double_update_r_tpidr_el2 d a b)
| [|- context[?d {r_tpidr_el2: (r_tpidr_el2 ?d)}]] => rewrite (self_update_r_tpidr_el2 d)
| [|- context[?d {r_trfcr_el2: ?a} {r_trfcr_el2: ?b}]] => rewrite (double_update_r_trfcr_el2 d a b)
| [|- context[?d {r_trfcr_el2: (r_trfcr_el2 ?d)}]] => rewrite (self_update_r_trfcr_el2 d)
| [|- context[?d {r_ttbr0_el2: ?a} {r_ttbr0_el2: ?b}]] => rewrite (double_update_r_ttbr0_el2 d a b)
| [|- context[?d {r_ttbr0_el2: (r_ttbr0_el2 ?d)}]] => rewrite (self_update_r_ttbr0_el2 d)
| [|- context[?d {r_ttbr1_el2: ?a} {r_ttbr1_el2: ?b}]] => rewrite (double_update_r_ttbr1_el2 d a b)
| [|- context[?d {r_ttbr1_el2: (r_ttbr1_el2 ?d)}]] => rewrite (self_update_r_ttbr1_el2 d)
| [|- context[?d {r_vbar_el2: ?a} {r_vbar_el2: ?b}]] => rewrite (double_update_r_vbar_el2 d a b)
| [|- context[?d {r_vbar_el2: (r_vbar_el2 ?d)}]] => rewrite (self_update_r_vbar_el2 d)
| [|- context[?d {r_vdisr_el2: ?a} {r_vdisr_el2: ?b}]] => rewrite (double_update_r_vdisr_el2 d a b)
| [|- context[?d {r_vdisr_el2: (r_vdisr_el2 ?d)}]] => rewrite (self_update_r_vdisr_el2 d)
| [|- context[?d {r_vncr_el2: ?a} {r_vncr_el2: ?b}]] => rewrite (double_update_r_vncr_el2 d a b)
| [|- context[?d {r_vncr_el2: (r_vncr_el2 ?d)}]] => rewrite (self_update_r_vncr_el2 d)
| [|- context[?d {r_vpidr_el2: ?a} {r_vpidr_el2: ?b}]] => rewrite (double_update_r_vpidr_el2 d a b)
| [|- context[?d {r_vpidr_el2: (r_vpidr_el2 ?d)}]] => rewrite (self_update_r_vpidr_el2 d)
| [|- context[?d {r_vsesr_el2: ?a} {r_vsesr_el2: ?b}]] => rewrite (double_update_r_vsesr_el2 d a b)
| [|- context[?d {r_vsesr_el2: (r_vsesr_el2 ?d)}]] => rewrite (self_update_r_vsesr_el2 d)
| [|- context[?d {r_vstcr_el2: ?a} {r_vstcr_el2: ?b}]] => rewrite (double_update_r_vstcr_el2 d a b)
| [|- context[?d {r_vstcr_el2: (r_vstcr_el2 ?d)}]] => rewrite (self_update_r_vstcr_el2 d)
| [|- context[?d {r_vsttbr_el2: ?a} {r_vsttbr_el2: ?b}]] => rewrite (double_update_r_vsttbr_el2 d a b)
| [|- context[?d {r_vsttbr_el2: (r_vsttbr_el2 ?d)}]] => rewrite (self_update_r_vsttbr_el2 d)
| [|- context[?d {r_zcr_el2: ?a} {r_zcr_el2: ?b}]] => rewrite (double_update_r_zcr_el2 d a b)
| [|- context[?d {r_zcr_el2: (r_zcr_el2 ?d)}]] => rewrite (self_update_r_zcr_el2 d)
| [|- context[?d {r_icc_sre_el2: ?a} {r_icc_sre_el2: ?b}]] => rewrite (double_update_r_icc_sre_el2 d a b)
| [|- context[?d {r_icc_sre_el2: (r_icc_sre_el2 ?d)}]] => rewrite (self_update_r_icc_sre_el2 d)
| [|- context[?d {r_icc_hppir1_el1: ?a} {r_icc_hppir1_el1: ?b}]] => rewrite (double_update_r_icc_hppir1_el1 d a b)
| [|- context[?d {r_icc_hppir1_el1: (r_icc_hppir1_el1 ?d)}]] => rewrite (self_update_r_icc_hppir1_el1 d)
| [|- context[?d {r_spsr_el3: ?a} {r_spsr_el3: ?b}]] => rewrite (double_update_r_spsr_el3 d a b)
| [|- context[?d {r_spsr_el3: (r_spsr_el3 ?d)}]] => rewrite (self_update_r_spsr_el3 d)
| [|- context[?d {r_elr_el3: ?a} {r_elr_el3: ?b}]] => rewrite (double_update_r_elr_el3 d a b)
| [|- context[?d {r_elr_el3: (r_elr_el3 ?d)}]] => rewrite (self_update_r_elr_el3 d)
| [|- context[?d {r_esr_el3: ?a} {r_esr_el3: ?b}]] => rewrite (double_update_r_esr_el3 d a b)
| [|- context[?d {r_esr_el3: (r_esr_el3 ?d)}]] => rewrite (self_update_r_esr_el3 d)
| [|- context[?d {r_scr_el3: ?a} {r_scr_el3: ?b}]] => rewrite (double_update_r_scr_el3 d a b)
| [|- context[?d {r_scr_el3: (r_scr_el3 ?d)}]] => rewrite (self_update_r_scr_el3 d)
| [|- context[?d {r_tpidr_el3: ?a} {r_tpidr_el3: ?b}]] => rewrite (double_update_r_tpidr_el3 d a b)
| [|- context[?d {r_tpidr_el3: (r_tpidr_el3 ?d)}]] => rewrite (self_update_r_tpidr_el3 d)
| [|- context[?d {a_CN: ?a} {a_CN: ?b}]] => rewrite (double_update_a_CN d a b)
| [|- context[?d {a_CN: (a_CN ?d)}]] => rewrite (self_update_a_CN d)
| [|- context[?d {a_CZ: ?a} {a_CZ: ?b}]] => rewrite (double_update_a_CZ d a b)
| [|- context[?d {a_CZ: (a_CZ ?d)}]] => rewrite (self_update_a_CZ d)
| [|- context[?d {a_CC: ?a} {a_CC: ?b}]] => rewrite (double_update_a_CC d a b)
| [|- context[?d {a_CC: (a_CC ?d)}]] => rewrite (self_update_a_CC d)
| [|- context[?d {a_CV: ?a} {a_CV: ?b}]] => rewrite (double_update_a_CV d a b)
| [|- context[?d {a_CV: (a_CV ?d)}]] => rewrite (self_update_a_CV d)
| [|- context[?d {a_DAIFCLR: ?a} {a_DAIFCLR: ?b}]] => rewrite (double_update_a_DAIFCLR d a b)
| [|- context[?d {a_DAIFCLR: (a_DAIFCLR ?d)}]] => rewrite (self_update_a_DAIFCLR d)
| [|- context[?d {a_SP: ?a} {a_SP: ?b}]] => rewrite (double_update_a_SP d a b)
| [|- context[?d {a_SP: (a_SP ?d)}]] => rewrite (self_update_a_SP d)
| [|- context[?d {a_PC: ?a} {a_PC: ?b}]] => rewrite (double_update_a_PC d a b)
| [|- context[?d {a_PC: (a_PC ?d)}]] => rewrite (self_update_a_PC d)
| [|- context[?d {a_EL3: ?a} {a_EL3: ?b}]] => rewrite (double_update_a_EL3 d a b)
| [|- context[?d {a_EL3: (a_EL3 ?d)}]] => rewrite (self_update_a_EL3 d)
| [|- context[?d {t_masked: ?a} {t_masked: ?b}]] => rewrite (double_update_t_masked d a b)
| [|- context[?d {t_masked: (t_masked ?d)}]] => rewrite (self_update_t_masked d)
| [|- context[?d {t_asserted: ?a} {t_asserted: ?b}]] => rewrite (double_update_t_asserted d a b)
| [|- context[?d {t_asserted: (t_asserted ?d)}]] => rewrite (self_update_t_asserted d)
| [|- context[?d {g_tag: ?a} {g_tag: ?b}]] => rewrite (double_update_g_tag d a b)
| [|- context[?d {g_tag: (g_tag ?d)}]] => rewrite (self_update_g_tag d)
| [|- context[?d {g_refcount: ?a} {g_refcount: ?b}]] => rewrite (double_update_g_refcount d a b)
| [|- context[?d {g_refcount: (g_refcount ?d)}]] => rewrite (self_update_g_refcount d)
| [|- context[?d {g_rd: ?a} {g_rd: ?b}]] => rewrite (double_update_g_rd d a b)
| [|- context[?d {g_rd: (g_rd ?d)}]] => rewrite (self_update_g_rd d)
| [|- context[?d {g_map_addr: ?a} {g_map_addr: ?b}]] => rewrite (double_update_g_map_addr d a b)
| [|- context[?d {g_map_addr: (g_map_addr ?d)}]] => rewrite (self_update_g_map_addr d)
| [|- context[?d {r_rvic_enabled: ?a} {r_rvic_enabled: ?b}]] => rewrite (double_update_r_rvic_enabled d a b)
| [|- context[?d {r_rvic_enabled: (r_rvic_enabled ?d)}]] => rewrite (self_update_r_rvic_enabled d)
| [|- context[?d {r_mask_bits: ?a} {r_mask_bits: ?b}]] => rewrite (double_update_r_mask_bits d a b)
| [|- context[?d {r_mask_bits: (r_mask_bits ?d)}]] => rewrite (self_update_r_mask_bits d)
| [|- context[?d {r_pending_bits: ?a} {r_pending_bits: ?b}]] => rewrite (double_update_r_pending_bits d a b)
| [|- context[?d {r_pending_bits: (r_pending_bits ?d)}]] => rewrite (self_update_r_pending_bits d)
| [|- context[?d {g_data: ?a} {g_data: ?b}]] => rewrite (double_update_g_data d a b)
| [|- context[?d {g_data: (g_data ?d)}]] => rewrite (self_update_g_data d)
| [|- context[?d {g_realm_state: ?a} {g_realm_state: ?b}]] => rewrite (double_update_g_realm_state d a b)
| [|- context[?d {g_realm_state: (g_realm_state ?d)}]] => rewrite (self_update_g_realm_state d)
| [|- context[?d {g_par_base: ?a} {g_par_base: ?b}]] => rewrite (double_update_g_par_base d a b)
| [|- context[?d {g_par_base: (g_par_base ?d)}]] => rewrite (self_update_g_par_base d)
| [|- context[?d {g_par_end: ?a} {g_par_end: ?b}]] => rewrite (double_update_g_par_end d a b)
| [|- context[?d {g_par_end: (g_par_end ?d)}]] => rewrite (self_update_g_par_end d)
| [|- context[?d {g_rec_list: ?a} {g_rec_list: ?b}]] => rewrite (double_update_g_rec_list d a b)
| [|- context[?d {g_rec_list: (g_rec_list ?d)}]] => rewrite (self_update_g_rec_list d)
| [|- context[?d {g_rtt: ?a} {g_rtt: ?b}]] => rewrite (double_update_g_rtt d a b)
| [|- context[?d {g_rtt: (g_rtt ?d)}]] => rewrite (self_update_g_rtt d)
| [|- context[?d {g_measurement_algo: ?a} {g_measurement_algo: ?b}]] => rewrite (double_update_g_measurement_algo d a b)
| [|- context[?d {g_measurement_algo: (g_measurement_algo ?d)}]] => rewrite (self_update_g_measurement_algo d)
| [|- context[?d {g_measurement_ctx: ?a} {g_measurement_ctx: ?b}]] => rewrite (double_update_g_measurement_ctx d a b)
| [|- context[?d {g_measurement_ctx: (g_measurement_ctx ?d)}]] => rewrite (self_update_g_measurement_ctx d)
| [|- context[?d {g_measurement: ?a} {g_measurement: ?b}]] => rewrite (double_update_g_measurement d a b)
| [|- context[?d {g_measurement: (g_measurement ?d)}]] => rewrite (self_update_g_measurement d)
| [|- context[?d {g_recs: ?a} {g_recs: ?b}]] => rewrite (double_update_g_recs d a b)
| [|- context[?d {g_recs: (g_recs ?d)}]] => rewrite (self_update_g_recs d)
| [|- context[?d {g_rvic: ?a} {g_rvic: ?b}]] => rewrite (double_update_g_rvic d a b)
| [|- context[?d {g_rvic: (g_rvic ?d)}]] => rewrite (self_update_g_rvic d)
| [|- context[?d {g_runnable: ?a} {g_runnable: ?b}]] => rewrite (double_update_g_runnable d a b)
| [|- context[?d {g_runnable: (g_runnable ?d)}]] => rewrite (self_update_g_runnable d)
| [|- context[?d {g_regs: ?a} {g_regs: ?b}]] => rewrite (double_update_g_regs d a b)
| [|- context[?d {g_regs: (g_regs ?d)}]] => rewrite (self_update_g_regs d)
| [|- context[?d {g_pc: ?a} {g_pc: ?b}]] => rewrite (double_update_g_pc d a b)
| [|- context[?d {g_pc: (g_pc ?d)}]] => rewrite (self_update_g_pc d)
| [|- context[?d {g_pstate: ?a} {g_pstate: ?b}]] => rewrite (double_update_g_pstate d a b)
| [|- context[?d {g_pstate: (g_pstate ?d)}]] => rewrite (self_update_g_pstate d)
| [|- context[?d {g_vtimer: ?a} {g_vtimer: ?b}]] => rewrite (double_update_g_vtimer d a b)
| [|- context[?d {g_vtimer: (g_vtimer ?d)}]] => rewrite (self_update_g_vtimer d)
| [|- context[?d {g_ptimer: ?a} {g_ptimer: ?b}]] => rewrite (double_update_g_ptimer d a b)
| [|- context[?d {g_ptimer: (g_ptimer ?d)}]] => rewrite (self_update_g_ptimer d)
| [|- context[?d {g_dispose_pending: ?a} {g_dispose_pending: ?b}]] => rewrite (double_update_g_dispose_pending d a b)
| [|- context[?d {g_dispose_pending: (g_dispose_pending ?d)}]] => rewrite (self_update_g_dispose_pending d)
| [|- context[?d {g_dispose_addr: ?a} {g_dispose_addr: ?b}]] => rewrite (double_update_g_dispose_addr d a b)
| [|- context[?d {g_dispose_addr: (g_dispose_addr ?d)}]] => rewrite (self_update_g_dispose_addr d)
| [|- context[?d {g_dispose_size: ?a} {g_dispose_size: ?b}]] => rewrite (double_update_g_dispose_size d a b)
| [|- context[?d {g_dispose_size: (g_dispose_size ?d)}]] => rewrite (self_update_g_dispose_size d)
| [|- context[?d {g_rec_rd: ?a} {g_rec_rd: ?b}]] => rewrite (double_update_g_rec_rd d a b)
| [|- context[?d {g_rec_rd: (g_rec_rd ?d)}]] => rewrite (self_update_g_rec_rd d)
| [|- context[?d {g_rec_par_base: ?a} {g_rec_par_base: ?b}]] => rewrite (double_update_g_rec_par_base d a b)
| [|- context[?d {g_rec_par_base: (g_rec_par_base ?d)}]] => rewrite (self_update_g_rec_par_base d)
| [|- context[?d {g_rec_par_end: ?a} {g_rec_par_end: ?b}]] => rewrite (double_update_g_rec_par_end d a b)
| [|- context[?d {g_rec_par_end: (g_rec_par_end ?d)}]] => rewrite (self_update_g_rec_par_end d)
| [|- context[?d {g_rec_rec_list: ?a} {g_rec_rec_list: ?b}]] => rewrite (double_update_g_rec_rec_list d a b)
| [|- context[?d {g_rec_rec_list: (g_rec_rec_list ?d)}]] => rewrite (self_update_g_rec_rec_list d)
| [|- context[?d {g_esr: ?a} {g_esr: ?b}]] => rewrite (double_update_g_esr d a b)
| [|- context[?d {g_esr: (g_esr ?d)}]] => rewrite (self_update_g_esr d)
| [|- context[?d {g_running: ?a} {g_running: ?b}]] => rewrite (double_update_g_running d a b)
| [|- context[?d {g_running: (g_running ?d)}]] => rewrite (self_update_g_running d)
| [|- context[?d {g_inited: ?a} {g_inited: ?b}]] => rewrite (double_update_g_inited d a b)
| [|- context[?d {g_inited: (g_inited ?d)}]] => rewrite (self_update_g_inited d)
| [|- context[?d {g_rec: ?a} {g_rec: ?b}]] => rewrite (double_update_g_rec d a b)
| [|- context[?d {g_rec: (g_rec ?d)}]] => rewrite (self_update_g_rec d)
| [|- context[?d {g_rec_idx: ?a} {g_rec_idx: ?b}]] => rewrite (double_update_g_rec_idx d a b)
| [|- context[?d {g_rec_idx: (g_rec_idx ?d)}]] => rewrite (self_update_g_rec_idx d)
| [|- context[?d {tbl_level: ?a} {tbl_level: ?b}]] => rewrite (double_update_tbl_level d a b)
| [|- context[?d {tbl_level: (tbl_level ?d)}]] => rewrite (self_update_tbl_level d)
| [|- context[?d {tbl_parent: ?a} {tbl_parent: ?b}]] => rewrite (double_update_tbl_parent d a b)
| [|- context[?d {tbl_parent: (tbl_parent ?d)}]] => rewrite (self_update_tbl_parent d)
| [|- context[?d {glock: ?a} {glock: ?b}]] => rewrite (double_update_glock d a b)
| [|- context[?d {glock: (glock ?d)}]] => rewrite (self_update_glock d)
| [|- context[?d {gref: ?a} {gref: ?b}]] => rewrite (double_update_gref d a b)
| [|- context[?d {gref: (gref ?d)}]] => rewrite (self_update_gref d)
| [|- context[?d {gtype: ?a} {gtype: ?b}]] => rewrite (double_update_gtype d a b)
| [|- context[?d {gtype: (gtype ?d)}]] => rewrite (self_update_gtype d)
| [|- context[?d {gcnt: ?a} {gcnt: ?b}]] => rewrite (double_update_gcnt d a b)
| [|- context[?d {gcnt: (gcnt ?d)}]] => rewrite (self_update_gcnt d)
| [|- context[?d {ginfo: ?a} {ginfo: ?b}]] => rewrite (double_update_ginfo d a b)
| [|- context[?d {ginfo: (ginfo ?d)}]] => rewrite (self_update_ginfo d)
| [|- context[?d {gnorm: ?a} {gnorm: ?b}]] => rewrite (double_update_gnorm d a b)
| [|- context[?d {gnorm: (gnorm ?d)}]] => rewrite (self_update_gnorm d)
| [|- context[?d {grec: ?a} {grec: ?b}]] => rewrite (double_update_grec d a b)
| [|- context[?d {grec: (grec ?d)}]] => rewrite (self_update_grec d)
| [|- context[?d {gro: ?a} {gro: ?b}]] => rewrite (double_update_gro d a b)
| [|- context[?d {gro: (gro ?d)}]] => rewrite (self_update_gro d)
| [|- context[?d {gaux: ?a} {gaux: ?b}]] => rewrite (double_update_gaux d a b)
| [|- context[?d {gaux: (gaux ?d)}]] => rewrite (self_update_gaux d)
| [|- context[?d {cpu_regs: ?a} {cpu_regs: ?b}]] => rewrite (double_update_cpu_regs d a b)
| [|- context[?d {cpu_regs: (cpu_regs ?d)}]] => rewrite (self_update_cpu_regs d)
| [|- context[?d {asm_regs: ?a} {asm_regs: ?b}]] => rewrite (double_update_asm_regs d a b)
| [|- context[?d {asm_regs: (asm_regs ?d)}]] => rewrite (self_update_asm_regs d)
| [|- context[?d {id_regs: ?a} {id_regs: ?b}]] => rewrite (double_update_id_regs d a b)
| [|- context[?d {id_regs: (id_regs ?d)}]] => rewrite (self_update_id_regs d)
| [|- context[?d {buffer: ?a} {buffer: ?b}]] => rewrite (double_update_buffer d a b)
| [|- context[?d {buffer: (buffer ?d)}]] => rewrite (self_update_buffer d)
| [|- context[?d {ns_regs_el2: ?a} {ns_regs_el2: ?b}]] => rewrite (double_update_ns_regs_el2 d a b)
| [|- context[?d {ns_regs_el2: (ns_regs_el2 ?d)}]] => rewrite (self_update_ns_regs_el2 d)
| [|- context[?d {realm_params: ?a} {realm_params: ?b}]] => rewrite (double_update_realm_params d a b)
| [|- context[?d {realm_params: (realm_params ?d)}]] => rewrite (self_update_realm_params d)
| [|- context[?d {rec_params: ?a} {rec_params: ?b}]] => rewrite (double_update_rec_params d a b)
| [|- context[?d {rec_params: (rec_params ?d)}]] => rewrite (self_update_rec_params d)
| [|- context[?d {rec_run: ?a} {rec_run: ?b}]] => rewrite (double_update_rec_run d a b)
| [|- context[?d {rec_run: (rec_run ?d)}]] => rewrite (self_update_rec_run d)
| [|- context[?d {retval: ?a} {retval: ?b}]] => rewrite (double_update_retval d a b)
| [|- context[?d {retval: (retval ?d)}]] => rewrite (self_update_retval d)
| [|- context[?d {locked_g: ?a} {locked_g: ?b}]] => rewrite (double_update_locked_g d a b)
| [|- context[?d {locked_g: (locked_g ?d)}]] => rewrite (self_update_locked_g d)
| [|- context[?d {wi_last_level: ?a} {wi_last_level: ?b}]] => rewrite (double_update_wi_last_level d a b)
| [|- context[?d {wi_last_level: (wi_last_level ?d)}]] => rewrite (self_update_wi_last_level d)
| [|- context[?d {wi_llt: ?a} {wi_llt: ?b}]] => rewrite (double_update_wi_llt d a b)
| [|- context[?d {wi_llt: (wi_llt ?d)}]] => rewrite (self_update_wi_llt d)
| [|- context[?d {wi_index: ?a} {wi_index: ?b}]] => rewrite (double_update_wi_index d a b)
| [|- context[?d {wi_index: (wi_index ?d)}]] => rewrite (self_update_wi_index d)
| [|- context[?d {rvic_x0: ?a} {rvic_x0: ?b}]] => rewrite (double_update_rvic_x0 d a b)
| [|- context[?d {rvic_x0: (rvic_x0 ?d)}]] => rewrite (self_update_rvic_x0 d)
| [|- context[?d {rvic_x1: ?a} {rvic_x1: ?b}]] => rewrite (double_update_rvic_x1 d a b)
| [|- context[?d {rvic_x1: (rvic_x1 ?d)}]] => rewrite (self_update_rvic_x1 d)
| [|- context[?d {rvic_x2: ?a} {rvic_x2: ?b}]] => rewrite (double_update_rvic_x2 d a b)
| [|- context[?d {rvic_x2: (rvic_x2 ?d)}]] => rewrite (self_update_rvic_x2 d)
| [|- context[?d {rvic_x3: ?a} {rvic_x3: ?b}]] => rewrite (double_update_rvic_x3 d a b)
| [|- context[?d {rvic_x3: (rvic_x3 ?d)}]] => rewrite (self_update_rvic_x3 d)
| [|- context[?d {rvic_target: ?a} {rvic_target: ?b}]] => rewrite (double_update_rvic_target d a b)
| [|- context[?d {rvic_target: (rvic_target ?d)}]] => rewrite (self_update_rvic_target d)
| [|- context[?d {rvic_ns_notify: ?a} {rvic_ns_notify: ?b}]] => rewrite (double_update_rvic_ns_notify d a b)
| [|- context[?d {rvic_ns_notify: (rvic_ns_notify ?d)}]] => rewrite (self_update_rvic_ns_notify d)
| [|- context[?d {psci_x0: ?a} {psci_x0: ?b}]] => rewrite (double_update_psci_x0 d a b)
| [|- context[?d {psci_x0: (psci_x0 ?d)}]] => rewrite (self_update_psci_x0 d)
| [|- context[?d {psci_x1: ?a} {psci_x1: ?b}]] => rewrite (double_update_psci_x1 d a b)
| [|- context[?d {psci_x1: (psci_x1 ?d)}]] => rewrite (self_update_psci_x1 d)
| [|- context[?d {psci_x2: ?a} {psci_x2: ?b}]] => rewrite (double_update_psci_x2 d a b)
| [|- context[?d {psci_x2: (psci_x2 ?d)}]] => rewrite (self_update_psci_x2 d)
| [|- context[?d {psci_x3: ?a} {psci_x3: ?b}]] => rewrite (double_update_psci_x3 d a b)
| [|- context[?d {psci_x3: (psci_x3 ?d)}]] => rewrite (self_update_psci_x3 d)
| [|- context[?d {psci_forward_x0: ?a} {psci_forward_x0: ?b}]] => rewrite (double_update_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x0: (psci_forward_x0 ?d)}]] => rewrite (self_update_psci_forward_x0 d)
| [|- context[?d {psci_forward_x1: ?a} {psci_forward_x1: ?b}]] => rewrite (double_update_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x1: (psci_forward_x1 ?d)}]] => rewrite (self_update_psci_forward_x1 d)
| [|- context[?d {psci_forward_x2: ?a} {psci_forward_x2: ?b}]] => rewrite (double_update_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x2: (psci_forward_x2 ?d)}]] => rewrite (self_update_psci_forward_x2 d)
| [|- context[?d {psci_forward_x3: ?a} {psci_forward_x3: ?b}]] => rewrite (double_update_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_x3: (psci_forward_x3 ?d)}]] => rewrite (self_update_psci_forward_x3 d)
| [|- context[?d {psci_forward_psci_call: ?a} {psci_forward_psci_call: ?b}]] => rewrite (double_update_psci_forward_psci_call d a b)
| [|- context[?d {psci_forward_psci_call: (psci_forward_psci_call ?d)}]] => rewrite (self_update_psci_forward_psci_call d)
| [|- context[?d {target_rec: ?a} {target_rec: ?b}]] => rewrite (double_update_target_rec d a b)
| [|- context[?d {target_rec: (target_rec ?d)}]] => rewrite (self_update_target_rec d)
| [|- context[?d {el2_stack: ?a} {el2_stack: ?b}]] => rewrite (double_update_el2_stack d a b)
| [|- context[?d {el2_stack: (el2_stack ?d)}]] => rewrite (self_update_el2_stack d)
| [|- context[?d {el3_stack: ?a} {el3_stack: ?b}]] => rewrite (double_update_el3_stack d a b)
| [|- context[?d {el3_stack: (el3_stack ?d)}]] => rewrite (self_update_el3_stack d)
| [|- context[?d {ns_regs_el3: ?a} {ns_regs_el3: ?b}]] => rewrite (double_update_ns_regs_el3 d a b)
| [|- context[?d {ns_regs_el3: (ns_regs_el3 ?d)}]] => rewrite (self_update_ns_regs_el3 d)
| [|- context[?d {realm_regs_el3: ?a} {realm_regs_el3: ?b}]] => rewrite (double_update_realm_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: (realm_regs_el3 ?d)}]] => rewrite (self_update_realm_regs_el3 d)
| [|- context[?d {cur_rec: ?a} {cur_rec: ?b}]] => rewrite (double_update_cur_rec d a b)
| [|- context[?d {cur_rec: (cur_rec ?d)}]] => rewrite (self_update_cur_rec d)
| [|- context[?d {mstage: ?a} {mstage: ?b}]] => rewrite (double_update_mstage d a b)
| [|- context[?d {mstage: (mstage ?d)}]] => rewrite (self_update_mstage d)
| [|- context[?d {trap_reason: ?a} {trap_reason: ?b}]] => rewrite (double_update_trap_reason d a b)
| [|- context[?d {trap_reason: (trap_reason ?d)}]] => rewrite (self_update_trap_reason d)
| [|- context[?d {sec_mem: ?a} {sec_mem: ?b}]] => rewrite (double_update_sec_mem d a b)
| [|- context[?d {sec_mem: (sec_mem ?d)}]] => rewrite (self_update_sec_mem d)
| [|- context[?d {sec_regs: ?a} {sec_regs: ?b}]] => rewrite (double_update_sec_regs d a b)
| [|- context[?d {sec_regs: (sec_regs ?d)}]] => rewrite (self_update_sec_regs d)
| [|- context[?d {decl_regs: ?a} {decl_regs: ?b}]] => rewrite (double_update_decl_regs d a b)
| [|- context[?d {decl_regs: (decl_regs ?d)}]] => rewrite (self_update_decl_regs d)
| [|- context[?d {gs: ?a} {gs: ?b}]] => rewrite (double_update_gs d a b)
| [|- context[?d {gs: (gs ?d)}]] => rewrite (self_update_gs d)
| [|- context[?d {gpt: ?a} {gpt: ?b}]] => rewrite (double_update_gpt d a b)
| [|- context[?d {gpt: (gpt ?d)}]] => rewrite (self_update_gpt d)
| [|- context[?d {gpt_lk: ?a} {gpt_lk: ?b}]] => rewrite (double_update_gpt_lk d a b)
| [|- context[?d {gpt_lk: (gpt_lk ?d)}]] => rewrite (self_update_gpt_lk d)
| [|- context[?d {tlbs: ?a} {tlbs: ?b}]] => rewrite (double_update_tlbs d a b)
| [|- context[?d {tlbs: (tlbs ?d)}]] => rewrite (self_update_tlbs d)
| [|- context[?d {rtts: ?a} {rtts: ?b}]] => rewrite (double_update_rtts d a b)
| [|- context[?d {rtts: (rtts ?d)}]] => rewrite (self_update_rtts d)
| [|- context[?d {realms: ?a} {realms: ?b}]] => rewrite (double_update_realms d a b)
| [|- context[?d {realms: (realms ?d)}]] => rewrite (self_update_realms d)
| [|- context[?d {log: ?a} {log: ?b}]] => rewrite (double_update_log d a b)
| [|- context[?d {log: (log ?d)}]] => rewrite (self_update_log d)
| [|- context[?d {oracle: ?a} {oracle: ?b}]] => rewrite (double_update_oracle d a b)
| [|- context[?d {oracle: (oracle ?d)}]] => rewrite (self_update_oracle d)
| [|- context[?d {repl: ?a} {repl: ?b}]] => rewrite (double_update_repl d a b)
| [|- context[?d {repl: (repl ?d)}]] => rewrite (self_update_repl d)
| [|- context[?d {share: ?a} {share: ?b}]] => rewrite (double_update_share d a b)
| [|- context[?d {share: (share ?d)}]] => rewrite (self_update_share d)
| [|- context[?d {priv: ?a} {priv: ?b}]] => rewrite (double_update_priv d a b)
| [|- context[?d {priv: (priv ?d)}]] => rewrite (self_update_priv d)
end.

Lemma swap_g_tag_g_refcount: forall d a b, d {g_refcount: a} {g_tag: b} = d{g_tag: b} {g_refcount: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_g_tag_g_rd: forall d a b, d {g_rd: a} {g_tag: b} = d{g_tag: b} {g_rd: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_g_tag_g_map_addr: forall d a b, d {g_map_addr: a} {g_tag: b} = d{g_tag: b} {g_map_addr: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_g_refcount_g_rd: forall d a b, d {g_rd: a} {g_refcount: b} = d{g_refcount: b} {g_rd: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_g_refcount_g_map_addr: forall d a b, d {g_map_addr: a} {g_refcount: b} = d{g_refcount: b} {g_map_addr: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_g_rd_g_map_addr: forall d a b, d {g_map_addr: a} {g_rd: b} = d{g_rd: b} {g_map_addr: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_asm_regs: forall d a b, d {asm_regs: a} {cpu_regs: b} = d{cpu_regs: b} {asm_regs: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_id_regs: forall d a b, d {id_regs: a} {cpu_regs: b} = d{cpu_regs: b} {id_regs: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_buffer: forall d a b, d {buffer: a} {cpu_regs: b} = d{cpu_regs: b} {buffer: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_ns_regs_el2: forall d a b, d {ns_regs_el2: a} {cpu_regs: b} = d{cpu_regs: b} {ns_regs_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_realm_params: forall d a b, d {realm_params: a} {cpu_regs: b} = d{cpu_regs: b} {realm_params: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_rec_params: forall d a b, d {rec_params: a} {cpu_regs: b} = d{cpu_regs: b} {rec_params: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_rec_run: forall d a b, d {rec_run: a} {cpu_regs: b} = d{cpu_regs: b} {rec_run: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_retval: forall d a b, d {retval: a} {cpu_regs: b} = d{cpu_regs: b} {retval: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_locked_g: forall d a b, d {locked_g: a} {cpu_regs: b} = d{cpu_regs: b} {locked_g: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_wi_last_level: forall d a b, d {wi_last_level: a} {cpu_regs: b} = d{cpu_regs: b} {wi_last_level: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_wi_llt: forall d a b, d {wi_llt: a} {cpu_regs: b} = d{cpu_regs: b} {wi_llt: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_wi_index: forall d a b, d {wi_index: a} {cpu_regs: b} = d{cpu_regs: b} {wi_index: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_rvic_x0: forall d a b, d {rvic_x0: a} {cpu_regs: b} = d{cpu_regs: b} {rvic_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_rvic_x1: forall d a b, d {rvic_x1: a} {cpu_regs: b} = d{cpu_regs: b} {rvic_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_rvic_x2: forall d a b, d {rvic_x2: a} {cpu_regs: b} = d{cpu_regs: b} {rvic_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_rvic_x3: forall d a b, d {rvic_x3: a} {cpu_regs: b} = d{cpu_regs: b} {rvic_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_rvic_target: forall d a b, d {rvic_target: a} {cpu_regs: b} = d{cpu_regs: b} {rvic_target: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_rvic_ns_notify: forall d a b, d {rvic_ns_notify: a} {cpu_regs: b} = d{cpu_regs: b} {rvic_ns_notify: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_psci_x0: forall d a b, d {psci_x0: a} {cpu_regs: b} = d{cpu_regs: b} {psci_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_psci_x1: forall d a b, d {psci_x1: a} {cpu_regs: b} = d{cpu_regs: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_psci_x2: forall d a b, d {psci_x2: a} {cpu_regs: b} = d{cpu_regs: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_psci_x3: forall d a b, d {psci_x3: a} {cpu_regs: b} = d{cpu_regs: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {cpu_regs: b} = d{cpu_regs: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {cpu_regs: b} = d{cpu_regs: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {cpu_regs: b} = d{cpu_regs: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {cpu_regs: b} = d{cpu_regs: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {cpu_regs: b} = d{cpu_regs: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_target_rec: forall d a b, d {target_rec: a} {cpu_regs: b} = d{cpu_regs: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_el2_stack: forall d a b, d {el2_stack: a} {cpu_regs: b} = d{cpu_regs: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_el3_stack: forall d a b, d {el3_stack: a} {cpu_regs: b} = d{cpu_regs: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {cpu_regs: b} = d{cpu_regs: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {cpu_regs: b} = d{cpu_regs: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_cur_rec: forall d a b, d {cur_rec: a} {cpu_regs: b} = d{cpu_regs: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_mstage: forall d a b, d {mstage: a} {cpu_regs: b} = d{cpu_regs: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cpu_regs_trap_reason: forall d a b, d {trap_reason: a} {cpu_regs: b} = d{cpu_regs: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_id_regs: forall d a b, d {id_regs: a} {asm_regs: b} = d{asm_regs: b} {id_regs: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_buffer: forall d a b, d {buffer: a} {asm_regs: b} = d{asm_regs: b} {buffer: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_ns_regs_el2: forall d a b, d {ns_regs_el2: a} {asm_regs: b} = d{asm_regs: b} {ns_regs_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_realm_params: forall d a b, d {realm_params: a} {asm_regs: b} = d{asm_regs: b} {realm_params: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_rec_params: forall d a b, d {rec_params: a} {asm_regs: b} = d{asm_regs: b} {rec_params: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_rec_run: forall d a b, d {rec_run: a} {asm_regs: b} = d{asm_regs: b} {rec_run: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_retval: forall d a b, d {retval: a} {asm_regs: b} = d{asm_regs: b} {retval: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_locked_g: forall d a b, d {locked_g: a} {asm_regs: b} = d{asm_regs: b} {locked_g: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_wi_last_level: forall d a b, d {wi_last_level: a} {asm_regs: b} = d{asm_regs: b} {wi_last_level: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_wi_llt: forall d a b, d {wi_llt: a} {asm_regs: b} = d{asm_regs: b} {wi_llt: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_wi_index: forall d a b, d {wi_index: a} {asm_regs: b} = d{asm_regs: b} {wi_index: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_rvic_x0: forall d a b, d {rvic_x0: a} {asm_regs: b} = d{asm_regs: b} {rvic_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_rvic_x1: forall d a b, d {rvic_x1: a} {asm_regs: b} = d{asm_regs: b} {rvic_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_rvic_x2: forall d a b, d {rvic_x2: a} {asm_regs: b} = d{asm_regs: b} {rvic_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_rvic_x3: forall d a b, d {rvic_x3: a} {asm_regs: b} = d{asm_regs: b} {rvic_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_rvic_target: forall d a b, d {rvic_target: a} {asm_regs: b} = d{asm_regs: b} {rvic_target: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_rvic_ns_notify: forall d a b, d {rvic_ns_notify: a} {asm_regs: b} = d{asm_regs: b} {rvic_ns_notify: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_psci_x0: forall d a b, d {psci_x0: a} {asm_regs: b} = d{asm_regs: b} {psci_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_psci_x1: forall d a b, d {psci_x1: a} {asm_regs: b} = d{asm_regs: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_psci_x2: forall d a b, d {psci_x2: a} {asm_regs: b} = d{asm_regs: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_psci_x3: forall d a b, d {psci_x3: a} {asm_regs: b} = d{asm_regs: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {asm_regs: b} = d{asm_regs: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {asm_regs: b} = d{asm_regs: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {asm_regs: b} = d{asm_regs: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {asm_regs: b} = d{asm_regs: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {asm_regs: b} = d{asm_regs: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_target_rec: forall d a b, d {target_rec: a} {asm_regs: b} = d{asm_regs: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_el2_stack: forall d a b, d {el2_stack: a} {asm_regs: b} = d{asm_regs: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_el3_stack: forall d a b, d {el3_stack: a} {asm_regs: b} = d{asm_regs: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {asm_regs: b} = d{asm_regs: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {asm_regs: b} = d{asm_regs: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_cur_rec: forall d a b, d {cur_rec: a} {asm_regs: b} = d{asm_regs: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_mstage: forall d a b, d {mstage: a} {asm_regs: b} = d{asm_regs: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_asm_regs_trap_reason: forall d a b, d {trap_reason: a} {asm_regs: b} = d{asm_regs: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_buffer: forall d a b, d {buffer: a} {id_regs: b} = d{id_regs: b} {buffer: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_ns_regs_el2: forall d a b, d {ns_regs_el2: a} {id_regs: b} = d{id_regs: b} {ns_regs_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_realm_params: forall d a b, d {realm_params: a} {id_regs: b} = d{id_regs: b} {realm_params: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_rec_params: forall d a b, d {rec_params: a} {id_regs: b} = d{id_regs: b} {rec_params: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_rec_run: forall d a b, d {rec_run: a} {id_regs: b} = d{id_regs: b} {rec_run: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_retval: forall d a b, d {retval: a} {id_regs: b} = d{id_regs: b} {retval: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_locked_g: forall d a b, d {locked_g: a} {id_regs: b} = d{id_regs: b} {locked_g: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_wi_last_level: forall d a b, d {wi_last_level: a} {id_regs: b} = d{id_regs: b} {wi_last_level: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_wi_llt: forall d a b, d {wi_llt: a} {id_regs: b} = d{id_regs: b} {wi_llt: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_wi_index: forall d a b, d {wi_index: a} {id_regs: b} = d{id_regs: b} {wi_index: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_rvic_x0: forall d a b, d {rvic_x0: a} {id_regs: b} = d{id_regs: b} {rvic_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_rvic_x1: forall d a b, d {rvic_x1: a} {id_regs: b} = d{id_regs: b} {rvic_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_rvic_x2: forall d a b, d {rvic_x2: a} {id_regs: b} = d{id_regs: b} {rvic_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_rvic_x3: forall d a b, d {rvic_x3: a} {id_regs: b} = d{id_regs: b} {rvic_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_rvic_target: forall d a b, d {rvic_target: a} {id_regs: b} = d{id_regs: b} {rvic_target: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_rvic_ns_notify: forall d a b, d {rvic_ns_notify: a} {id_regs: b} = d{id_regs: b} {rvic_ns_notify: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_psci_x0: forall d a b, d {psci_x0: a} {id_regs: b} = d{id_regs: b} {psci_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_psci_x1: forall d a b, d {psci_x1: a} {id_regs: b} = d{id_regs: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_psci_x2: forall d a b, d {psci_x2: a} {id_regs: b} = d{id_regs: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_psci_x3: forall d a b, d {psci_x3: a} {id_regs: b} = d{id_regs: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {id_regs: b} = d{id_regs: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {id_regs: b} = d{id_regs: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {id_regs: b} = d{id_regs: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {id_regs: b} = d{id_regs: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {id_regs: b} = d{id_regs: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_target_rec: forall d a b, d {target_rec: a} {id_regs: b} = d{id_regs: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_el2_stack: forall d a b, d {el2_stack: a} {id_regs: b} = d{id_regs: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_el3_stack: forall d a b, d {el3_stack: a} {id_regs: b} = d{id_regs: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {id_regs: b} = d{id_regs: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {id_regs: b} = d{id_regs: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_cur_rec: forall d a b, d {cur_rec: a} {id_regs: b} = d{id_regs: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_mstage: forall d a b, d {mstage: a} {id_regs: b} = d{id_regs: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_id_regs_trap_reason: forall d a b, d {trap_reason: a} {id_regs: b} = d{id_regs: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_ns_regs_el2: forall d a b, d {ns_regs_el2: a} {buffer: b} = d{buffer: b} {ns_regs_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_realm_params: forall d a b, d {realm_params: a} {buffer: b} = d{buffer: b} {realm_params: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_rec_params: forall d a b, d {rec_params: a} {buffer: b} = d{buffer: b} {rec_params: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_rec_run: forall d a b, d {rec_run: a} {buffer: b} = d{buffer: b} {rec_run: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_retval: forall d a b, d {retval: a} {buffer: b} = d{buffer: b} {retval: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_locked_g: forall d a b, d {locked_g: a} {buffer: b} = d{buffer: b} {locked_g: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_wi_last_level: forall d a b, d {wi_last_level: a} {buffer: b} = d{buffer: b} {wi_last_level: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_wi_llt: forall d a b, d {wi_llt: a} {buffer: b} = d{buffer: b} {wi_llt: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_wi_index: forall d a b, d {wi_index: a} {buffer: b} = d{buffer: b} {wi_index: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_rvic_x0: forall d a b, d {rvic_x0: a} {buffer: b} = d{buffer: b} {rvic_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_rvic_x1: forall d a b, d {rvic_x1: a} {buffer: b} = d{buffer: b} {rvic_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_rvic_x2: forall d a b, d {rvic_x2: a} {buffer: b} = d{buffer: b} {rvic_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_rvic_x3: forall d a b, d {rvic_x3: a} {buffer: b} = d{buffer: b} {rvic_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_rvic_target: forall d a b, d {rvic_target: a} {buffer: b} = d{buffer: b} {rvic_target: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_rvic_ns_notify: forall d a b, d {rvic_ns_notify: a} {buffer: b} = d{buffer: b} {rvic_ns_notify: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_psci_x0: forall d a b, d {psci_x0: a} {buffer: b} = d{buffer: b} {psci_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_psci_x1: forall d a b, d {psci_x1: a} {buffer: b} = d{buffer: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_psci_x2: forall d a b, d {psci_x2: a} {buffer: b} = d{buffer: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_psci_x3: forall d a b, d {psci_x3: a} {buffer: b} = d{buffer: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {buffer: b} = d{buffer: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {buffer: b} = d{buffer: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {buffer: b} = d{buffer: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {buffer: b} = d{buffer: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {buffer: b} = d{buffer: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_target_rec: forall d a b, d {target_rec: a} {buffer: b} = d{buffer: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_el2_stack: forall d a b, d {el2_stack: a} {buffer: b} = d{buffer: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_el3_stack: forall d a b, d {el3_stack: a} {buffer: b} = d{buffer: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {buffer: b} = d{buffer: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {buffer: b} = d{buffer: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_cur_rec: forall d a b, d {cur_rec: a} {buffer: b} = d{buffer: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_mstage: forall d a b, d {mstage: a} {buffer: b} = d{buffer: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_buffer_trap_reason: forall d a b, d {trap_reason: a} {buffer: b} = d{buffer: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_realm_params: forall d a b, d {realm_params: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {realm_params: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_rec_params: forall d a b, d {rec_params: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {rec_params: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_rec_run: forall d a b, d {rec_run: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {rec_run: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_retval: forall d a b, d {retval: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {retval: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_locked_g: forall d a b, d {locked_g: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {locked_g: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_wi_last_level: forall d a b, d {wi_last_level: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {wi_last_level: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_wi_llt: forall d a b, d {wi_llt: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {wi_llt: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_wi_index: forall d a b, d {wi_index: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {wi_index: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_rvic_x0: forall d a b, d {rvic_x0: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {rvic_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_rvic_x1: forall d a b, d {rvic_x1: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {rvic_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_rvic_x2: forall d a b, d {rvic_x2: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {rvic_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_rvic_x3: forall d a b, d {rvic_x3: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {rvic_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_rvic_target: forall d a b, d {rvic_target: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {rvic_target: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_rvic_ns_notify: forall d a b, d {rvic_ns_notify: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {rvic_ns_notify: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_psci_x0: forall d a b, d {psci_x0: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {psci_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_psci_x1: forall d a b, d {psci_x1: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_psci_x2: forall d a b, d {psci_x2: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_psci_x3: forall d a b, d {psci_x3: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_target_rec: forall d a b, d {target_rec: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_el2_stack: forall d a b, d {el2_stack: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_el3_stack: forall d a b, d {el3_stack: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_cur_rec: forall d a b, d {cur_rec: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_mstage: forall d a b, d {mstage: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el2_trap_reason: forall d a b, d {trap_reason: a} {ns_regs_el2: b} = d{ns_regs_el2: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_rec_params: forall d a b, d {rec_params: a} {realm_params: b} = d{realm_params: b} {rec_params: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_rec_run: forall d a b, d {rec_run: a} {realm_params: b} = d{realm_params: b} {rec_run: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_retval: forall d a b, d {retval: a} {realm_params: b} = d{realm_params: b} {retval: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_locked_g: forall d a b, d {locked_g: a} {realm_params: b} = d{realm_params: b} {locked_g: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_wi_last_level: forall d a b, d {wi_last_level: a} {realm_params: b} = d{realm_params: b} {wi_last_level: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_wi_llt: forall d a b, d {wi_llt: a} {realm_params: b} = d{realm_params: b} {wi_llt: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_wi_index: forall d a b, d {wi_index: a} {realm_params: b} = d{realm_params: b} {wi_index: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_rvic_x0: forall d a b, d {rvic_x0: a} {realm_params: b} = d{realm_params: b} {rvic_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_rvic_x1: forall d a b, d {rvic_x1: a} {realm_params: b} = d{realm_params: b} {rvic_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_rvic_x2: forall d a b, d {rvic_x2: a} {realm_params: b} = d{realm_params: b} {rvic_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_rvic_x3: forall d a b, d {rvic_x3: a} {realm_params: b} = d{realm_params: b} {rvic_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_rvic_target: forall d a b, d {rvic_target: a} {realm_params: b} = d{realm_params: b} {rvic_target: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_rvic_ns_notify: forall d a b, d {rvic_ns_notify: a} {realm_params: b} = d{realm_params: b} {rvic_ns_notify: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_psci_x0: forall d a b, d {psci_x0: a} {realm_params: b} = d{realm_params: b} {psci_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_psci_x1: forall d a b, d {psci_x1: a} {realm_params: b} = d{realm_params: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_psci_x2: forall d a b, d {psci_x2: a} {realm_params: b} = d{realm_params: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_psci_x3: forall d a b, d {psci_x3: a} {realm_params: b} = d{realm_params: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {realm_params: b} = d{realm_params: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {realm_params: b} = d{realm_params: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {realm_params: b} = d{realm_params: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {realm_params: b} = d{realm_params: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {realm_params: b} = d{realm_params: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_target_rec: forall d a b, d {target_rec: a} {realm_params: b} = d{realm_params: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_el2_stack: forall d a b, d {el2_stack: a} {realm_params: b} = d{realm_params: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_el3_stack: forall d a b, d {el3_stack: a} {realm_params: b} = d{realm_params: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {realm_params: b} = d{realm_params: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {realm_params: b} = d{realm_params: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_cur_rec: forall d a b, d {cur_rec: a} {realm_params: b} = d{realm_params: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_mstage: forall d a b, d {mstage: a} {realm_params: b} = d{realm_params: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_params_trap_reason: forall d a b, d {trap_reason: a} {realm_params: b} = d{realm_params: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_rec_run: forall d a b, d {rec_run: a} {rec_params: b} = d{rec_params: b} {rec_run: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_retval: forall d a b, d {retval: a} {rec_params: b} = d{rec_params: b} {retval: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_locked_g: forall d a b, d {locked_g: a} {rec_params: b} = d{rec_params: b} {locked_g: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_wi_last_level: forall d a b, d {wi_last_level: a} {rec_params: b} = d{rec_params: b} {wi_last_level: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_wi_llt: forall d a b, d {wi_llt: a} {rec_params: b} = d{rec_params: b} {wi_llt: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_wi_index: forall d a b, d {wi_index: a} {rec_params: b} = d{rec_params: b} {wi_index: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_rvic_x0: forall d a b, d {rvic_x0: a} {rec_params: b} = d{rec_params: b} {rvic_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_rvic_x1: forall d a b, d {rvic_x1: a} {rec_params: b} = d{rec_params: b} {rvic_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_rvic_x2: forall d a b, d {rvic_x2: a} {rec_params: b} = d{rec_params: b} {rvic_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_rvic_x3: forall d a b, d {rvic_x3: a} {rec_params: b} = d{rec_params: b} {rvic_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_rvic_target: forall d a b, d {rvic_target: a} {rec_params: b} = d{rec_params: b} {rvic_target: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_rvic_ns_notify: forall d a b, d {rvic_ns_notify: a} {rec_params: b} = d{rec_params: b} {rvic_ns_notify: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_psci_x0: forall d a b, d {psci_x0: a} {rec_params: b} = d{rec_params: b} {psci_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_psci_x1: forall d a b, d {psci_x1: a} {rec_params: b} = d{rec_params: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_psci_x2: forall d a b, d {psci_x2: a} {rec_params: b} = d{rec_params: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_psci_x3: forall d a b, d {psci_x3: a} {rec_params: b} = d{rec_params: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {rec_params: b} = d{rec_params: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {rec_params: b} = d{rec_params: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {rec_params: b} = d{rec_params: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {rec_params: b} = d{rec_params: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {rec_params: b} = d{rec_params: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_target_rec: forall d a b, d {target_rec: a} {rec_params: b} = d{rec_params: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_el2_stack: forall d a b, d {el2_stack: a} {rec_params: b} = d{rec_params: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_el3_stack: forall d a b, d {el3_stack: a} {rec_params: b} = d{rec_params: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {rec_params: b} = d{rec_params: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {rec_params: b} = d{rec_params: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_cur_rec: forall d a b, d {cur_rec: a} {rec_params: b} = d{rec_params: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_mstage: forall d a b, d {mstage: a} {rec_params: b} = d{rec_params: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_params_trap_reason: forall d a b, d {trap_reason: a} {rec_params: b} = d{rec_params: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_retval: forall d a b, d {retval: a} {rec_run: b} = d{rec_run: b} {retval: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_locked_g: forall d a b, d {locked_g: a} {rec_run: b} = d{rec_run: b} {locked_g: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_wi_last_level: forall d a b, d {wi_last_level: a} {rec_run: b} = d{rec_run: b} {wi_last_level: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_wi_llt: forall d a b, d {wi_llt: a} {rec_run: b} = d{rec_run: b} {wi_llt: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_wi_index: forall d a b, d {wi_index: a} {rec_run: b} = d{rec_run: b} {wi_index: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_rvic_x0: forall d a b, d {rvic_x0: a} {rec_run: b} = d{rec_run: b} {rvic_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_rvic_x1: forall d a b, d {rvic_x1: a} {rec_run: b} = d{rec_run: b} {rvic_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_rvic_x2: forall d a b, d {rvic_x2: a} {rec_run: b} = d{rec_run: b} {rvic_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_rvic_x3: forall d a b, d {rvic_x3: a} {rec_run: b} = d{rec_run: b} {rvic_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_rvic_target: forall d a b, d {rvic_target: a} {rec_run: b} = d{rec_run: b} {rvic_target: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_rvic_ns_notify: forall d a b, d {rvic_ns_notify: a} {rec_run: b} = d{rec_run: b} {rvic_ns_notify: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_psci_x0: forall d a b, d {psci_x0: a} {rec_run: b} = d{rec_run: b} {psci_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_psci_x1: forall d a b, d {psci_x1: a} {rec_run: b} = d{rec_run: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_psci_x2: forall d a b, d {psci_x2: a} {rec_run: b} = d{rec_run: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_psci_x3: forall d a b, d {psci_x3: a} {rec_run: b} = d{rec_run: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {rec_run: b} = d{rec_run: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {rec_run: b} = d{rec_run: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {rec_run: b} = d{rec_run: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {rec_run: b} = d{rec_run: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {rec_run: b} = d{rec_run: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_target_rec: forall d a b, d {target_rec: a} {rec_run: b} = d{rec_run: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_el2_stack: forall d a b, d {el2_stack: a} {rec_run: b} = d{rec_run: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_el3_stack: forall d a b, d {el3_stack: a} {rec_run: b} = d{rec_run: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {rec_run: b} = d{rec_run: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {rec_run: b} = d{rec_run: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_cur_rec: forall d a b, d {cur_rec: a} {rec_run: b} = d{rec_run: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_mstage: forall d a b, d {mstage: a} {rec_run: b} = d{rec_run: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rec_run_trap_reason: forall d a b, d {trap_reason: a} {rec_run: b} = d{rec_run: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_locked_g: forall d a b, d {locked_g: a} {retval: b} = d{retval: b} {locked_g: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_wi_last_level: forall d a b, d {wi_last_level: a} {retval: b} = d{retval: b} {wi_last_level: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_wi_llt: forall d a b, d {wi_llt: a} {retval: b} = d{retval: b} {wi_llt: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_wi_index: forall d a b, d {wi_index: a} {retval: b} = d{retval: b} {wi_index: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_rvic_x0: forall d a b, d {rvic_x0: a} {retval: b} = d{retval: b} {rvic_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_rvic_x1: forall d a b, d {rvic_x1: a} {retval: b} = d{retval: b} {rvic_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_rvic_x2: forall d a b, d {rvic_x2: a} {retval: b} = d{retval: b} {rvic_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_rvic_x3: forall d a b, d {rvic_x3: a} {retval: b} = d{retval: b} {rvic_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_rvic_target: forall d a b, d {rvic_target: a} {retval: b} = d{retval: b} {rvic_target: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_rvic_ns_notify: forall d a b, d {rvic_ns_notify: a} {retval: b} = d{retval: b} {rvic_ns_notify: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_psci_x0: forall d a b, d {psci_x0: a} {retval: b} = d{retval: b} {psci_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_psci_x1: forall d a b, d {psci_x1: a} {retval: b} = d{retval: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_psci_x2: forall d a b, d {psci_x2: a} {retval: b} = d{retval: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_psci_x3: forall d a b, d {psci_x3: a} {retval: b} = d{retval: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {retval: b} = d{retval: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {retval: b} = d{retval: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {retval: b} = d{retval: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {retval: b} = d{retval: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {retval: b} = d{retval: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_target_rec: forall d a b, d {target_rec: a} {retval: b} = d{retval: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_el2_stack: forall d a b, d {el2_stack: a} {retval: b} = d{retval: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_el3_stack: forall d a b, d {el3_stack: a} {retval: b} = d{retval: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {retval: b} = d{retval: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {retval: b} = d{retval: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_cur_rec: forall d a b, d {cur_rec: a} {retval: b} = d{retval: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_mstage: forall d a b, d {mstage: a} {retval: b} = d{retval: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_retval_trap_reason: forall d a b, d {trap_reason: a} {retval: b} = d{retval: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_wi_last_level: forall d a b, d {wi_last_level: a} {locked_g: b} = d{locked_g: b} {wi_last_level: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_wi_llt: forall d a b, d {wi_llt: a} {locked_g: b} = d{locked_g: b} {wi_llt: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_wi_index: forall d a b, d {wi_index: a} {locked_g: b} = d{locked_g: b} {wi_index: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_rvic_x0: forall d a b, d {rvic_x0: a} {locked_g: b} = d{locked_g: b} {rvic_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_rvic_x1: forall d a b, d {rvic_x1: a} {locked_g: b} = d{locked_g: b} {rvic_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_rvic_x2: forall d a b, d {rvic_x2: a} {locked_g: b} = d{locked_g: b} {rvic_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_rvic_x3: forall d a b, d {rvic_x3: a} {locked_g: b} = d{locked_g: b} {rvic_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_rvic_target: forall d a b, d {rvic_target: a} {locked_g: b} = d{locked_g: b} {rvic_target: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_rvic_ns_notify: forall d a b, d {rvic_ns_notify: a} {locked_g: b} = d{locked_g: b} {rvic_ns_notify: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_psci_x0: forall d a b, d {psci_x0: a} {locked_g: b} = d{locked_g: b} {psci_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_psci_x1: forall d a b, d {psci_x1: a} {locked_g: b} = d{locked_g: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_psci_x2: forall d a b, d {psci_x2: a} {locked_g: b} = d{locked_g: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_psci_x3: forall d a b, d {psci_x3: a} {locked_g: b} = d{locked_g: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {locked_g: b} = d{locked_g: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {locked_g: b} = d{locked_g: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {locked_g: b} = d{locked_g: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {locked_g: b} = d{locked_g: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {locked_g: b} = d{locked_g: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_target_rec: forall d a b, d {target_rec: a} {locked_g: b} = d{locked_g: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_el2_stack: forall d a b, d {el2_stack: a} {locked_g: b} = d{locked_g: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_el3_stack: forall d a b, d {el3_stack: a} {locked_g: b} = d{locked_g: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {locked_g: b} = d{locked_g: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {locked_g: b} = d{locked_g: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_cur_rec: forall d a b, d {cur_rec: a} {locked_g: b} = d{locked_g: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_mstage: forall d a b, d {mstage: a} {locked_g: b} = d{locked_g: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_locked_g_trap_reason: forall d a b, d {trap_reason: a} {locked_g: b} = d{locked_g: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_wi_llt: forall d a b, d {wi_llt: a} {wi_last_level: b} = d{wi_last_level: b} {wi_llt: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_wi_index: forall d a b, d {wi_index: a} {wi_last_level: b} = d{wi_last_level: b} {wi_index: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_rvic_x0: forall d a b, d {rvic_x0: a} {wi_last_level: b} = d{wi_last_level: b} {rvic_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_rvic_x1: forall d a b, d {rvic_x1: a} {wi_last_level: b} = d{wi_last_level: b} {rvic_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_rvic_x2: forall d a b, d {rvic_x2: a} {wi_last_level: b} = d{wi_last_level: b} {rvic_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_rvic_x3: forall d a b, d {rvic_x3: a} {wi_last_level: b} = d{wi_last_level: b} {rvic_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_rvic_target: forall d a b, d {rvic_target: a} {wi_last_level: b} = d{wi_last_level: b} {rvic_target: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_rvic_ns_notify: forall d a b, d {rvic_ns_notify: a} {wi_last_level: b} = d{wi_last_level: b} {rvic_ns_notify: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_psci_x0: forall d a b, d {psci_x0: a} {wi_last_level: b} = d{wi_last_level: b} {psci_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_psci_x1: forall d a b, d {psci_x1: a} {wi_last_level: b} = d{wi_last_level: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_psci_x2: forall d a b, d {psci_x2: a} {wi_last_level: b} = d{wi_last_level: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_psci_x3: forall d a b, d {psci_x3: a} {wi_last_level: b} = d{wi_last_level: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {wi_last_level: b} = d{wi_last_level: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {wi_last_level: b} = d{wi_last_level: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {wi_last_level: b} = d{wi_last_level: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {wi_last_level: b} = d{wi_last_level: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {wi_last_level: b} = d{wi_last_level: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_target_rec: forall d a b, d {target_rec: a} {wi_last_level: b} = d{wi_last_level: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_el2_stack: forall d a b, d {el2_stack: a} {wi_last_level: b} = d{wi_last_level: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_el3_stack: forall d a b, d {el3_stack: a} {wi_last_level: b} = d{wi_last_level: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {wi_last_level: b} = d{wi_last_level: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {wi_last_level: b} = d{wi_last_level: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_cur_rec: forall d a b, d {cur_rec: a} {wi_last_level: b} = d{wi_last_level: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_mstage: forall d a b, d {mstage: a} {wi_last_level: b} = d{wi_last_level: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_last_level_trap_reason: forall d a b, d {trap_reason: a} {wi_last_level: b} = d{wi_last_level: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_wi_index: forall d a b, d {wi_index: a} {wi_llt: b} = d{wi_llt: b} {wi_index: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_rvic_x0: forall d a b, d {rvic_x0: a} {wi_llt: b} = d{wi_llt: b} {rvic_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_rvic_x1: forall d a b, d {rvic_x1: a} {wi_llt: b} = d{wi_llt: b} {rvic_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_rvic_x2: forall d a b, d {rvic_x2: a} {wi_llt: b} = d{wi_llt: b} {rvic_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_rvic_x3: forall d a b, d {rvic_x3: a} {wi_llt: b} = d{wi_llt: b} {rvic_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_rvic_target: forall d a b, d {rvic_target: a} {wi_llt: b} = d{wi_llt: b} {rvic_target: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_rvic_ns_notify: forall d a b, d {rvic_ns_notify: a} {wi_llt: b} = d{wi_llt: b} {rvic_ns_notify: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_psci_x0: forall d a b, d {psci_x0: a} {wi_llt: b} = d{wi_llt: b} {psci_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_psci_x1: forall d a b, d {psci_x1: a} {wi_llt: b} = d{wi_llt: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_psci_x2: forall d a b, d {psci_x2: a} {wi_llt: b} = d{wi_llt: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_psci_x3: forall d a b, d {psci_x3: a} {wi_llt: b} = d{wi_llt: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {wi_llt: b} = d{wi_llt: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {wi_llt: b} = d{wi_llt: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {wi_llt: b} = d{wi_llt: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {wi_llt: b} = d{wi_llt: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {wi_llt: b} = d{wi_llt: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_target_rec: forall d a b, d {target_rec: a} {wi_llt: b} = d{wi_llt: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_el2_stack: forall d a b, d {el2_stack: a} {wi_llt: b} = d{wi_llt: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_el3_stack: forall d a b, d {el3_stack: a} {wi_llt: b} = d{wi_llt: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {wi_llt: b} = d{wi_llt: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {wi_llt: b} = d{wi_llt: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_cur_rec: forall d a b, d {cur_rec: a} {wi_llt: b} = d{wi_llt: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_mstage: forall d a b, d {mstage: a} {wi_llt: b} = d{wi_llt: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_llt_trap_reason: forall d a b, d {trap_reason: a} {wi_llt: b} = d{wi_llt: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_rvic_x0: forall d a b, d {rvic_x0: a} {wi_index: b} = d{wi_index: b} {rvic_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_rvic_x1: forall d a b, d {rvic_x1: a} {wi_index: b} = d{wi_index: b} {rvic_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_rvic_x2: forall d a b, d {rvic_x2: a} {wi_index: b} = d{wi_index: b} {rvic_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_rvic_x3: forall d a b, d {rvic_x3: a} {wi_index: b} = d{wi_index: b} {rvic_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_rvic_target: forall d a b, d {rvic_target: a} {wi_index: b} = d{wi_index: b} {rvic_target: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_rvic_ns_notify: forall d a b, d {rvic_ns_notify: a} {wi_index: b} = d{wi_index: b} {rvic_ns_notify: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_psci_x0: forall d a b, d {psci_x0: a} {wi_index: b} = d{wi_index: b} {psci_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_psci_x1: forall d a b, d {psci_x1: a} {wi_index: b} = d{wi_index: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_psci_x2: forall d a b, d {psci_x2: a} {wi_index: b} = d{wi_index: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_psci_x3: forall d a b, d {psci_x3: a} {wi_index: b} = d{wi_index: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {wi_index: b} = d{wi_index: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {wi_index: b} = d{wi_index: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {wi_index: b} = d{wi_index: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {wi_index: b} = d{wi_index: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {wi_index: b} = d{wi_index: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_target_rec: forall d a b, d {target_rec: a} {wi_index: b} = d{wi_index: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_el2_stack: forall d a b, d {el2_stack: a} {wi_index: b} = d{wi_index: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_el3_stack: forall d a b, d {el3_stack: a} {wi_index: b} = d{wi_index: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {wi_index: b} = d{wi_index: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {wi_index: b} = d{wi_index: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_cur_rec: forall d a b, d {cur_rec: a} {wi_index: b} = d{wi_index: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_mstage: forall d a b, d {mstage: a} {wi_index: b} = d{wi_index: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_wi_index_trap_reason: forall d a b, d {trap_reason: a} {wi_index: b} = d{wi_index: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_rvic_x1: forall d a b, d {rvic_x1: a} {rvic_x0: b} = d{rvic_x0: b} {rvic_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_rvic_x2: forall d a b, d {rvic_x2: a} {rvic_x0: b} = d{rvic_x0: b} {rvic_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_rvic_x3: forall d a b, d {rvic_x3: a} {rvic_x0: b} = d{rvic_x0: b} {rvic_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_rvic_target: forall d a b, d {rvic_target: a} {rvic_x0: b} = d{rvic_x0: b} {rvic_target: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_rvic_ns_notify: forall d a b, d {rvic_ns_notify: a} {rvic_x0: b} = d{rvic_x0: b} {rvic_ns_notify: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_psci_x0: forall d a b, d {psci_x0: a} {rvic_x0: b} = d{rvic_x0: b} {psci_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_psci_x1: forall d a b, d {psci_x1: a} {rvic_x0: b} = d{rvic_x0: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_psci_x2: forall d a b, d {psci_x2: a} {rvic_x0: b} = d{rvic_x0: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_psci_x3: forall d a b, d {psci_x3: a} {rvic_x0: b} = d{rvic_x0: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {rvic_x0: b} = d{rvic_x0: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {rvic_x0: b} = d{rvic_x0: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {rvic_x0: b} = d{rvic_x0: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {rvic_x0: b} = d{rvic_x0: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {rvic_x0: b} = d{rvic_x0: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_target_rec: forall d a b, d {target_rec: a} {rvic_x0: b} = d{rvic_x0: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_el2_stack: forall d a b, d {el2_stack: a} {rvic_x0: b} = d{rvic_x0: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_el3_stack: forall d a b, d {el3_stack: a} {rvic_x0: b} = d{rvic_x0: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {rvic_x0: b} = d{rvic_x0: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {rvic_x0: b} = d{rvic_x0: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_cur_rec: forall d a b, d {cur_rec: a} {rvic_x0: b} = d{rvic_x0: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_mstage: forall d a b, d {mstage: a} {rvic_x0: b} = d{rvic_x0: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x0_trap_reason: forall d a b, d {trap_reason: a} {rvic_x0: b} = d{rvic_x0: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_rvic_x2: forall d a b, d {rvic_x2: a} {rvic_x1: b} = d{rvic_x1: b} {rvic_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_rvic_x3: forall d a b, d {rvic_x3: a} {rvic_x1: b} = d{rvic_x1: b} {rvic_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_rvic_target: forall d a b, d {rvic_target: a} {rvic_x1: b} = d{rvic_x1: b} {rvic_target: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_rvic_ns_notify: forall d a b, d {rvic_ns_notify: a} {rvic_x1: b} = d{rvic_x1: b} {rvic_ns_notify: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_psci_x0: forall d a b, d {psci_x0: a} {rvic_x1: b} = d{rvic_x1: b} {psci_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_psci_x1: forall d a b, d {psci_x1: a} {rvic_x1: b} = d{rvic_x1: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_psci_x2: forall d a b, d {psci_x2: a} {rvic_x1: b} = d{rvic_x1: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_psci_x3: forall d a b, d {psci_x3: a} {rvic_x1: b} = d{rvic_x1: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {rvic_x1: b} = d{rvic_x1: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {rvic_x1: b} = d{rvic_x1: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {rvic_x1: b} = d{rvic_x1: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {rvic_x1: b} = d{rvic_x1: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {rvic_x1: b} = d{rvic_x1: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_target_rec: forall d a b, d {target_rec: a} {rvic_x1: b} = d{rvic_x1: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_el2_stack: forall d a b, d {el2_stack: a} {rvic_x1: b} = d{rvic_x1: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_el3_stack: forall d a b, d {el3_stack: a} {rvic_x1: b} = d{rvic_x1: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {rvic_x1: b} = d{rvic_x1: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {rvic_x1: b} = d{rvic_x1: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_cur_rec: forall d a b, d {cur_rec: a} {rvic_x1: b} = d{rvic_x1: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_mstage: forall d a b, d {mstage: a} {rvic_x1: b} = d{rvic_x1: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x1_trap_reason: forall d a b, d {trap_reason: a} {rvic_x1: b} = d{rvic_x1: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_rvic_x3: forall d a b, d {rvic_x3: a} {rvic_x2: b} = d{rvic_x2: b} {rvic_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_rvic_target: forall d a b, d {rvic_target: a} {rvic_x2: b} = d{rvic_x2: b} {rvic_target: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_rvic_ns_notify: forall d a b, d {rvic_ns_notify: a} {rvic_x2: b} = d{rvic_x2: b} {rvic_ns_notify: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_psci_x0: forall d a b, d {psci_x0: a} {rvic_x2: b} = d{rvic_x2: b} {psci_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_psci_x1: forall d a b, d {psci_x1: a} {rvic_x2: b} = d{rvic_x2: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_psci_x2: forall d a b, d {psci_x2: a} {rvic_x2: b} = d{rvic_x2: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_psci_x3: forall d a b, d {psci_x3: a} {rvic_x2: b} = d{rvic_x2: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {rvic_x2: b} = d{rvic_x2: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {rvic_x2: b} = d{rvic_x2: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {rvic_x2: b} = d{rvic_x2: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {rvic_x2: b} = d{rvic_x2: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {rvic_x2: b} = d{rvic_x2: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_target_rec: forall d a b, d {target_rec: a} {rvic_x2: b} = d{rvic_x2: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_el2_stack: forall d a b, d {el2_stack: a} {rvic_x2: b} = d{rvic_x2: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_el3_stack: forall d a b, d {el3_stack: a} {rvic_x2: b} = d{rvic_x2: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {rvic_x2: b} = d{rvic_x2: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {rvic_x2: b} = d{rvic_x2: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_cur_rec: forall d a b, d {cur_rec: a} {rvic_x2: b} = d{rvic_x2: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_mstage: forall d a b, d {mstage: a} {rvic_x2: b} = d{rvic_x2: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x2_trap_reason: forall d a b, d {trap_reason: a} {rvic_x2: b} = d{rvic_x2: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x3_rvic_target: forall d a b, d {rvic_target: a} {rvic_x3: b} = d{rvic_x3: b} {rvic_target: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x3_rvic_ns_notify: forall d a b, d {rvic_ns_notify: a} {rvic_x3: b} = d{rvic_x3: b} {rvic_ns_notify: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x3_psci_x0: forall d a b, d {psci_x0: a} {rvic_x3: b} = d{rvic_x3: b} {psci_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x3_psci_x1: forall d a b, d {psci_x1: a} {rvic_x3: b} = d{rvic_x3: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x3_psci_x2: forall d a b, d {psci_x2: a} {rvic_x3: b} = d{rvic_x3: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x3_psci_x3: forall d a b, d {psci_x3: a} {rvic_x3: b} = d{rvic_x3: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x3_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {rvic_x3: b} = d{rvic_x3: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x3_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {rvic_x3: b} = d{rvic_x3: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x3_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {rvic_x3: b} = d{rvic_x3: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x3_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {rvic_x3: b} = d{rvic_x3: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x3_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {rvic_x3: b} = d{rvic_x3: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x3_target_rec: forall d a b, d {target_rec: a} {rvic_x3: b} = d{rvic_x3: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x3_el2_stack: forall d a b, d {el2_stack: a} {rvic_x3: b} = d{rvic_x3: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x3_el3_stack: forall d a b, d {el3_stack: a} {rvic_x3: b} = d{rvic_x3: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x3_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {rvic_x3: b} = d{rvic_x3: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x3_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {rvic_x3: b} = d{rvic_x3: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x3_cur_rec: forall d a b, d {cur_rec: a} {rvic_x3: b} = d{rvic_x3: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x3_mstage: forall d a b, d {mstage: a} {rvic_x3: b} = d{rvic_x3: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_x3_trap_reason: forall d a b, d {trap_reason: a} {rvic_x3: b} = d{rvic_x3: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_target_rvic_ns_notify: forall d a b, d {rvic_ns_notify: a} {rvic_target: b} = d{rvic_target: b} {rvic_ns_notify: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_target_psci_x0: forall d a b, d {psci_x0: a} {rvic_target: b} = d{rvic_target: b} {psci_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_target_psci_x1: forall d a b, d {psci_x1: a} {rvic_target: b} = d{rvic_target: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_target_psci_x2: forall d a b, d {psci_x2: a} {rvic_target: b} = d{rvic_target: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_target_psci_x3: forall d a b, d {psci_x3: a} {rvic_target: b} = d{rvic_target: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_target_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {rvic_target: b} = d{rvic_target: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_target_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {rvic_target: b} = d{rvic_target: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_target_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {rvic_target: b} = d{rvic_target: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_target_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {rvic_target: b} = d{rvic_target: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_target_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {rvic_target: b} = d{rvic_target: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_target_target_rec: forall d a b, d {target_rec: a} {rvic_target: b} = d{rvic_target: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_target_el2_stack: forall d a b, d {el2_stack: a} {rvic_target: b} = d{rvic_target: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_target_el3_stack: forall d a b, d {el3_stack: a} {rvic_target: b} = d{rvic_target: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_target_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {rvic_target: b} = d{rvic_target: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_target_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {rvic_target: b} = d{rvic_target: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_target_cur_rec: forall d a b, d {cur_rec: a} {rvic_target: b} = d{rvic_target: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_target_mstage: forall d a b, d {mstage: a} {rvic_target: b} = d{rvic_target: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_target_trap_reason: forall d a b, d {trap_reason: a} {rvic_target: b} = d{rvic_target: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_ns_notify_psci_x0: forall d a b, d {psci_x0: a} {rvic_ns_notify: b} = d{rvic_ns_notify: b} {psci_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_ns_notify_psci_x1: forall d a b, d {psci_x1: a} {rvic_ns_notify: b} = d{rvic_ns_notify: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_ns_notify_psci_x2: forall d a b, d {psci_x2: a} {rvic_ns_notify: b} = d{rvic_ns_notify: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_ns_notify_psci_x3: forall d a b, d {psci_x3: a} {rvic_ns_notify: b} = d{rvic_ns_notify: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_ns_notify_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {rvic_ns_notify: b} = d{rvic_ns_notify: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_ns_notify_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {rvic_ns_notify: b} = d{rvic_ns_notify: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_ns_notify_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {rvic_ns_notify: b} = d{rvic_ns_notify: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_ns_notify_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {rvic_ns_notify: b} = d{rvic_ns_notify: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_ns_notify_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {rvic_ns_notify: b} = d{rvic_ns_notify: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_ns_notify_target_rec: forall d a b, d {target_rec: a} {rvic_ns_notify: b} = d{rvic_ns_notify: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_ns_notify_el2_stack: forall d a b, d {el2_stack: a} {rvic_ns_notify: b} = d{rvic_ns_notify: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_ns_notify_el3_stack: forall d a b, d {el3_stack: a} {rvic_ns_notify: b} = d{rvic_ns_notify: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_ns_notify_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {rvic_ns_notify: b} = d{rvic_ns_notify: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_ns_notify_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {rvic_ns_notify: b} = d{rvic_ns_notify: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_ns_notify_cur_rec: forall d a b, d {cur_rec: a} {rvic_ns_notify: b} = d{rvic_ns_notify: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_ns_notify_mstage: forall d a b, d {mstage: a} {rvic_ns_notify: b} = d{rvic_ns_notify: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rvic_ns_notify_trap_reason: forall d a b, d {trap_reason: a} {rvic_ns_notify: b} = d{rvic_ns_notify: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x0_psci_x1: forall d a b, d {psci_x1: a} {psci_x0: b} = d{psci_x0: b} {psci_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x0_psci_x2: forall d a b, d {psci_x2: a} {psci_x0: b} = d{psci_x0: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x0_psci_x3: forall d a b, d {psci_x3: a} {psci_x0: b} = d{psci_x0: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x0_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {psci_x0: b} = d{psci_x0: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x0_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {psci_x0: b} = d{psci_x0: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x0_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {psci_x0: b} = d{psci_x0: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x0_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {psci_x0: b} = d{psci_x0: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x0_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {psci_x0: b} = d{psci_x0: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x0_target_rec: forall d a b, d {target_rec: a} {psci_x0: b} = d{psci_x0: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x0_el2_stack: forall d a b, d {el2_stack: a} {psci_x0: b} = d{psci_x0: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x0_el3_stack: forall d a b, d {el3_stack: a} {psci_x0: b} = d{psci_x0: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x0_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {psci_x0: b} = d{psci_x0: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x0_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {psci_x0: b} = d{psci_x0: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x0_cur_rec: forall d a b, d {cur_rec: a} {psci_x0: b} = d{psci_x0: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x0_mstage: forall d a b, d {mstage: a} {psci_x0: b} = d{psci_x0: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x0_trap_reason: forall d a b, d {trap_reason: a} {psci_x0: b} = d{psci_x0: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x1_psci_x2: forall d a b, d {psci_x2: a} {psci_x1: b} = d{psci_x1: b} {psci_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x1_psci_x3: forall d a b, d {psci_x3: a} {psci_x1: b} = d{psci_x1: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x1_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {psci_x1: b} = d{psci_x1: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x1_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {psci_x1: b} = d{psci_x1: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x1_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {psci_x1: b} = d{psci_x1: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x1_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {psci_x1: b} = d{psci_x1: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x1_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {psci_x1: b} = d{psci_x1: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x1_target_rec: forall d a b, d {target_rec: a} {psci_x1: b} = d{psci_x1: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x1_el2_stack: forall d a b, d {el2_stack: a} {psci_x1: b} = d{psci_x1: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x1_el3_stack: forall d a b, d {el3_stack: a} {psci_x1: b} = d{psci_x1: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x1_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {psci_x1: b} = d{psci_x1: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x1_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {psci_x1: b} = d{psci_x1: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x1_cur_rec: forall d a b, d {cur_rec: a} {psci_x1: b} = d{psci_x1: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x1_mstage: forall d a b, d {mstage: a} {psci_x1: b} = d{psci_x1: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x1_trap_reason: forall d a b, d {trap_reason: a} {psci_x1: b} = d{psci_x1: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x2_psci_x3: forall d a b, d {psci_x3: a} {psci_x2: b} = d{psci_x2: b} {psci_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x2_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {psci_x2: b} = d{psci_x2: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x2_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {psci_x2: b} = d{psci_x2: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x2_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {psci_x2: b} = d{psci_x2: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x2_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {psci_x2: b} = d{psci_x2: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x2_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {psci_x2: b} = d{psci_x2: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x2_target_rec: forall d a b, d {target_rec: a} {psci_x2: b} = d{psci_x2: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x2_el2_stack: forall d a b, d {el2_stack: a} {psci_x2: b} = d{psci_x2: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x2_el3_stack: forall d a b, d {el3_stack: a} {psci_x2: b} = d{psci_x2: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x2_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {psci_x2: b} = d{psci_x2: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x2_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {psci_x2: b} = d{psci_x2: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x2_cur_rec: forall d a b, d {cur_rec: a} {psci_x2: b} = d{psci_x2: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x2_mstage: forall d a b, d {mstage: a} {psci_x2: b} = d{psci_x2: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x2_trap_reason: forall d a b, d {trap_reason: a} {psci_x2: b} = d{psci_x2: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x3_psci_forward_x0: forall d a b, d {psci_forward_x0: a} {psci_x3: b} = d{psci_x3: b} {psci_forward_x0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x3_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {psci_x3: b} = d{psci_x3: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x3_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {psci_x3: b} = d{psci_x3: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x3_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {psci_x3: b} = d{psci_x3: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x3_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {psci_x3: b} = d{psci_x3: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x3_target_rec: forall d a b, d {target_rec: a} {psci_x3: b} = d{psci_x3: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x3_el2_stack: forall d a b, d {el2_stack: a} {psci_x3: b} = d{psci_x3: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x3_el3_stack: forall d a b, d {el3_stack: a} {psci_x3: b} = d{psci_x3: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x3_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {psci_x3: b} = d{psci_x3: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x3_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {psci_x3: b} = d{psci_x3: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x3_cur_rec: forall d a b, d {cur_rec: a} {psci_x3: b} = d{psci_x3: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x3_mstage: forall d a b, d {mstage: a} {psci_x3: b} = d{psci_x3: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_x3_trap_reason: forall d a b, d {trap_reason: a} {psci_x3: b} = d{psci_x3: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x0_psci_forward_x1: forall d a b, d {psci_forward_x1: a} {psci_forward_x0: b} = d{psci_forward_x0: b} {psci_forward_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x0_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {psci_forward_x0: b} = d{psci_forward_x0: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x0_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {psci_forward_x0: b} = d{psci_forward_x0: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x0_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {psci_forward_x0: b} = d{psci_forward_x0: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x0_target_rec: forall d a b, d {target_rec: a} {psci_forward_x0: b} = d{psci_forward_x0: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x0_el2_stack: forall d a b, d {el2_stack: a} {psci_forward_x0: b} = d{psci_forward_x0: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x0_el3_stack: forall d a b, d {el3_stack: a} {psci_forward_x0: b} = d{psci_forward_x0: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x0_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {psci_forward_x0: b} = d{psci_forward_x0: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x0_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {psci_forward_x0: b} = d{psci_forward_x0: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x0_cur_rec: forall d a b, d {cur_rec: a} {psci_forward_x0: b} = d{psci_forward_x0: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x0_mstage: forall d a b, d {mstage: a} {psci_forward_x0: b} = d{psci_forward_x0: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x0_trap_reason: forall d a b, d {trap_reason: a} {psci_forward_x0: b} = d{psci_forward_x0: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x1_psci_forward_x2: forall d a b, d {psci_forward_x2: a} {psci_forward_x1: b} = d{psci_forward_x1: b} {psci_forward_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x1_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {psci_forward_x1: b} = d{psci_forward_x1: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x1_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {psci_forward_x1: b} = d{psci_forward_x1: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x1_target_rec: forall d a b, d {target_rec: a} {psci_forward_x1: b} = d{psci_forward_x1: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x1_el2_stack: forall d a b, d {el2_stack: a} {psci_forward_x1: b} = d{psci_forward_x1: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x1_el3_stack: forall d a b, d {el3_stack: a} {psci_forward_x1: b} = d{psci_forward_x1: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x1_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {psci_forward_x1: b} = d{psci_forward_x1: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x1_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {psci_forward_x1: b} = d{psci_forward_x1: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x1_cur_rec: forall d a b, d {cur_rec: a} {psci_forward_x1: b} = d{psci_forward_x1: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x1_mstage: forall d a b, d {mstage: a} {psci_forward_x1: b} = d{psci_forward_x1: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x1_trap_reason: forall d a b, d {trap_reason: a} {psci_forward_x1: b} = d{psci_forward_x1: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x2_psci_forward_x3: forall d a b, d {psci_forward_x3: a} {psci_forward_x2: b} = d{psci_forward_x2: b} {psci_forward_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x2_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {psci_forward_x2: b} = d{psci_forward_x2: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x2_target_rec: forall d a b, d {target_rec: a} {psci_forward_x2: b} = d{psci_forward_x2: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x2_el2_stack: forall d a b, d {el2_stack: a} {psci_forward_x2: b} = d{psci_forward_x2: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x2_el3_stack: forall d a b, d {el3_stack: a} {psci_forward_x2: b} = d{psci_forward_x2: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x2_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {psci_forward_x2: b} = d{psci_forward_x2: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x2_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {psci_forward_x2: b} = d{psci_forward_x2: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x2_cur_rec: forall d a b, d {cur_rec: a} {psci_forward_x2: b} = d{psci_forward_x2: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x2_mstage: forall d a b, d {mstage: a} {psci_forward_x2: b} = d{psci_forward_x2: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x2_trap_reason: forall d a b, d {trap_reason: a} {psci_forward_x2: b} = d{psci_forward_x2: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x3_psci_forward_psci_call: forall d a b, d {psci_forward_psci_call: a} {psci_forward_x3: b} = d{psci_forward_x3: b} {psci_forward_psci_call: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x3_target_rec: forall d a b, d {target_rec: a} {psci_forward_x3: b} = d{psci_forward_x3: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x3_el2_stack: forall d a b, d {el2_stack: a} {psci_forward_x3: b} = d{psci_forward_x3: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x3_el3_stack: forall d a b, d {el3_stack: a} {psci_forward_x3: b} = d{psci_forward_x3: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x3_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {psci_forward_x3: b} = d{psci_forward_x3: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x3_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {psci_forward_x3: b} = d{psci_forward_x3: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x3_cur_rec: forall d a b, d {cur_rec: a} {psci_forward_x3: b} = d{psci_forward_x3: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x3_mstage: forall d a b, d {mstage: a} {psci_forward_x3: b} = d{psci_forward_x3: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_x3_trap_reason: forall d a b, d {trap_reason: a} {psci_forward_x3: b} = d{psci_forward_x3: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_psci_call_target_rec: forall d a b, d {target_rec: a} {psci_forward_psci_call: b} = d{psci_forward_psci_call: b} {target_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_psci_call_el2_stack: forall d a b, d {el2_stack: a} {psci_forward_psci_call: b} = d{psci_forward_psci_call: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_psci_call_el3_stack: forall d a b, d {el3_stack: a} {psci_forward_psci_call: b} = d{psci_forward_psci_call: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_psci_call_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {psci_forward_psci_call: b} = d{psci_forward_psci_call: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_psci_call_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {psci_forward_psci_call: b} = d{psci_forward_psci_call: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_psci_call_cur_rec: forall d a b, d {cur_rec: a} {psci_forward_psci_call: b} = d{psci_forward_psci_call: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_psci_call_mstage: forall d a b, d {mstage: a} {psci_forward_psci_call: b} = d{psci_forward_psci_call: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_psci_forward_psci_call_trap_reason: forall d a b, d {trap_reason: a} {psci_forward_psci_call: b} = d{psci_forward_psci_call: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_target_rec_el2_stack: forall d a b, d {el2_stack: a} {target_rec: b} = d{target_rec: b} {el2_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_target_rec_el3_stack: forall d a b, d {el3_stack: a} {target_rec: b} = d{target_rec: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_target_rec_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {target_rec: b} = d{target_rec: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_target_rec_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {target_rec: b} = d{target_rec: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_target_rec_cur_rec: forall d a b, d {cur_rec: a} {target_rec: b} = d{target_rec: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_target_rec_mstage: forall d a b, d {mstage: a} {target_rec: b} = d{target_rec: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_target_rec_trap_reason: forall d a b, d {trap_reason: a} {target_rec: b} = d{target_rec: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_el2_stack_el3_stack: forall d a b, d {el3_stack: a} {el2_stack: b} = d{el2_stack: b} {el3_stack: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_el2_stack_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {el2_stack: b} = d{el2_stack: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_el2_stack_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {el2_stack: b} = d{el2_stack: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_el2_stack_cur_rec: forall d a b, d {cur_rec: a} {el2_stack: b} = d{el2_stack: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_el2_stack_mstage: forall d a b, d {mstage: a} {el2_stack: b} = d{el2_stack: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_el2_stack_trap_reason: forall d a b, d {trap_reason: a} {el2_stack: b} = d{el2_stack: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_el3_stack_ns_regs_el3: forall d a b, d {ns_regs_el3: a} {el3_stack: b} = d{el3_stack: b} {ns_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_el3_stack_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {el3_stack: b} = d{el3_stack: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_el3_stack_cur_rec: forall d a b, d {cur_rec: a} {el3_stack: b} = d{el3_stack: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_el3_stack_mstage: forall d a b, d {mstage: a} {el3_stack: b} = d{el3_stack: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_el3_stack_trap_reason: forall d a b, d {trap_reason: a} {el3_stack: b} = d{el3_stack: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el3_realm_regs_el3: forall d a b, d {realm_regs_el3: a} {ns_regs_el3: b} = d{ns_regs_el3: b} {realm_regs_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el3_cur_rec: forall d a b, d {cur_rec: a} {ns_regs_el3: b} = d{ns_regs_el3: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el3_mstage: forall d a b, d {mstage: a} {ns_regs_el3: b} = d{ns_regs_el3: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ns_regs_el3_trap_reason: forall d a b, d {trap_reason: a} {ns_regs_el3: b} = d{ns_regs_el3: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_regs_el3_cur_rec: forall d a b, d {cur_rec: a} {realm_regs_el3: b} = d{realm_regs_el3: b} {cur_rec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_regs_el3_mstage: forall d a b, d {mstage: a} {realm_regs_el3: b} = d{realm_regs_el3: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_realm_regs_el3_trap_reason: forall d a b, d {trap_reason: a} {realm_regs_el3: b} = d{realm_regs_el3: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cur_rec_mstage: forall d a b, d {mstage: a} {cur_rec: b} = d{cur_rec: b} {mstage: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_cur_rec_trap_reason: forall d a b, d {trap_reason: a} {cur_rec: b} = d{cur_rec: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_mstage_trap_reason: forall d a b, d {trap_reason: a} {mstage: b} = d{mstage: b} {trap_reason: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gs_gpt: forall d a b, d {gpt: a} {gs: b} = d{gs: b} {gpt: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gs_gpt_lk: forall d a b, d {gpt_lk: a} {gs: b} = d{gs: b} {gpt_lk: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gs_tlbs: forall d a b, d {tlbs: a} {gs: b} = d{gs: b} {tlbs: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gs_rtts: forall d a b, d {rtts: a} {gs: b} = d{gs: b} {rtts: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gs_realms: forall d a b, d {realms: a} {gs: b} = d{gs: b} {realms: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gpt_gpt_lk: forall d a b, d {gpt_lk: a} {gpt: b} = d{gpt: b} {gpt_lk: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gpt_tlbs: forall d a b, d {tlbs: a} {gpt: b} = d{gpt: b} {tlbs: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gpt_rtts: forall d a b, d {rtts: a} {gpt: b} = d{gpt: b} {rtts: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gpt_realms: forall d a b, d {realms: a} {gpt: b} = d{gpt: b} {realms: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gpt_lk_tlbs: forall d a b, d {tlbs: a} {gpt_lk: b} = d{gpt_lk: b} {tlbs: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gpt_lk_rtts: forall d a b, d {rtts: a} {gpt_lk: b} = d{gpt_lk: b} {rtts: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gpt_lk_realms: forall d a b, d {realms: a} {gpt_lk: b} = d{gpt_lk: b} {realms: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_tlbs_rtts: forall d a b, d {rtts: a} {tlbs: b} = d{tlbs: b} {rtts: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_tlbs_realms: forall d a b, d {realms: a} {tlbs: b} = d{tlbs: b} {realms: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_rtts_realms: forall d a b, d {realms: a} {rtts: b} = d{rtts: b} {realms: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_glock_gref: forall d a b, d {gref: a} {glock: b} = d{glock: b} {gref: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_glock_gtype: forall d a b, d {gtype: a} {glock: b} = d{glock: b} {gtype: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_glock_gcnt: forall d a b, d {gcnt: a} {glock: b} = d{glock: b} {gcnt: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_glock_ginfo: forall d a b, d {ginfo: a} {glock: b} = d{glock: b} {ginfo: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_glock_gnorm: forall d a b, d {gnorm: a} {glock: b} = d{glock: b} {gnorm: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_glock_grec: forall d a b, d {grec: a} {glock: b} = d{glock: b} {grec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_glock_gro: forall d a b, d {gro: a} {glock: b} = d{glock: b} {gro: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_glock_gaux: forall d a b, d {gaux: a} {glock: b} = d{glock: b} {gaux: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gref_gtype: forall d a b, d {gtype: a} {gref: b} = d{gref: b} {gtype: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gref_gcnt: forall d a b, d {gcnt: a} {gref: b} = d{gref: b} {gcnt: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gref_ginfo: forall d a b, d {ginfo: a} {gref: b} = d{gref: b} {ginfo: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gref_gnorm: forall d a b, d {gnorm: a} {gref: b} = d{gref: b} {gnorm: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gref_grec: forall d a b, d {grec: a} {gref: b} = d{gref: b} {grec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gref_gro: forall d a b, d {gro: a} {gref: b} = d{gref: b} {gro: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gref_gaux: forall d a b, d {gaux: a} {gref: b} = d{gref: b} {gaux: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gtype_gcnt: forall d a b, d {gcnt: a} {gtype: b} = d{gtype: b} {gcnt: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gtype_ginfo: forall d a b, d {ginfo: a} {gtype: b} = d{gtype: b} {ginfo: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gtype_gnorm: forall d a b, d {gnorm: a} {gtype: b} = d{gtype: b} {gnorm: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gtype_grec: forall d a b, d {grec: a} {gtype: b} = d{gtype: b} {grec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gtype_gro: forall d a b, d {gro: a} {gtype: b} = d{gtype: b} {gro: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gtype_gaux: forall d a b, d {gaux: a} {gtype: b} = d{gtype: b} {gaux: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gcnt_ginfo: forall d a b, d {ginfo: a} {gcnt: b} = d{gcnt: b} {ginfo: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gcnt_gnorm: forall d a b, d {gnorm: a} {gcnt: b} = d{gcnt: b} {gnorm: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gcnt_grec: forall d a b, d {grec: a} {gcnt: b} = d{gcnt: b} {grec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gcnt_gro: forall d a b, d {gro: a} {gcnt: b} = d{gcnt: b} {gro: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gcnt_gaux: forall d a b, d {gaux: a} {gcnt: b} = d{gcnt: b} {gaux: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ginfo_gnorm: forall d a b, d {gnorm: a} {ginfo: b} = d{ginfo: b} {gnorm: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ginfo_grec: forall d a b, d {grec: a} {ginfo: b} = d{ginfo: b} {grec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ginfo_gro: forall d a b, d {gro: a} {ginfo: b} = d{ginfo: b} {gro: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_ginfo_gaux: forall d a b, d {gaux: a} {ginfo: b} = d{ginfo: b} {gaux: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gnorm_grec: forall d a b, d {grec: a} {gnorm: b} = d{gnorm: b} {grec: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gnorm_gro: forall d a b, d {gro: a} {gnorm: b} = d{gnorm: b} {gro: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gnorm_gaux: forall d a b, d {gaux: a} {gnorm: b} = d{gnorm: b} {gaux: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_grec_gro: forall d a b, d {gro: a} {grec: b} = d{grec: b} {gro: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_grec_gaux: forall d a b, d {gaux: a} {grec: b} = d{grec: b} {gaux: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_gro_gaux: forall d a b, d {gaux: a} {gro: b} = d{gro: b} {gaux: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x1: forall d a b, d {r_x1: a} {r_x0: b} = d{r_x0: b} {r_x1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x2: forall d a b, d {r_x2: a} {r_x0: b} = d{r_x0: b} {r_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x3: forall d a b, d {r_x3: a} {r_x0: b} = d{r_x0: b} {r_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x4: forall d a b, d {r_x4: a} {r_x0: b} = d{r_x0: b} {r_x4: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x5: forall d a b, d {r_x5: a} {r_x0: b} = d{r_x0: b} {r_x5: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x6: forall d a b, d {r_x6: a} {r_x0: b} = d{r_x0: b} {r_x6: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x7: forall d a b, d {r_x7: a} {r_x0: b} = d{r_x0: b} {r_x7: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x8: forall d a b, d {r_x8: a} {r_x0: b} = d{r_x0: b} {r_x8: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x9: forall d a b, d {r_x9: a} {r_x0: b} = d{r_x0: b} {r_x9: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x10: forall d a b, d {r_x10: a} {r_x0: b} = d{r_x0: b} {r_x10: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x11: forall d a b, d {r_x11: a} {r_x0: b} = d{r_x0: b} {r_x11: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x12: forall d a b, d {r_x12: a} {r_x0: b} = d{r_x0: b} {r_x12: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x13: forall d a b, d {r_x13: a} {r_x0: b} = d{r_x0: b} {r_x13: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x14: forall d a b, d {r_x14: a} {r_x0: b} = d{r_x0: b} {r_x14: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x15: forall d a b, d {r_x15: a} {r_x0: b} = d{r_x0: b} {r_x15: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x16: forall d a b, d {r_x16: a} {r_x0: b} = d{r_x0: b} {r_x16: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x17: forall d a b, d {r_x17: a} {r_x0: b} = d{r_x0: b} {r_x17: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x18: forall d a b, d {r_x18: a} {r_x0: b} = d{r_x0: b} {r_x18: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x19: forall d a b, d {r_x19: a} {r_x0: b} = d{r_x0: b} {r_x19: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x20: forall d a b, d {r_x20: a} {r_x0: b} = d{r_x0: b} {r_x20: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x21: forall d a b, d {r_x21: a} {r_x0: b} = d{r_x0: b} {r_x21: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x22: forall d a b, d {r_x22: a} {r_x0: b} = d{r_x0: b} {r_x22: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x23: forall d a b, d {r_x23: a} {r_x0: b} = d{r_x0: b} {r_x23: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x24: forall d a b, d {r_x24: a} {r_x0: b} = d{r_x0: b} {r_x24: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x25: forall d a b, d {r_x25: a} {r_x0: b} = d{r_x0: b} {r_x25: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x26: forall d a b, d {r_x26: a} {r_x0: b} = d{r_x0: b} {r_x26: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x27: forall d a b, d {r_x27: a} {r_x0: b} = d{r_x0: b} {r_x27: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x28: forall d a b, d {r_x28: a} {r_x0: b} = d{r_x0: b} {r_x28: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x29: forall d a b, d {r_x29: a} {r_x0: b} = d{r_x0: b} {r_x29: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_x30: forall d a b, d {r_x30: a} {r_x0: b} = d{r_x0: b} {r_x30: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_lr: forall d a b, d {r_lr: a} {r_x0: b} = d{r_x0: b} {r_lr: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_cntp_ctl_el0: forall d a b, d {r_cntp_ctl_el0: a} {r_x0: b} = d{r_x0: b} {r_cntp_ctl_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_cntp_cval_el0: forall d a b, d {r_cntp_cval_el0: a} {r_x0: b} = d{r_x0: b} {r_cntp_cval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_cntp_tval_el0: forall d a b, d {r_cntp_tval_el0: a} {r_x0: b} = d{r_x0: b} {r_cntp_tval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_cntv_ctl_el0: forall d a b, d {r_cntv_ctl_el0: a} {r_x0: b} = d{r_x0: b} {r_cntv_ctl_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_cntv_cval_el0: forall d a b, d {r_cntv_cval_el0: a} {r_x0: b} = d{r_x0: b} {r_cntv_cval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_cntv_tval_el0: forall d a b, d {r_cntv_tval_el0: a} {r_x0: b} = d{r_x0: b} {r_cntv_tval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_sp_el0: forall d a b, d {r_sp_el0: a} {r_x0: b} = d{r_x0: b} {r_sp_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_pmcr_el0: forall d a b, d {r_pmcr_el0: a} {r_x0: b} = d{r_x0: b} {r_pmcr_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_pmuserenr_el0: forall d a b, d {r_pmuserenr_el0: a} {r_x0: b} = d{r_x0: b} {r_pmuserenr_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_tpidrro_el0: forall d a b, d {r_tpidrro_el0: a} {r_x0: b} = d{r_x0: b} {r_tpidrro_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_tpidr_el0: forall d a b, d {r_tpidr_el0: a} {r_x0: b} = d{r_x0: b} {r_tpidr_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_sp_el1: forall d a b, d {r_sp_el1: a} {r_x0: b} = d{r_x0: b} {r_sp_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_elr_el1: forall d a b, d {r_elr_el1: a} {r_x0: b} = d{r_x0: b} {r_elr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_spsr_el1: forall d a b, d {r_spsr_el1: a} {r_x0: b} = d{r_x0: b} {r_spsr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_csselr_el1: forall d a b, d {r_csselr_el1: a} {r_x0: b} = d{r_x0: b} {r_csselr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_sctlr_el1: forall d a b, d {r_sctlr_el1: a} {r_x0: b} = d{r_x0: b} {r_sctlr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_actlr_el1: forall d a b, d {r_actlr_el1: a} {r_x0: b} = d{r_x0: b} {r_actlr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_cpacr_el1: forall d a b, d {r_cpacr_el1: a} {r_x0: b} = d{r_x0: b} {r_cpacr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_zcr_el1: forall d a b, d {r_zcr_el1: a} {r_x0: b} = d{r_x0: b} {r_zcr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_ttbr0_el1: forall d a b, d {r_ttbr0_el1: a} {r_x0: b} = d{r_x0: b} {r_ttbr0_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_ttbr1_el1: forall d a b, d {r_ttbr1_el1: a} {r_x0: b} = d{r_x0: b} {r_ttbr1_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_tcr_el1: forall d a b, d {r_tcr_el1: a} {r_x0: b} = d{r_x0: b} {r_tcr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_esr_el1: forall d a b, d {r_esr_el1: a} {r_x0: b} = d{r_x0: b} {r_esr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_afsr0_el1: forall d a b, d {r_afsr0_el1: a} {r_x0: b} = d{r_x0: b} {r_afsr0_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_afsr1_el1: forall d a b, d {r_afsr1_el1: a} {r_x0: b} = d{r_x0: b} {r_afsr1_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_far_el1: forall d a b, d {r_far_el1: a} {r_x0: b} = d{r_x0: b} {r_far_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_mair_el1: forall d a b, d {r_mair_el1: a} {r_x0: b} = d{r_x0: b} {r_mair_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_vbar_el1: forall d a b, d {r_vbar_el1: a} {r_x0: b} = d{r_x0: b} {r_vbar_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_contextidr_el1: forall d a b, d {r_contextidr_el1: a} {r_x0: b} = d{r_x0: b} {r_contextidr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_tpidr_el1: forall d a b, d {r_tpidr_el1: a} {r_x0: b} = d{r_x0: b} {r_tpidr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_amair_el1: forall d a b, d {r_amair_el1: a} {r_x0: b} = d{r_x0: b} {r_amair_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_cntkctl_el1: forall d a b, d {r_cntkctl_el1: a} {r_x0: b} = d{r_x0: b} {r_cntkctl_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_par_el1: forall d a b, d {r_par_el1: a} {r_x0: b} = d{r_x0: b} {r_par_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_mdscr_el1: forall d a b, d {r_mdscr_el1: a} {r_x0: b} = d{r_x0: b} {r_mdscr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_mdccint_el1: forall d a b, d {r_mdccint_el1: a} {r_x0: b} = d{r_x0: b} {r_mdccint_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_disr_el1: forall d a b, d {r_disr_el1: a} {r_x0: b} = d{r_x0: b} {r_disr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_mpam0_el1: forall d a b, d {r_mpam0_el1: a} {r_x0: b} = d{r_x0: b} {r_mpam0_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_cnthctl_el2: forall d a b, d {r_cnthctl_el2: a} {r_x0: b} = d{r_x0: b} {r_cnthctl_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_cntvoff_el2: forall d a b, d {r_cntvoff_el2: a} {r_x0: b} = d{r_x0: b} {r_cntvoff_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_cntpoff_el2: forall d a b, d {r_cntpoff_el2: a} {r_x0: b} = d{r_x0: b} {r_cntpoff_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_vmpidr_el2: forall d a b, d {r_vmpidr_el2: a} {r_x0: b} = d{r_x0: b} {r_vmpidr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_vttbr_el2: forall d a b, d {r_vttbr_el2: a} {r_x0: b} = d{r_x0: b} {r_vttbr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_vtcr_el2: forall d a b, d {r_vtcr_el2: a} {r_x0: b} = d{r_x0: b} {r_vtcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_hcr_el2: forall d a b, d {r_hcr_el2: a} {r_x0: b} = d{r_x0: b} {r_hcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_actlr_el2: forall d a b, d {r_actlr_el2: a} {r_x0: b} = d{r_x0: b} {r_actlr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_afsr0_el2: forall d a b, d {r_afsr0_el2: a} {r_x0: b} = d{r_x0: b} {r_afsr0_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_afsr1_el2: forall d a b, d {r_afsr1_el2: a} {r_x0: b} = d{r_x0: b} {r_afsr1_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_amair_el2: forall d a b, d {r_amair_el2: a} {r_x0: b} = d{r_x0: b} {r_amair_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_cptr_el2: forall d a b, d {r_cptr_el2: a} {r_x0: b} = d{r_x0: b} {r_cptr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_elr_el2: forall d a b, d {r_elr_el2: a} {r_x0: b} = d{r_x0: b} {r_elr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_esr_el2: forall d a b, d {r_esr_el2: a} {r_x0: b} = d{r_x0: b} {r_esr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_far_el2: forall d a b, d {r_far_el2: a} {r_x0: b} = d{r_x0: b} {r_far_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_hacr_el2: forall d a b, d {r_hacr_el2: a} {r_x0: b} = d{r_x0: b} {r_hacr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_hpfar_el2: forall d a b, d {r_hpfar_el2: a} {r_x0: b} = d{r_x0: b} {r_hpfar_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_hstr_el2: forall d a b, d {r_hstr_el2: a} {r_x0: b} = d{r_x0: b} {r_hstr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_mair_el2: forall d a b, d {r_mair_el2: a} {r_x0: b} = d{r_x0: b} {r_mair_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_mpam_el2: forall d a b, d {r_mpam_el2: a} {r_x0: b} = d{r_x0: b} {r_mpam_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_mpamhcr_el2: forall d a b, d {r_mpamhcr_el2: a} {r_x0: b} = d{r_x0: b} {r_mpamhcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_pmscr_el2: forall d a b, d {r_pmscr_el2: a} {r_x0: b} = d{r_x0: b} {r_pmscr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_sctlr_el2: forall d a b, d {r_sctlr_el2: a} {r_x0: b} = d{r_x0: b} {r_sctlr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_scxtnum_el2: forall d a b, d {r_scxtnum_el2: a} {r_x0: b} = d{r_x0: b} {r_scxtnum_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_sp_el2: forall d a b, d {r_sp_el2: a} {r_x0: b} = d{r_x0: b} {r_sp_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_spsr_el2: forall d a b, d {r_spsr_el2: a} {r_x0: b} = d{r_x0: b} {r_spsr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_tcr_el2: forall d a b, d {r_tcr_el2: a} {r_x0: b} = d{r_x0: b} {r_tcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_tfsr_el2: forall d a b, d {r_tfsr_el2: a} {r_x0: b} = d{r_x0: b} {r_tfsr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_tpidr_el2: forall d a b, d {r_tpidr_el2: a} {r_x0: b} = d{r_x0: b} {r_tpidr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_trfcr_el2: forall d a b, d {r_trfcr_el2: a} {r_x0: b} = d{r_x0: b} {r_trfcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_ttbr0_el2: forall d a b, d {r_ttbr0_el2: a} {r_x0: b} = d{r_x0: b} {r_ttbr0_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_ttbr1_el2: forall d a b, d {r_ttbr1_el2: a} {r_x0: b} = d{r_x0: b} {r_ttbr1_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_vbar_el2: forall d a b, d {r_vbar_el2: a} {r_x0: b} = d{r_x0: b} {r_vbar_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_vdisr_el2: forall d a b, d {r_vdisr_el2: a} {r_x0: b} = d{r_x0: b} {r_vdisr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_vncr_el2: forall d a b, d {r_vncr_el2: a} {r_x0: b} = d{r_x0: b} {r_vncr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_vpidr_el2: forall d a b, d {r_vpidr_el2: a} {r_x0: b} = d{r_x0: b} {r_vpidr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_vsesr_el2: forall d a b, d {r_vsesr_el2: a} {r_x0: b} = d{r_x0: b} {r_vsesr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_vstcr_el2: forall d a b, d {r_vstcr_el2: a} {r_x0: b} = d{r_x0: b} {r_vstcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_vsttbr_el2: forall d a b, d {r_vsttbr_el2: a} {r_x0: b} = d{r_x0: b} {r_vsttbr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_zcr_el2: forall d a b, d {r_zcr_el2: a} {r_x0: b} = d{r_x0: b} {r_zcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_icc_sre_el2: forall d a b, d {r_icc_sre_el2: a} {r_x0: b} = d{r_x0: b} {r_icc_sre_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_icc_hppir1_el1: forall d a b, d {r_icc_hppir1_el1: a} {r_x0: b} = d{r_x0: b} {r_icc_hppir1_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_spsr_el3: forall d a b, d {r_spsr_el3: a} {r_x0: b} = d{r_x0: b} {r_spsr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_elr_el3: forall d a b, d {r_elr_el3: a} {r_x0: b} = d{r_x0: b} {r_elr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_esr_el3: forall d a b, d {r_esr_el3: a} {r_x0: b} = d{r_x0: b} {r_esr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_scr_el3: forall d a b, d {r_scr_el3: a} {r_x0: b} = d{r_x0: b} {r_scr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x0_r_tpidr_el3: forall d a b, d {r_tpidr_el3: a} {r_x0: b} = d{r_x0: b} {r_tpidr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x2: forall d a b, d {r_x2: a} {r_x1: b} = d{r_x1: b} {r_x2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x3: forall d a b, d {r_x3: a} {r_x1: b} = d{r_x1: b} {r_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x4: forall d a b, d {r_x4: a} {r_x1: b} = d{r_x1: b} {r_x4: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x5: forall d a b, d {r_x5: a} {r_x1: b} = d{r_x1: b} {r_x5: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x6: forall d a b, d {r_x6: a} {r_x1: b} = d{r_x1: b} {r_x6: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x7: forall d a b, d {r_x7: a} {r_x1: b} = d{r_x1: b} {r_x7: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x8: forall d a b, d {r_x8: a} {r_x1: b} = d{r_x1: b} {r_x8: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x9: forall d a b, d {r_x9: a} {r_x1: b} = d{r_x1: b} {r_x9: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x10: forall d a b, d {r_x10: a} {r_x1: b} = d{r_x1: b} {r_x10: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x11: forall d a b, d {r_x11: a} {r_x1: b} = d{r_x1: b} {r_x11: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x12: forall d a b, d {r_x12: a} {r_x1: b} = d{r_x1: b} {r_x12: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x13: forall d a b, d {r_x13: a} {r_x1: b} = d{r_x1: b} {r_x13: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x14: forall d a b, d {r_x14: a} {r_x1: b} = d{r_x1: b} {r_x14: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x15: forall d a b, d {r_x15: a} {r_x1: b} = d{r_x1: b} {r_x15: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x16: forall d a b, d {r_x16: a} {r_x1: b} = d{r_x1: b} {r_x16: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x17: forall d a b, d {r_x17: a} {r_x1: b} = d{r_x1: b} {r_x17: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x18: forall d a b, d {r_x18: a} {r_x1: b} = d{r_x1: b} {r_x18: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x19: forall d a b, d {r_x19: a} {r_x1: b} = d{r_x1: b} {r_x19: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x20: forall d a b, d {r_x20: a} {r_x1: b} = d{r_x1: b} {r_x20: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x21: forall d a b, d {r_x21: a} {r_x1: b} = d{r_x1: b} {r_x21: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x22: forall d a b, d {r_x22: a} {r_x1: b} = d{r_x1: b} {r_x22: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x23: forall d a b, d {r_x23: a} {r_x1: b} = d{r_x1: b} {r_x23: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x24: forall d a b, d {r_x24: a} {r_x1: b} = d{r_x1: b} {r_x24: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x25: forall d a b, d {r_x25: a} {r_x1: b} = d{r_x1: b} {r_x25: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x26: forall d a b, d {r_x26: a} {r_x1: b} = d{r_x1: b} {r_x26: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x27: forall d a b, d {r_x27: a} {r_x1: b} = d{r_x1: b} {r_x27: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x28: forall d a b, d {r_x28: a} {r_x1: b} = d{r_x1: b} {r_x28: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x29: forall d a b, d {r_x29: a} {r_x1: b} = d{r_x1: b} {r_x29: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_x30: forall d a b, d {r_x30: a} {r_x1: b} = d{r_x1: b} {r_x30: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_lr: forall d a b, d {r_lr: a} {r_x1: b} = d{r_x1: b} {r_lr: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_cntp_ctl_el0: forall d a b, d {r_cntp_ctl_el0: a} {r_x1: b} = d{r_x1: b} {r_cntp_ctl_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_cntp_cval_el0: forall d a b, d {r_cntp_cval_el0: a} {r_x1: b} = d{r_x1: b} {r_cntp_cval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_cntp_tval_el0: forall d a b, d {r_cntp_tval_el0: a} {r_x1: b} = d{r_x1: b} {r_cntp_tval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_cntv_ctl_el0: forall d a b, d {r_cntv_ctl_el0: a} {r_x1: b} = d{r_x1: b} {r_cntv_ctl_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_cntv_cval_el0: forall d a b, d {r_cntv_cval_el0: a} {r_x1: b} = d{r_x1: b} {r_cntv_cval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_cntv_tval_el0: forall d a b, d {r_cntv_tval_el0: a} {r_x1: b} = d{r_x1: b} {r_cntv_tval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_sp_el0: forall d a b, d {r_sp_el0: a} {r_x1: b} = d{r_x1: b} {r_sp_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_pmcr_el0: forall d a b, d {r_pmcr_el0: a} {r_x1: b} = d{r_x1: b} {r_pmcr_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_pmuserenr_el0: forall d a b, d {r_pmuserenr_el0: a} {r_x1: b} = d{r_x1: b} {r_pmuserenr_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_tpidrro_el0: forall d a b, d {r_tpidrro_el0: a} {r_x1: b} = d{r_x1: b} {r_tpidrro_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_tpidr_el0: forall d a b, d {r_tpidr_el0: a} {r_x1: b} = d{r_x1: b} {r_tpidr_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_sp_el1: forall d a b, d {r_sp_el1: a} {r_x1: b} = d{r_x1: b} {r_sp_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_elr_el1: forall d a b, d {r_elr_el1: a} {r_x1: b} = d{r_x1: b} {r_elr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_spsr_el1: forall d a b, d {r_spsr_el1: a} {r_x1: b} = d{r_x1: b} {r_spsr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_csselr_el1: forall d a b, d {r_csselr_el1: a} {r_x1: b} = d{r_x1: b} {r_csselr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_sctlr_el1: forall d a b, d {r_sctlr_el1: a} {r_x1: b} = d{r_x1: b} {r_sctlr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_actlr_el1: forall d a b, d {r_actlr_el1: a} {r_x1: b} = d{r_x1: b} {r_actlr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_cpacr_el1: forall d a b, d {r_cpacr_el1: a} {r_x1: b} = d{r_x1: b} {r_cpacr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_zcr_el1: forall d a b, d {r_zcr_el1: a} {r_x1: b} = d{r_x1: b} {r_zcr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_ttbr0_el1: forall d a b, d {r_ttbr0_el1: a} {r_x1: b} = d{r_x1: b} {r_ttbr0_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_ttbr1_el1: forall d a b, d {r_ttbr1_el1: a} {r_x1: b} = d{r_x1: b} {r_ttbr1_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_tcr_el1: forall d a b, d {r_tcr_el1: a} {r_x1: b} = d{r_x1: b} {r_tcr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_esr_el1: forall d a b, d {r_esr_el1: a} {r_x1: b} = d{r_x1: b} {r_esr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_afsr0_el1: forall d a b, d {r_afsr0_el1: a} {r_x1: b} = d{r_x1: b} {r_afsr0_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_afsr1_el1: forall d a b, d {r_afsr1_el1: a} {r_x1: b} = d{r_x1: b} {r_afsr1_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_far_el1: forall d a b, d {r_far_el1: a} {r_x1: b} = d{r_x1: b} {r_far_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_mair_el1: forall d a b, d {r_mair_el1: a} {r_x1: b} = d{r_x1: b} {r_mair_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_vbar_el1: forall d a b, d {r_vbar_el1: a} {r_x1: b} = d{r_x1: b} {r_vbar_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_contextidr_el1: forall d a b, d {r_contextidr_el1: a} {r_x1: b} = d{r_x1: b} {r_contextidr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_tpidr_el1: forall d a b, d {r_tpidr_el1: a} {r_x1: b} = d{r_x1: b} {r_tpidr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_amair_el1: forall d a b, d {r_amair_el1: a} {r_x1: b} = d{r_x1: b} {r_amair_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_cntkctl_el1: forall d a b, d {r_cntkctl_el1: a} {r_x1: b} = d{r_x1: b} {r_cntkctl_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_par_el1: forall d a b, d {r_par_el1: a} {r_x1: b} = d{r_x1: b} {r_par_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_mdscr_el1: forall d a b, d {r_mdscr_el1: a} {r_x1: b} = d{r_x1: b} {r_mdscr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_mdccint_el1: forall d a b, d {r_mdccint_el1: a} {r_x1: b} = d{r_x1: b} {r_mdccint_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_disr_el1: forall d a b, d {r_disr_el1: a} {r_x1: b} = d{r_x1: b} {r_disr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_mpam0_el1: forall d a b, d {r_mpam0_el1: a} {r_x1: b} = d{r_x1: b} {r_mpam0_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_cnthctl_el2: forall d a b, d {r_cnthctl_el2: a} {r_x1: b} = d{r_x1: b} {r_cnthctl_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_cntvoff_el2: forall d a b, d {r_cntvoff_el2: a} {r_x1: b} = d{r_x1: b} {r_cntvoff_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_cntpoff_el2: forall d a b, d {r_cntpoff_el2: a} {r_x1: b} = d{r_x1: b} {r_cntpoff_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_vmpidr_el2: forall d a b, d {r_vmpidr_el2: a} {r_x1: b} = d{r_x1: b} {r_vmpidr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_vttbr_el2: forall d a b, d {r_vttbr_el2: a} {r_x1: b} = d{r_x1: b} {r_vttbr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_vtcr_el2: forall d a b, d {r_vtcr_el2: a} {r_x1: b} = d{r_x1: b} {r_vtcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_hcr_el2: forall d a b, d {r_hcr_el2: a} {r_x1: b} = d{r_x1: b} {r_hcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_actlr_el2: forall d a b, d {r_actlr_el2: a} {r_x1: b} = d{r_x1: b} {r_actlr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_afsr0_el2: forall d a b, d {r_afsr0_el2: a} {r_x1: b} = d{r_x1: b} {r_afsr0_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_afsr1_el2: forall d a b, d {r_afsr1_el2: a} {r_x1: b} = d{r_x1: b} {r_afsr1_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_amair_el2: forall d a b, d {r_amair_el2: a} {r_x1: b} = d{r_x1: b} {r_amair_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_cptr_el2: forall d a b, d {r_cptr_el2: a} {r_x1: b} = d{r_x1: b} {r_cptr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_elr_el2: forall d a b, d {r_elr_el2: a} {r_x1: b} = d{r_x1: b} {r_elr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_esr_el2: forall d a b, d {r_esr_el2: a} {r_x1: b} = d{r_x1: b} {r_esr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_far_el2: forall d a b, d {r_far_el2: a} {r_x1: b} = d{r_x1: b} {r_far_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_hacr_el2: forall d a b, d {r_hacr_el2: a} {r_x1: b} = d{r_x1: b} {r_hacr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_hpfar_el2: forall d a b, d {r_hpfar_el2: a} {r_x1: b} = d{r_x1: b} {r_hpfar_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_hstr_el2: forall d a b, d {r_hstr_el2: a} {r_x1: b} = d{r_x1: b} {r_hstr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_mair_el2: forall d a b, d {r_mair_el2: a} {r_x1: b} = d{r_x1: b} {r_mair_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_mpam_el2: forall d a b, d {r_mpam_el2: a} {r_x1: b} = d{r_x1: b} {r_mpam_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_mpamhcr_el2: forall d a b, d {r_mpamhcr_el2: a} {r_x1: b} = d{r_x1: b} {r_mpamhcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_pmscr_el2: forall d a b, d {r_pmscr_el2: a} {r_x1: b} = d{r_x1: b} {r_pmscr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_sctlr_el2: forall d a b, d {r_sctlr_el2: a} {r_x1: b} = d{r_x1: b} {r_sctlr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_scxtnum_el2: forall d a b, d {r_scxtnum_el2: a} {r_x1: b} = d{r_x1: b} {r_scxtnum_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_sp_el2: forall d a b, d {r_sp_el2: a} {r_x1: b} = d{r_x1: b} {r_sp_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_spsr_el2: forall d a b, d {r_spsr_el2: a} {r_x1: b} = d{r_x1: b} {r_spsr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_tcr_el2: forall d a b, d {r_tcr_el2: a} {r_x1: b} = d{r_x1: b} {r_tcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_tfsr_el2: forall d a b, d {r_tfsr_el2: a} {r_x1: b} = d{r_x1: b} {r_tfsr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_tpidr_el2: forall d a b, d {r_tpidr_el2: a} {r_x1: b} = d{r_x1: b} {r_tpidr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_trfcr_el2: forall d a b, d {r_trfcr_el2: a} {r_x1: b} = d{r_x1: b} {r_trfcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_ttbr0_el2: forall d a b, d {r_ttbr0_el2: a} {r_x1: b} = d{r_x1: b} {r_ttbr0_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_ttbr1_el2: forall d a b, d {r_ttbr1_el2: a} {r_x1: b} = d{r_x1: b} {r_ttbr1_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_vbar_el2: forall d a b, d {r_vbar_el2: a} {r_x1: b} = d{r_x1: b} {r_vbar_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_vdisr_el2: forall d a b, d {r_vdisr_el2: a} {r_x1: b} = d{r_x1: b} {r_vdisr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_vncr_el2: forall d a b, d {r_vncr_el2: a} {r_x1: b} = d{r_x1: b} {r_vncr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_vpidr_el2: forall d a b, d {r_vpidr_el2: a} {r_x1: b} = d{r_x1: b} {r_vpidr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_vsesr_el2: forall d a b, d {r_vsesr_el2: a} {r_x1: b} = d{r_x1: b} {r_vsesr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_vstcr_el2: forall d a b, d {r_vstcr_el2: a} {r_x1: b} = d{r_x1: b} {r_vstcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_vsttbr_el2: forall d a b, d {r_vsttbr_el2: a} {r_x1: b} = d{r_x1: b} {r_vsttbr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_zcr_el2: forall d a b, d {r_zcr_el2: a} {r_x1: b} = d{r_x1: b} {r_zcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_icc_sre_el2: forall d a b, d {r_icc_sre_el2: a} {r_x1: b} = d{r_x1: b} {r_icc_sre_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_icc_hppir1_el1: forall d a b, d {r_icc_hppir1_el1: a} {r_x1: b} = d{r_x1: b} {r_icc_hppir1_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_spsr_el3: forall d a b, d {r_spsr_el3: a} {r_x1: b} = d{r_x1: b} {r_spsr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_elr_el3: forall d a b, d {r_elr_el3: a} {r_x1: b} = d{r_x1: b} {r_elr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_esr_el3: forall d a b, d {r_esr_el3: a} {r_x1: b} = d{r_x1: b} {r_esr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_scr_el3: forall d a b, d {r_scr_el3: a} {r_x1: b} = d{r_x1: b} {r_scr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x1_r_tpidr_el3: forall d a b, d {r_tpidr_el3: a} {r_x1: b} = d{r_x1: b} {r_tpidr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x3: forall d a b, d {r_x3: a} {r_x2: b} = d{r_x2: b} {r_x3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x4: forall d a b, d {r_x4: a} {r_x2: b} = d{r_x2: b} {r_x4: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x5: forall d a b, d {r_x5: a} {r_x2: b} = d{r_x2: b} {r_x5: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x6: forall d a b, d {r_x6: a} {r_x2: b} = d{r_x2: b} {r_x6: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x7: forall d a b, d {r_x7: a} {r_x2: b} = d{r_x2: b} {r_x7: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x8: forall d a b, d {r_x8: a} {r_x2: b} = d{r_x2: b} {r_x8: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x9: forall d a b, d {r_x9: a} {r_x2: b} = d{r_x2: b} {r_x9: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x10: forall d a b, d {r_x10: a} {r_x2: b} = d{r_x2: b} {r_x10: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x11: forall d a b, d {r_x11: a} {r_x2: b} = d{r_x2: b} {r_x11: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x12: forall d a b, d {r_x12: a} {r_x2: b} = d{r_x2: b} {r_x12: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x13: forall d a b, d {r_x13: a} {r_x2: b} = d{r_x2: b} {r_x13: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x14: forall d a b, d {r_x14: a} {r_x2: b} = d{r_x2: b} {r_x14: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x15: forall d a b, d {r_x15: a} {r_x2: b} = d{r_x2: b} {r_x15: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x16: forall d a b, d {r_x16: a} {r_x2: b} = d{r_x2: b} {r_x16: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x17: forall d a b, d {r_x17: a} {r_x2: b} = d{r_x2: b} {r_x17: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x18: forall d a b, d {r_x18: a} {r_x2: b} = d{r_x2: b} {r_x18: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x19: forall d a b, d {r_x19: a} {r_x2: b} = d{r_x2: b} {r_x19: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x20: forall d a b, d {r_x20: a} {r_x2: b} = d{r_x2: b} {r_x20: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x21: forall d a b, d {r_x21: a} {r_x2: b} = d{r_x2: b} {r_x21: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x22: forall d a b, d {r_x22: a} {r_x2: b} = d{r_x2: b} {r_x22: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x23: forall d a b, d {r_x23: a} {r_x2: b} = d{r_x2: b} {r_x23: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x24: forall d a b, d {r_x24: a} {r_x2: b} = d{r_x2: b} {r_x24: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x25: forall d a b, d {r_x25: a} {r_x2: b} = d{r_x2: b} {r_x25: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x26: forall d a b, d {r_x26: a} {r_x2: b} = d{r_x2: b} {r_x26: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x27: forall d a b, d {r_x27: a} {r_x2: b} = d{r_x2: b} {r_x27: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x28: forall d a b, d {r_x28: a} {r_x2: b} = d{r_x2: b} {r_x28: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x29: forall d a b, d {r_x29: a} {r_x2: b} = d{r_x2: b} {r_x29: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_x30: forall d a b, d {r_x30: a} {r_x2: b} = d{r_x2: b} {r_x30: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_lr: forall d a b, d {r_lr: a} {r_x2: b} = d{r_x2: b} {r_lr: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_cntp_ctl_el0: forall d a b, d {r_cntp_ctl_el0: a} {r_x2: b} = d{r_x2: b} {r_cntp_ctl_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_cntp_cval_el0: forall d a b, d {r_cntp_cval_el0: a} {r_x2: b} = d{r_x2: b} {r_cntp_cval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_cntp_tval_el0: forall d a b, d {r_cntp_tval_el0: a} {r_x2: b} = d{r_x2: b} {r_cntp_tval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_cntv_ctl_el0: forall d a b, d {r_cntv_ctl_el0: a} {r_x2: b} = d{r_x2: b} {r_cntv_ctl_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_cntv_cval_el0: forall d a b, d {r_cntv_cval_el0: a} {r_x2: b} = d{r_x2: b} {r_cntv_cval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_cntv_tval_el0: forall d a b, d {r_cntv_tval_el0: a} {r_x2: b} = d{r_x2: b} {r_cntv_tval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_sp_el0: forall d a b, d {r_sp_el0: a} {r_x2: b} = d{r_x2: b} {r_sp_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_pmcr_el0: forall d a b, d {r_pmcr_el0: a} {r_x2: b} = d{r_x2: b} {r_pmcr_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_pmuserenr_el0: forall d a b, d {r_pmuserenr_el0: a} {r_x2: b} = d{r_x2: b} {r_pmuserenr_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_tpidrro_el0: forall d a b, d {r_tpidrro_el0: a} {r_x2: b} = d{r_x2: b} {r_tpidrro_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_tpidr_el0: forall d a b, d {r_tpidr_el0: a} {r_x2: b} = d{r_x2: b} {r_tpidr_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_sp_el1: forall d a b, d {r_sp_el1: a} {r_x2: b} = d{r_x2: b} {r_sp_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_elr_el1: forall d a b, d {r_elr_el1: a} {r_x2: b} = d{r_x2: b} {r_elr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_spsr_el1: forall d a b, d {r_spsr_el1: a} {r_x2: b} = d{r_x2: b} {r_spsr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_csselr_el1: forall d a b, d {r_csselr_el1: a} {r_x2: b} = d{r_x2: b} {r_csselr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_sctlr_el1: forall d a b, d {r_sctlr_el1: a} {r_x2: b} = d{r_x2: b} {r_sctlr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_actlr_el1: forall d a b, d {r_actlr_el1: a} {r_x2: b} = d{r_x2: b} {r_actlr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_cpacr_el1: forall d a b, d {r_cpacr_el1: a} {r_x2: b} = d{r_x2: b} {r_cpacr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_zcr_el1: forall d a b, d {r_zcr_el1: a} {r_x2: b} = d{r_x2: b} {r_zcr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_ttbr0_el1: forall d a b, d {r_ttbr0_el1: a} {r_x2: b} = d{r_x2: b} {r_ttbr0_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_ttbr1_el1: forall d a b, d {r_ttbr1_el1: a} {r_x2: b} = d{r_x2: b} {r_ttbr1_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_tcr_el1: forall d a b, d {r_tcr_el1: a} {r_x2: b} = d{r_x2: b} {r_tcr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_esr_el1: forall d a b, d {r_esr_el1: a} {r_x2: b} = d{r_x2: b} {r_esr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_afsr0_el1: forall d a b, d {r_afsr0_el1: a} {r_x2: b} = d{r_x2: b} {r_afsr0_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_afsr1_el1: forall d a b, d {r_afsr1_el1: a} {r_x2: b} = d{r_x2: b} {r_afsr1_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_far_el1: forall d a b, d {r_far_el1: a} {r_x2: b} = d{r_x2: b} {r_far_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_mair_el1: forall d a b, d {r_mair_el1: a} {r_x2: b} = d{r_x2: b} {r_mair_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_vbar_el1: forall d a b, d {r_vbar_el1: a} {r_x2: b} = d{r_x2: b} {r_vbar_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_contextidr_el1: forall d a b, d {r_contextidr_el1: a} {r_x2: b} = d{r_x2: b} {r_contextidr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_tpidr_el1: forall d a b, d {r_tpidr_el1: a} {r_x2: b} = d{r_x2: b} {r_tpidr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_amair_el1: forall d a b, d {r_amair_el1: a} {r_x2: b} = d{r_x2: b} {r_amair_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_cntkctl_el1: forall d a b, d {r_cntkctl_el1: a} {r_x2: b} = d{r_x2: b} {r_cntkctl_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_par_el1: forall d a b, d {r_par_el1: a} {r_x2: b} = d{r_x2: b} {r_par_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_mdscr_el1: forall d a b, d {r_mdscr_el1: a} {r_x2: b} = d{r_x2: b} {r_mdscr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_mdccint_el1: forall d a b, d {r_mdccint_el1: a} {r_x2: b} = d{r_x2: b} {r_mdccint_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_disr_el1: forall d a b, d {r_disr_el1: a} {r_x2: b} = d{r_x2: b} {r_disr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_mpam0_el1: forall d a b, d {r_mpam0_el1: a} {r_x2: b} = d{r_x2: b} {r_mpam0_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_cnthctl_el2: forall d a b, d {r_cnthctl_el2: a} {r_x2: b} = d{r_x2: b} {r_cnthctl_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_cntvoff_el2: forall d a b, d {r_cntvoff_el2: a} {r_x2: b} = d{r_x2: b} {r_cntvoff_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_cntpoff_el2: forall d a b, d {r_cntpoff_el2: a} {r_x2: b} = d{r_x2: b} {r_cntpoff_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_vmpidr_el2: forall d a b, d {r_vmpidr_el2: a} {r_x2: b} = d{r_x2: b} {r_vmpidr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_vttbr_el2: forall d a b, d {r_vttbr_el2: a} {r_x2: b} = d{r_x2: b} {r_vttbr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_vtcr_el2: forall d a b, d {r_vtcr_el2: a} {r_x2: b} = d{r_x2: b} {r_vtcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_hcr_el2: forall d a b, d {r_hcr_el2: a} {r_x2: b} = d{r_x2: b} {r_hcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_actlr_el2: forall d a b, d {r_actlr_el2: a} {r_x2: b} = d{r_x2: b} {r_actlr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_afsr0_el2: forall d a b, d {r_afsr0_el2: a} {r_x2: b} = d{r_x2: b} {r_afsr0_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_afsr1_el2: forall d a b, d {r_afsr1_el2: a} {r_x2: b} = d{r_x2: b} {r_afsr1_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_amair_el2: forall d a b, d {r_amair_el2: a} {r_x2: b} = d{r_x2: b} {r_amair_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_cptr_el2: forall d a b, d {r_cptr_el2: a} {r_x2: b} = d{r_x2: b} {r_cptr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_elr_el2: forall d a b, d {r_elr_el2: a} {r_x2: b} = d{r_x2: b} {r_elr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_esr_el2: forall d a b, d {r_esr_el2: a} {r_x2: b} = d{r_x2: b} {r_esr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_far_el2: forall d a b, d {r_far_el2: a} {r_x2: b} = d{r_x2: b} {r_far_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_hacr_el2: forall d a b, d {r_hacr_el2: a} {r_x2: b} = d{r_x2: b} {r_hacr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_hpfar_el2: forall d a b, d {r_hpfar_el2: a} {r_x2: b} = d{r_x2: b} {r_hpfar_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_hstr_el2: forall d a b, d {r_hstr_el2: a} {r_x2: b} = d{r_x2: b} {r_hstr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_mair_el2: forall d a b, d {r_mair_el2: a} {r_x2: b} = d{r_x2: b} {r_mair_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_mpam_el2: forall d a b, d {r_mpam_el2: a} {r_x2: b} = d{r_x2: b} {r_mpam_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_mpamhcr_el2: forall d a b, d {r_mpamhcr_el2: a} {r_x2: b} = d{r_x2: b} {r_mpamhcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_pmscr_el2: forall d a b, d {r_pmscr_el2: a} {r_x2: b} = d{r_x2: b} {r_pmscr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_sctlr_el2: forall d a b, d {r_sctlr_el2: a} {r_x2: b} = d{r_x2: b} {r_sctlr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_scxtnum_el2: forall d a b, d {r_scxtnum_el2: a} {r_x2: b} = d{r_x2: b} {r_scxtnum_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_sp_el2: forall d a b, d {r_sp_el2: a} {r_x2: b} = d{r_x2: b} {r_sp_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_spsr_el2: forall d a b, d {r_spsr_el2: a} {r_x2: b} = d{r_x2: b} {r_spsr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_tcr_el2: forall d a b, d {r_tcr_el2: a} {r_x2: b} = d{r_x2: b} {r_tcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_tfsr_el2: forall d a b, d {r_tfsr_el2: a} {r_x2: b} = d{r_x2: b} {r_tfsr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_tpidr_el2: forall d a b, d {r_tpidr_el2: a} {r_x2: b} = d{r_x2: b} {r_tpidr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_trfcr_el2: forall d a b, d {r_trfcr_el2: a} {r_x2: b} = d{r_x2: b} {r_trfcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_ttbr0_el2: forall d a b, d {r_ttbr0_el2: a} {r_x2: b} = d{r_x2: b} {r_ttbr0_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_ttbr1_el2: forall d a b, d {r_ttbr1_el2: a} {r_x2: b} = d{r_x2: b} {r_ttbr1_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_vbar_el2: forall d a b, d {r_vbar_el2: a} {r_x2: b} = d{r_x2: b} {r_vbar_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_vdisr_el2: forall d a b, d {r_vdisr_el2: a} {r_x2: b} = d{r_x2: b} {r_vdisr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_vncr_el2: forall d a b, d {r_vncr_el2: a} {r_x2: b} = d{r_x2: b} {r_vncr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_vpidr_el2: forall d a b, d {r_vpidr_el2: a} {r_x2: b} = d{r_x2: b} {r_vpidr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_vsesr_el2: forall d a b, d {r_vsesr_el2: a} {r_x2: b} = d{r_x2: b} {r_vsesr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_vstcr_el2: forall d a b, d {r_vstcr_el2: a} {r_x2: b} = d{r_x2: b} {r_vstcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_vsttbr_el2: forall d a b, d {r_vsttbr_el2: a} {r_x2: b} = d{r_x2: b} {r_vsttbr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_zcr_el2: forall d a b, d {r_zcr_el2: a} {r_x2: b} = d{r_x2: b} {r_zcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_icc_sre_el2: forall d a b, d {r_icc_sre_el2: a} {r_x2: b} = d{r_x2: b} {r_icc_sre_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_icc_hppir1_el1: forall d a b, d {r_icc_hppir1_el1: a} {r_x2: b} = d{r_x2: b} {r_icc_hppir1_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_spsr_el3: forall d a b, d {r_spsr_el3: a} {r_x2: b} = d{r_x2: b} {r_spsr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_elr_el3: forall d a b, d {r_elr_el3: a} {r_x2: b} = d{r_x2: b} {r_elr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_esr_el3: forall d a b, d {r_esr_el3: a} {r_x2: b} = d{r_x2: b} {r_esr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_scr_el3: forall d a b, d {r_scr_el3: a} {r_x2: b} = d{r_x2: b} {r_scr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x2_r_tpidr_el3: forall d a b, d {r_tpidr_el3: a} {r_x2: b} = d{r_x2: b} {r_tpidr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x4: forall d a b, d {r_x4: a} {r_x3: b} = d{r_x3: b} {r_x4: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x5: forall d a b, d {r_x5: a} {r_x3: b} = d{r_x3: b} {r_x5: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x6: forall d a b, d {r_x6: a} {r_x3: b} = d{r_x3: b} {r_x6: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x7: forall d a b, d {r_x7: a} {r_x3: b} = d{r_x3: b} {r_x7: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x8: forall d a b, d {r_x8: a} {r_x3: b} = d{r_x3: b} {r_x8: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x9: forall d a b, d {r_x9: a} {r_x3: b} = d{r_x3: b} {r_x9: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x10: forall d a b, d {r_x10: a} {r_x3: b} = d{r_x3: b} {r_x10: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x11: forall d a b, d {r_x11: a} {r_x3: b} = d{r_x3: b} {r_x11: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x12: forall d a b, d {r_x12: a} {r_x3: b} = d{r_x3: b} {r_x12: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x13: forall d a b, d {r_x13: a} {r_x3: b} = d{r_x3: b} {r_x13: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x14: forall d a b, d {r_x14: a} {r_x3: b} = d{r_x3: b} {r_x14: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x15: forall d a b, d {r_x15: a} {r_x3: b} = d{r_x3: b} {r_x15: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x16: forall d a b, d {r_x16: a} {r_x3: b} = d{r_x3: b} {r_x16: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x17: forall d a b, d {r_x17: a} {r_x3: b} = d{r_x3: b} {r_x17: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x18: forall d a b, d {r_x18: a} {r_x3: b} = d{r_x3: b} {r_x18: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x19: forall d a b, d {r_x19: a} {r_x3: b} = d{r_x3: b} {r_x19: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x20: forall d a b, d {r_x20: a} {r_x3: b} = d{r_x3: b} {r_x20: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x21: forall d a b, d {r_x21: a} {r_x3: b} = d{r_x3: b} {r_x21: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x22: forall d a b, d {r_x22: a} {r_x3: b} = d{r_x3: b} {r_x22: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x23: forall d a b, d {r_x23: a} {r_x3: b} = d{r_x3: b} {r_x23: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x24: forall d a b, d {r_x24: a} {r_x3: b} = d{r_x3: b} {r_x24: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x25: forall d a b, d {r_x25: a} {r_x3: b} = d{r_x3: b} {r_x25: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x26: forall d a b, d {r_x26: a} {r_x3: b} = d{r_x3: b} {r_x26: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x27: forall d a b, d {r_x27: a} {r_x3: b} = d{r_x3: b} {r_x27: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x28: forall d a b, d {r_x28: a} {r_x3: b} = d{r_x3: b} {r_x28: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x29: forall d a b, d {r_x29: a} {r_x3: b} = d{r_x3: b} {r_x29: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_x30: forall d a b, d {r_x30: a} {r_x3: b} = d{r_x3: b} {r_x30: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_lr: forall d a b, d {r_lr: a} {r_x3: b} = d{r_x3: b} {r_lr: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_cntp_ctl_el0: forall d a b, d {r_cntp_ctl_el0: a} {r_x3: b} = d{r_x3: b} {r_cntp_ctl_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_cntp_cval_el0: forall d a b, d {r_cntp_cval_el0: a} {r_x3: b} = d{r_x3: b} {r_cntp_cval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_cntp_tval_el0: forall d a b, d {r_cntp_tval_el0: a} {r_x3: b} = d{r_x3: b} {r_cntp_tval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_cntv_ctl_el0: forall d a b, d {r_cntv_ctl_el0: a} {r_x3: b} = d{r_x3: b} {r_cntv_ctl_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_cntv_cval_el0: forall d a b, d {r_cntv_cval_el0: a} {r_x3: b} = d{r_x3: b} {r_cntv_cval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_cntv_tval_el0: forall d a b, d {r_cntv_tval_el0: a} {r_x3: b} = d{r_x3: b} {r_cntv_tval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_sp_el0: forall d a b, d {r_sp_el0: a} {r_x3: b} = d{r_x3: b} {r_sp_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_pmcr_el0: forall d a b, d {r_pmcr_el0: a} {r_x3: b} = d{r_x3: b} {r_pmcr_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_pmuserenr_el0: forall d a b, d {r_pmuserenr_el0: a} {r_x3: b} = d{r_x3: b} {r_pmuserenr_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_tpidrro_el0: forall d a b, d {r_tpidrro_el0: a} {r_x3: b} = d{r_x3: b} {r_tpidrro_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_tpidr_el0: forall d a b, d {r_tpidr_el0: a} {r_x3: b} = d{r_x3: b} {r_tpidr_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_sp_el1: forall d a b, d {r_sp_el1: a} {r_x3: b} = d{r_x3: b} {r_sp_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_elr_el1: forall d a b, d {r_elr_el1: a} {r_x3: b} = d{r_x3: b} {r_elr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_spsr_el1: forall d a b, d {r_spsr_el1: a} {r_x3: b} = d{r_x3: b} {r_spsr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_csselr_el1: forall d a b, d {r_csselr_el1: a} {r_x3: b} = d{r_x3: b} {r_csselr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_sctlr_el1: forall d a b, d {r_sctlr_el1: a} {r_x3: b} = d{r_x3: b} {r_sctlr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_actlr_el1: forall d a b, d {r_actlr_el1: a} {r_x3: b} = d{r_x3: b} {r_actlr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_cpacr_el1: forall d a b, d {r_cpacr_el1: a} {r_x3: b} = d{r_x3: b} {r_cpacr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_zcr_el1: forall d a b, d {r_zcr_el1: a} {r_x3: b} = d{r_x3: b} {r_zcr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_ttbr0_el1: forall d a b, d {r_ttbr0_el1: a} {r_x3: b} = d{r_x3: b} {r_ttbr0_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_ttbr1_el1: forall d a b, d {r_ttbr1_el1: a} {r_x3: b} = d{r_x3: b} {r_ttbr1_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_tcr_el1: forall d a b, d {r_tcr_el1: a} {r_x3: b} = d{r_x3: b} {r_tcr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_esr_el1: forall d a b, d {r_esr_el1: a} {r_x3: b} = d{r_x3: b} {r_esr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_afsr0_el1: forall d a b, d {r_afsr0_el1: a} {r_x3: b} = d{r_x3: b} {r_afsr0_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_afsr1_el1: forall d a b, d {r_afsr1_el1: a} {r_x3: b} = d{r_x3: b} {r_afsr1_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_far_el1: forall d a b, d {r_far_el1: a} {r_x3: b} = d{r_x3: b} {r_far_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_mair_el1: forall d a b, d {r_mair_el1: a} {r_x3: b} = d{r_x3: b} {r_mair_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_vbar_el1: forall d a b, d {r_vbar_el1: a} {r_x3: b} = d{r_x3: b} {r_vbar_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_contextidr_el1: forall d a b, d {r_contextidr_el1: a} {r_x3: b} = d{r_x3: b} {r_contextidr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_tpidr_el1: forall d a b, d {r_tpidr_el1: a} {r_x3: b} = d{r_x3: b} {r_tpidr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_amair_el1: forall d a b, d {r_amair_el1: a} {r_x3: b} = d{r_x3: b} {r_amair_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_cntkctl_el1: forall d a b, d {r_cntkctl_el1: a} {r_x3: b} = d{r_x3: b} {r_cntkctl_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_par_el1: forall d a b, d {r_par_el1: a} {r_x3: b} = d{r_x3: b} {r_par_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_mdscr_el1: forall d a b, d {r_mdscr_el1: a} {r_x3: b} = d{r_x3: b} {r_mdscr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_mdccint_el1: forall d a b, d {r_mdccint_el1: a} {r_x3: b} = d{r_x3: b} {r_mdccint_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_disr_el1: forall d a b, d {r_disr_el1: a} {r_x3: b} = d{r_x3: b} {r_disr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_mpam0_el1: forall d a b, d {r_mpam0_el1: a} {r_x3: b} = d{r_x3: b} {r_mpam0_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_cnthctl_el2: forall d a b, d {r_cnthctl_el2: a} {r_x3: b} = d{r_x3: b} {r_cnthctl_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_cntvoff_el2: forall d a b, d {r_cntvoff_el2: a} {r_x3: b} = d{r_x3: b} {r_cntvoff_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_cntpoff_el2: forall d a b, d {r_cntpoff_el2: a} {r_x3: b} = d{r_x3: b} {r_cntpoff_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_vmpidr_el2: forall d a b, d {r_vmpidr_el2: a} {r_x3: b} = d{r_x3: b} {r_vmpidr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_vttbr_el2: forall d a b, d {r_vttbr_el2: a} {r_x3: b} = d{r_x3: b} {r_vttbr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_vtcr_el2: forall d a b, d {r_vtcr_el2: a} {r_x3: b} = d{r_x3: b} {r_vtcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_hcr_el2: forall d a b, d {r_hcr_el2: a} {r_x3: b} = d{r_x3: b} {r_hcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_actlr_el2: forall d a b, d {r_actlr_el2: a} {r_x3: b} = d{r_x3: b} {r_actlr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_afsr0_el2: forall d a b, d {r_afsr0_el2: a} {r_x3: b} = d{r_x3: b} {r_afsr0_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_afsr1_el2: forall d a b, d {r_afsr1_el2: a} {r_x3: b} = d{r_x3: b} {r_afsr1_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_amair_el2: forall d a b, d {r_amair_el2: a} {r_x3: b} = d{r_x3: b} {r_amair_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_cptr_el2: forall d a b, d {r_cptr_el2: a} {r_x3: b} = d{r_x3: b} {r_cptr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_elr_el2: forall d a b, d {r_elr_el2: a} {r_x3: b} = d{r_x3: b} {r_elr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_esr_el2: forall d a b, d {r_esr_el2: a} {r_x3: b} = d{r_x3: b} {r_esr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_far_el2: forall d a b, d {r_far_el2: a} {r_x3: b} = d{r_x3: b} {r_far_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_hacr_el2: forall d a b, d {r_hacr_el2: a} {r_x3: b} = d{r_x3: b} {r_hacr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_hpfar_el2: forall d a b, d {r_hpfar_el2: a} {r_x3: b} = d{r_x3: b} {r_hpfar_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_hstr_el2: forall d a b, d {r_hstr_el2: a} {r_x3: b} = d{r_x3: b} {r_hstr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_mair_el2: forall d a b, d {r_mair_el2: a} {r_x3: b} = d{r_x3: b} {r_mair_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_mpam_el2: forall d a b, d {r_mpam_el2: a} {r_x3: b} = d{r_x3: b} {r_mpam_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_mpamhcr_el2: forall d a b, d {r_mpamhcr_el2: a} {r_x3: b} = d{r_x3: b} {r_mpamhcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_pmscr_el2: forall d a b, d {r_pmscr_el2: a} {r_x3: b} = d{r_x3: b} {r_pmscr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_sctlr_el2: forall d a b, d {r_sctlr_el2: a} {r_x3: b} = d{r_x3: b} {r_sctlr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_scxtnum_el2: forall d a b, d {r_scxtnum_el2: a} {r_x3: b} = d{r_x3: b} {r_scxtnum_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_sp_el2: forall d a b, d {r_sp_el2: a} {r_x3: b} = d{r_x3: b} {r_sp_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_spsr_el2: forall d a b, d {r_spsr_el2: a} {r_x3: b} = d{r_x3: b} {r_spsr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_tcr_el2: forall d a b, d {r_tcr_el2: a} {r_x3: b} = d{r_x3: b} {r_tcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_tfsr_el2: forall d a b, d {r_tfsr_el2: a} {r_x3: b} = d{r_x3: b} {r_tfsr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_tpidr_el2: forall d a b, d {r_tpidr_el2: a} {r_x3: b} = d{r_x3: b} {r_tpidr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_trfcr_el2: forall d a b, d {r_trfcr_el2: a} {r_x3: b} = d{r_x3: b} {r_trfcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_ttbr0_el2: forall d a b, d {r_ttbr0_el2: a} {r_x3: b} = d{r_x3: b} {r_ttbr0_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_ttbr1_el2: forall d a b, d {r_ttbr1_el2: a} {r_x3: b} = d{r_x3: b} {r_ttbr1_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_vbar_el2: forall d a b, d {r_vbar_el2: a} {r_x3: b} = d{r_x3: b} {r_vbar_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_vdisr_el2: forall d a b, d {r_vdisr_el2: a} {r_x3: b} = d{r_x3: b} {r_vdisr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_vncr_el2: forall d a b, d {r_vncr_el2: a} {r_x3: b} = d{r_x3: b} {r_vncr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_vpidr_el2: forall d a b, d {r_vpidr_el2: a} {r_x3: b} = d{r_x3: b} {r_vpidr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_vsesr_el2: forall d a b, d {r_vsesr_el2: a} {r_x3: b} = d{r_x3: b} {r_vsesr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_vstcr_el2: forall d a b, d {r_vstcr_el2: a} {r_x3: b} = d{r_x3: b} {r_vstcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_vsttbr_el2: forall d a b, d {r_vsttbr_el2: a} {r_x3: b} = d{r_x3: b} {r_vsttbr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_zcr_el2: forall d a b, d {r_zcr_el2: a} {r_x3: b} = d{r_x3: b} {r_zcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_icc_sre_el2: forall d a b, d {r_icc_sre_el2: a} {r_x3: b} = d{r_x3: b} {r_icc_sre_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_icc_hppir1_el1: forall d a b, d {r_icc_hppir1_el1: a} {r_x3: b} = d{r_x3: b} {r_icc_hppir1_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_spsr_el3: forall d a b, d {r_spsr_el3: a} {r_x3: b} = d{r_x3: b} {r_spsr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_elr_el3: forall d a b, d {r_elr_el3: a} {r_x3: b} = d{r_x3: b} {r_elr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_esr_el3: forall d a b, d {r_esr_el3: a} {r_x3: b} = d{r_x3: b} {r_esr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_scr_el3: forall d a b, d {r_scr_el3: a} {r_x3: b} = d{r_x3: b} {r_scr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x3_r_tpidr_el3: forall d a b, d {r_tpidr_el3: a} {r_x3: b} = d{r_x3: b} {r_tpidr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x5: forall d a b, d {r_x5: a} {r_x4: b} = d{r_x4: b} {r_x5: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x6: forall d a b, d {r_x6: a} {r_x4: b} = d{r_x4: b} {r_x6: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x7: forall d a b, d {r_x7: a} {r_x4: b} = d{r_x4: b} {r_x7: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x8: forall d a b, d {r_x8: a} {r_x4: b} = d{r_x4: b} {r_x8: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x9: forall d a b, d {r_x9: a} {r_x4: b} = d{r_x4: b} {r_x9: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x10: forall d a b, d {r_x10: a} {r_x4: b} = d{r_x4: b} {r_x10: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x11: forall d a b, d {r_x11: a} {r_x4: b} = d{r_x4: b} {r_x11: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x12: forall d a b, d {r_x12: a} {r_x4: b} = d{r_x4: b} {r_x12: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x13: forall d a b, d {r_x13: a} {r_x4: b} = d{r_x4: b} {r_x13: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x14: forall d a b, d {r_x14: a} {r_x4: b} = d{r_x4: b} {r_x14: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x15: forall d a b, d {r_x15: a} {r_x4: b} = d{r_x4: b} {r_x15: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x16: forall d a b, d {r_x16: a} {r_x4: b} = d{r_x4: b} {r_x16: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x17: forall d a b, d {r_x17: a} {r_x4: b} = d{r_x4: b} {r_x17: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x18: forall d a b, d {r_x18: a} {r_x4: b} = d{r_x4: b} {r_x18: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x19: forall d a b, d {r_x19: a} {r_x4: b} = d{r_x4: b} {r_x19: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x20: forall d a b, d {r_x20: a} {r_x4: b} = d{r_x4: b} {r_x20: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x21: forall d a b, d {r_x21: a} {r_x4: b} = d{r_x4: b} {r_x21: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x22: forall d a b, d {r_x22: a} {r_x4: b} = d{r_x4: b} {r_x22: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x23: forall d a b, d {r_x23: a} {r_x4: b} = d{r_x4: b} {r_x23: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x24: forall d a b, d {r_x24: a} {r_x4: b} = d{r_x4: b} {r_x24: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x25: forall d a b, d {r_x25: a} {r_x4: b} = d{r_x4: b} {r_x25: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x26: forall d a b, d {r_x26: a} {r_x4: b} = d{r_x4: b} {r_x26: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x27: forall d a b, d {r_x27: a} {r_x4: b} = d{r_x4: b} {r_x27: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x28: forall d a b, d {r_x28: a} {r_x4: b} = d{r_x4: b} {r_x28: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x29: forall d a b, d {r_x29: a} {r_x4: b} = d{r_x4: b} {r_x29: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_x30: forall d a b, d {r_x30: a} {r_x4: b} = d{r_x4: b} {r_x30: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_lr: forall d a b, d {r_lr: a} {r_x4: b} = d{r_x4: b} {r_lr: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_cntp_ctl_el0: forall d a b, d {r_cntp_ctl_el0: a} {r_x4: b} = d{r_x4: b} {r_cntp_ctl_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_cntp_cval_el0: forall d a b, d {r_cntp_cval_el0: a} {r_x4: b} = d{r_x4: b} {r_cntp_cval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_cntp_tval_el0: forall d a b, d {r_cntp_tval_el0: a} {r_x4: b} = d{r_x4: b} {r_cntp_tval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_cntv_ctl_el0: forall d a b, d {r_cntv_ctl_el0: a} {r_x4: b} = d{r_x4: b} {r_cntv_ctl_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_cntv_cval_el0: forall d a b, d {r_cntv_cval_el0: a} {r_x4: b} = d{r_x4: b} {r_cntv_cval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_cntv_tval_el0: forall d a b, d {r_cntv_tval_el0: a} {r_x4: b} = d{r_x4: b} {r_cntv_tval_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_sp_el0: forall d a b, d {r_sp_el0: a} {r_x4: b} = d{r_x4: b} {r_sp_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_pmcr_el0: forall d a b, d {r_pmcr_el0: a} {r_x4: b} = d{r_x4: b} {r_pmcr_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_pmuserenr_el0: forall d a b, d {r_pmuserenr_el0: a} {r_x4: b} = d{r_x4: b} {r_pmuserenr_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_tpidrro_el0: forall d a b, d {r_tpidrro_el0: a} {r_x4: b} = d{r_x4: b} {r_tpidrro_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_tpidr_el0: forall d a b, d {r_tpidr_el0: a} {r_x4: b} = d{r_x4: b} {r_tpidr_el0: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_sp_el1: forall d a b, d {r_sp_el1: a} {r_x4: b} = d{r_x4: b} {r_sp_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_elr_el1: forall d a b, d {r_elr_el1: a} {r_x4: b} = d{r_x4: b} {r_elr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_spsr_el1: forall d a b, d {r_spsr_el1: a} {r_x4: b} = d{r_x4: b} {r_spsr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_csselr_el1: forall d a b, d {r_csselr_el1: a} {r_x4: b} = d{r_x4: b} {r_csselr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_sctlr_el1: forall d a b, d {r_sctlr_el1: a} {r_x4: b} = d{r_x4: b} {r_sctlr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_actlr_el1: forall d a b, d {r_actlr_el1: a} {r_x4: b} = d{r_x4: b} {r_actlr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_cpacr_el1: forall d a b, d {r_cpacr_el1: a} {r_x4: b} = d{r_x4: b} {r_cpacr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_zcr_el1: forall d a b, d {r_zcr_el1: a} {r_x4: b} = d{r_x4: b} {r_zcr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_ttbr0_el1: forall d a b, d {r_ttbr0_el1: a} {r_x4: b} = d{r_x4: b} {r_ttbr0_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_ttbr1_el1: forall d a b, d {r_ttbr1_el1: a} {r_x4: b} = d{r_x4: b} {r_ttbr1_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_tcr_el1: forall d a b, d {r_tcr_el1: a} {r_x4: b} = d{r_x4: b} {r_tcr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_esr_el1: forall d a b, d {r_esr_el1: a} {r_x4: b} = d{r_x4: b} {r_esr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_afsr0_el1: forall d a b, d {r_afsr0_el1: a} {r_x4: b} = d{r_x4: b} {r_afsr0_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_afsr1_el1: forall d a b, d {r_afsr1_el1: a} {r_x4: b} = d{r_x4: b} {r_afsr1_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_far_el1: forall d a b, d {r_far_el1: a} {r_x4: b} = d{r_x4: b} {r_far_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_mair_el1: forall d a b, d {r_mair_el1: a} {r_x4: b} = d{r_x4: b} {r_mair_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_vbar_el1: forall d a b, d {r_vbar_el1: a} {r_x4: b} = d{r_x4: b} {r_vbar_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_contextidr_el1: forall d a b, d {r_contextidr_el1: a} {r_x4: b} = d{r_x4: b} {r_contextidr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_tpidr_el1: forall d a b, d {r_tpidr_el1: a} {r_x4: b} = d{r_x4: b} {r_tpidr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_amair_el1: forall d a b, d {r_amair_el1: a} {r_x4: b} = d{r_x4: b} {r_amair_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_cntkctl_el1: forall d a b, d {r_cntkctl_el1: a} {r_x4: b} = d{r_x4: b} {r_cntkctl_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_par_el1: forall d a b, d {r_par_el1: a} {r_x4: b} = d{r_x4: b} {r_par_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_mdscr_el1: forall d a b, d {r_mdscr_el1: a} {r_x4: b} = d{r_x4: b} {r_mdscr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_mdccint_el1: forall d a b, d {r_mdccint_el1: a} {r_x4: b} = d{r_x4: b} {r_mdccint_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_disr_el1: forall d a b, d {r_disr_el1: a} {r_x4: b} = d{r_x4: b} {r_disr_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_mpam0_el1: forall d a b, d {r_mpam0_el1: a} {r_x4: b} = d{r_x4: b} {r_mpam0_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_cnthctl_el2: forall d a b, d {r_cnthctl_el2: a} {r_x4: b} = d{r_x4: b} {r_cnthctl_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_cntvoff_el2: forall d a b, d {r_cntvoff_el2: a} {r_x4: b} = d{r_x4: b} {r_cntvoff_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_cntpoff_el2: forall d a b, d {r_cntpoff_el2: a} {r_x4: b} = d{r_x4: b} {r_cntpoff_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_vmpidr_el2: forall d a b, d {r_vmpidr_el2: a} {r_x4: b} = d{r_x4: b} {r_vmpidr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_vttbr_el2: forall d a b, d {r_vttbr_el2: a} {r_x4: b} = d{r_x4: b} {r_vttbr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_vtcr_el2: forall d a b, d {r_vtcr_el2: a} {r_x4: b} = d{r_x4: b} {r_vtcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_hcr_el2: forall d a b, d {r_hcr_el2: a} {r_x4: b} = d{r_x4: b} {r_hcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_actlr_el2: forall d a b, d {r_actlr_el2: a} {r_x4: b} = d{r_x4: b} {r_actlr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_afsr0_el2: forall d a b, d {r_afsr0_el2: a} {r_x4: b} = d{r_x4: b} {r_afsr0_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_afsr1_el2: forall d a b, d {r_afsr1_el2: a} {r_x4: b} = d{r_x4: b} {r_afsr1_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_amair_el2: forall d a b, d {r_amair_el2: a} {r_x4: b} = d{r_x4: b} {r_amair_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_cptr_el2: forall d a b, d {r_cptr_el2: a} {r_x4: b} = d{r_x4: b} {r_cptr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_elr_el2: forall d a b, d {r_elr_el2: a} {r_x4: b} = d{r_x4: b} {r_elr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_esr_el2: forall d a b, d {r_esr_el2: a} {r_x4: b} = d{r_x4: b} {r_esr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_far_el2: forall d a b, d {r_far_el2: a} {r_x4: b} = d{r_x4: b} {r_far_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_hacr_el2: forall d a b, d {r_hacr_el2: a} {r_x4: b} = d{r_x4: b} {r_hacr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_hpfar_el2: forall d a b, d {r_hpfar_el2: a} {r_x4: b} = d{r_x4: b} {r_hpfar_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_hstr_el2: forall d a b, d {r_hstr_el2: a} {r_x4: b} = d{r_x4: b} {r_hstr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_mair_el2: forall d a b, d {r_mair_el2: a} {r_x4: b} = d{r_x4: b} {r_mair_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_mpam_el2: forall d a b, d {r_mpam_el2: a} {r_x4: b} = d{r_x4: b} {r_mpam_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_mpamhcr_el2: forall d a b, d {r_mpamhcr_el2: a} {r_x4: b} = d{r_x4: b} {r_mpamhcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_pmscr_el2: forall d a b, d {r_pmscr_el2: a} {r_x4: b} = d{r_x4: b} {r_pmscr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_sctlr_el2: forall d a b, d {r_sctlr_el2: a} {r_x4: b} = d{r_x4: b} {r_sctlr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_scxtnum_el2: forall d a b, d {r_scxtnum_el2: a} {r_x4: b} = d{r_x4: b} {r_scxtnum_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_sp_el2: forall d a b, d {r_sp_el2: a} {r_x4: b} = d{r_x4: b} {r_sp_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_spsr_el2: forall d a b, d {r_spsr_el2: a} {r_x4: b} = d{r_x4: b} {r_spsr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_tcr_el2: forall d a b, d {r_tcr_el2: a} {r_x4: b} = d{r_x4: b} {r_tcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_tfsr_el2: forall d a b, d {r_tfsr_el2: a} {r_x4: b} = d{r_x4: b} {r_tfsr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_tpidr_el2: forall d a b, d {r_tpidr_el2: a} {r_x4: b} = d{r_x4: b} {r_tpidr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_trfcr_el2: forall d a b, d {r_trfcr_el2: a} {r_x4: b} = d{r_x4: b} {r_trfcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_ttbr0_el2: forall d a b, d {r_ttbr0_el2: a} {r_x4: b} = d{r_x4: b} {r_ttbr0_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_ttbr1_el2: forall d a b, d {r_ttbr1_el2: a} {r_x4: b} = d{r_x4: b} {r_ttbr1_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_vbar_el2: forall d a b, d {r_vbar_el2: a} {r_x4: b} = d{r_x4: b} {r_vbar_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_vdisr_el2: forall d a b, d {r_vdisr_el2: a} {r_x4: b} = d{r_x4: b} {r_vdisr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_vncr_el2: forall d a b, d {r_vncr_el2: a} {r_x4: b} = d{r_x4: b} {r_vncr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_vpidr_el2: forall d a b, d {r_vpidr_el2: a} {r_x4: b} = d{r_x4: b} {r_vpidr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_vsesr_el2: forall d a b, d {r_vsesr_el2: a} {r_x4: b} = d{r_x4: b} {r_vsesr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_vstcr_el2: forall d a b, d {r_vstcr_el2: a} {r_x4: b} = d{r_x4: b} {r_vstcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_vsttbr_el2: forall d a b, d {r_vsttbr_el2: a} {r_x4: b} = d{r_x4: b} {r_vsttbr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_zcr_el2: forall d a b, d {r_zcr_el2: a} {r_x4: b} = d{r_x4: b} {r_zcr_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_icc_sre_el2: forall d a b, d {r_icc_sre_el2: a} {r_x4: b} = d{r_x4: b} {r_icc_sre_el2: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_icc_hppir1_el1: forall d a b, d {r_icc_hppir1_el1: a} {r_x4: b} = d{r_x4: b} {r_icc_hppir1_el1: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_spsr_el3: forall d a b, d {r_spsr_el3: a} {r_x4: b} = d{r_x4: b} {r_spsr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_elr_el3: forall d a b, d {r_elr_el3: a} {r_x4: b} = d{r_x4: b} {r_elr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_esr_el3: forall d a b, d {r_esr_el3: a} {r_x4: b} = d{r_x4: b} {r_esr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_scr_el3: forall d a b, d {r_scr_el3: a} {r_x4: b} = d{r_x4: b} {r_scr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_r_x4_r_tpidr_el3: forall d a b, d {r_tpidr_el3: a} {r_x4: b} = d{r_x4: b} {r_tpidr_el3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_log_share: forall d a b, d {share: a} {log: b} = d{log: b} {share: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_log_priv: forall d a b, d {priv: a} {log: b} = d{log: b} {priv: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_share_priv: forall d a b, d {priv: a} {share: b} = d{share: b} {priv: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CN_a_CZ: forall d a b, d {a_CZ: a} {a_CN: b} = d{a_CN: b} {a_CZ: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CN_a_CC: forall d a b, d {a_CC: a} {a_CN: b} = d{a_CN: b} {a_CC: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CN_a_CV: forall d a b, d {a_CV: a} {a_CN: b} = d{a_CN: b} {a_CV: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CN_a_DAIFCLR: forall d a b, d {a_DAIFCLR: a} {a_CN: b} = d{a_CN: b} {a_DAIFCLR: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CN_a_SP: forall d a b, d {a_SP: a} {a_CN: b} = d{a_CN: b} {a_SP: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CN_a_PC: forall d a b, d {a_PC: a} {a_CN: b} = d{a_CN: b} {a_PC: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CN_a_EL3: forall d a b, d {a_EL3: a} {a_CN: b} = d{a_CN: b} {a_EL3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CZ_a_CC: forall d a b, d {a_CC: a} {a_CZ: b} = d{a_CZ: b} {a_CC: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CZ_a_CV: forall d a b, d {a_CV: a} {a_CZ: b} = d{a_CZ: b} {a_CV: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CZ_a_DAIFCLR: forall d a b, d {a_DAIFCLR: a} {a_CZ: b} = d{a_CZ: b} {a_DAIFCLR: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CZ_a_SP: forall d a b, d {a_SP: a} {a_CZ: b} = d{a_CZ: b} {a_SP: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CZ_a_PC: forall d a b, d {a_PC: a} {a_CZ: b} = d{a_CZ: b} {a_PC: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CZ_a_EL3: forall d a b, d {a_EL3: a} {a_CZ: b} = d{a_CZ: b} {a_EL3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CC_a_CV: forall d a b, d {a_CV: a} {a_CC: b} = d{a_CC: b} {a_CV: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CC_a_DAIFCLR: forall d a b, d {a_DAIFCLR: a} {a_CC: b} = d{a_CC: b} {a_DAIFCLR: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CC_a_SP: forall d a b, d {a_SP: a} {a_CC: b} = d{a_CC: b} {a_SP: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CC_a_PC: forall d a b, d {a_PC: a} {a_CC: b} = d{a_CC: b} {a_PC: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CC_a_EL3: forall d a b, d {a_EL3: a} {a_CC: b} = d{a_CC: b} {a_EL3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CV_a_DAIFCLR: forall d a b, d {a_DAIFCLR: a} {a_CV: b} = d{a_CV: b} {a_DAIFCLR: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CV_a_SP: forall d a b, d {a_SP: a} {a_CV: b} = d{a_CV: b} {a_SP: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CV_a_PC: forall d a b, d {a_PC: a} {a_CV: b} = d{a_CV: b} {a_PC: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_CV_a_EL3: forall d a b, d {a_EL3: a} {a_CV: b} = d{a_CV: b} {a_EL3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_DAIFCLR_a_SP: forall d a b, d {a_SP: a} {a_DAIFCLR: b} = d{a_DAIFCLR: b} {a_SP: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_DAIFCLR_a_PC: forall d a b, d {a_PC: a} {a_DAIFCLR: b} = d{a_DAIFCLR: b} {a_PC: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_DAIFCLR_a_EL3: forall d a b, d {a_EL3: a} {a_DAIFCLR: b} = d{a_DAIFCLR: b} {a_EL3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_SP_a_PC: forall d a b, d {a_PC: a} {a_SP: b} = d{a_SP: b} {a_PC: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_SP_a_EL3: forall d a b, d {a_EL3: a} {a_SP: b} = d{a_SP: b} {a_EL3: a}.
Proof. intros. reflexivity. Qed.
Lemma swap_a_PC_a_EL3: forall d a b, d {a_EL3: a} {a_PC: b} = d{a_PC: b} {a_EL3: a}.
Proof. intros. reflexivity. Qed.

Ltac swap_fields :=
match goal with
| [|- context[?d {g_refcount: ?a} {g_tag: ?b}]] => rewrite (swap_g_tag_g_refcount d a b)
| [|- context[?d {g_rd: ?a} {g_tag: ?b}]] => rewrite (swap_g_tag_g_rd d a b)
| [|- context[?d {g_map_addr: ?a} {g_tag: ?b}]] => rewrite (swap_g_tag_g_map_addr d a b)
| [|- context[?d {g_rd: ?a} {g_refcount: ?b}]] => rewrite (swap_g_refcount_g_rd d a b)
| [|- context[?d {g_map_addr: ?a} {g_refcount: ?b}]] => rewrite (swap_g_refcount_g_map_addr d a b)
| [|- context[?d {g_map_addr: ?a} {g_rd: ?b}]] => rewrite (swap_g_rd_g_map_addr d a b)
| [|- context[?d {asm_regs: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_asm_regs d a b)
| [|- context[?d {id_regs: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_id_regs d a b)
| [|- context[?d {buffer: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_buffer d a b)
| [|- context[?d {ns_regs_el2: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_ns_regs_el2 d a b)
| [|- context[?d {realm_params: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_realm_params d a b)
| [|- context[?d {rec_params: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_rec_params d a b)
| [|- context[?d {rec_run: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_rec_run d a b)
| [|- context[?d {retval: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_retval d a b)
| [|- context[?d {locked_g: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_locked_g d a b)
| [|- context[?d {wi_last_level: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_wi_last_level d a b)
| [|- context[?d {wi_llt: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_wi_llt d a b)
| [|- context[?d {wi_index: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_wi_index d a b)
| [|- context[?d {rvic_x0: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_rvic_x0 d a b)
| [|- context[?d {rvic_x1: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_rvic_x1 d a b)
| [|- context[?d {rvic_x2: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_rvic_x2 d a b)
| [|- context[?d {rvic_x3: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_rvic_x3 d a b)
| [|- context[?d {rvic_target: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_rvic_target d a b)
| [|- context[?d {rvic_ns_notify: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_rvic_ns_notify d a b)
| [|- context[?d {psci_x0: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_psci_x0 d a b)
| [|- context[?d {psci_x1: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_cur_rec d a b)
| [|- context[?d {mstage: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_mstage d a b)
| [|- context[?d {trap_reason: ?a} {cpu_regs: ?b}]] => rewrite (swap_cpu_regs_trap_reason d a b)
| [|- context[?d {id_regs: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_id_regs d a b)
| [|- context[?d {buffer: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_buffer d a b)
| [|- context[?d {ns_regs_el2: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_ns_regs_el2 d a b)
| [|- context[?d {realm_params: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_realm_params d a b)
| [|- context[?d {rec_params: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_rec_params d a b)
| [|- context[?d {rec_run: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_rec_run d a b)
| [|- context[?d {retval: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_retval d a b)
| [|- context[?d {locked_g: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_locked_g d a b)
| [|- context[?d {wi_last_level: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_wi_last_level d a b)
| [|- context[?d {wi_llt: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_wi_llt d a b)
| [|- context[?d {wi_index: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_wi_index d a b)
| [|- context[?d {rvic_x0: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_rvic_x0 d a b)
| [|- context[?d {rvic_x1: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_rvic_x1 d a b)
| [|- context[?d {rvic_x2: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_rvic_x2 d a b)
| [|- context[?d {rvic_x3: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_rvic_x3 d a b)
| [|- context[?d {rvic_target: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_rvic_target d a b)
| [|- context[?d {rvic_ns_notify: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_rvic_ns_notify d a b)
| [|- context[?d {psci_x0: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_psci_x0 d a b)
| [|- context[?d {psci_x1: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_cur_rec d a b)
| [|- context[?d {mstage: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_mstage d a b)
| [|- context[?d {trap_reason: ?a} {asm_regs: ?b}]] => rewrite (swap_asm_regs_trap_reason d a b)
| [|- context[?d {buffer: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_buffer d a b)
| [|- context[?d {ns_regs_el2: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_ns_regs_el2 d a b)
| [|- context[?d {realm_params: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_realm_params d a b)
| [|- context[?d {rec_params: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_rec_params d a b)
| [|- context[?d {rec_run: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_rec_run d a b)
| [|- context[?d {retval: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_retval d a b)
| [|- context[?d {locked_g: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_locked_g d a b)
| [|- context[?d {wi_last_level: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_wi_last_level d a b)
| [|- context[?d {wi_llt: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_wi_llt d a b)
| [|- context[?d {wi_index: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_wi_index d a b)
| [|- context[?d {rvic_x0: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_rvic_x0 d a b)
| [|- context[?d {rvic_x1: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_rvic_x1 d a b)
| [|- context[?d {rvic_x2: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_rvic_x2 d a b)
| [|- context[?d {rvic_x3: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_rvic_x3 d a b)
| [|- context[?d {rvic_target: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_rvic_target d a b)
| [|- context[?d {rvic_ns_notify: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_rvic_ns_notify d a b)
| [|- context[?d {psci_x0: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_psci_x0 d a b)
| [|- context[?d {psci_x1: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_cur_rec d a b)
| [|- context[?d {mstage: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_mstage d a b)
| [|- context[?d {trap_reason: ?a} {id_regs: ?b}]] => rewrite (swap_id_regs_trap_reason d a b)
| [|- context[?d {ns_regs_el2: ?a} {buffer: ?b}]] => rewrite (swap_buffer_ns_regs_el2 d a b)
| [|- context[?d {realm_params: ?a} {buffer: ?b}]] => rewrite (swap_buffer_realm_params d a b)
| [|- context[?d {rec_params: ?a} {buffer: ?b}]] => rewrite (swap_buffer_rec_params d a b)
| [|- context[?d {rec_run: ?a} {buffer: ?b}]] => rewrite (swap_buffer_rec_run d a b)
| [|- context[?d {retval: ?a} {buffer: ?b}]] => rewrite (swap_buffer_retval d a b)
| [|- context[?d {locked_g: ?a} {buffer: ?b}]] => rewrite (swap_buffer_locked_g d a b)
| [|- context[?d {wi_last_level: ?a} {buffer: ?b}]] => rewrite (swap_buffer_wi_last_level d a b)
| [|- context[?d {wi_llt: ?a} {buffer: ?b}]] => rewrite (swap_buffer_wi_llt d a b)
| [|- context[?d {wi_index: ?a} {buffer: ?b}]] => rewrite (swap_buffer_wi_index d a b)
| [|- context[?d {rvic_x0: ?a} {buffer: ?b}]] => rewrite (swap_buffer_rvic_x0 d a b)
| [|- context[?d {rvic_x1: ?a} {buffer: ?b}]] => rewrite (swap_buffer_rvic_x1 d a b)
| [|- context[?d {rvic_x2: ?a} {buffer: ?b}]] => rewrite (swap_buffer_rvic_x2 d a b)
| [|- context[?d {rvic_x3: ?a} {buffer: ?b}]] => rewrite (swap_buffer_rvic_x3 d a b)
| [|- context[?d {rvic_target: ?a} {buffer: ?b}]] => rewrite (swap_buffer_rvic_target d a b)
| [|- context[?d {rvic_ns_notify: ?a} {buffer: ?b}]] => rewrite (swap_buffer_rvic_ns_notify d a b)
| [|- context[?d {psci_x0: ?a} {buffer: ?b}]] => rewrite (swap_buffer_psci_x0 d a b)
| [|- context[?d {psci_x1: ?a} {buffer: ?b}]] => rewrite (swap_buffer_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {buffer: ?b}]] => rewrite (swap_buffer_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {buffer: ?b}]] => rewrite (swap_buffer_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {buffer: ?b}]] => rewrite (swap_buffer_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {buffer: ?b}]] => rewrite (swap_buffer_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {buffer: ?b}]] => rewrite (swap_buffer_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {buffer: ?b}]] => rewrite (swap_buffer_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {buffer: ?b}]] => rewrite (swap_buffer_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {buffer: ?b}]] => rewrite (swap_buffer_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {buffer: ?b}]] => rewrite (swap_buffer_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {buffer: ?b}]] => rewrite (swap_buffer_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {buffer: ?b}]] => rewrite (swap_buffer_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {buffer: ?b}]] => rewrite (swap_buffer_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {buffer: ?b}]] => rewrite (swap_buffer_cur_rec d a b)
| [|- context[?d {mstage: ?a} {buffer: ?b}]] => rewrite (swap_buffer_mstage d a b)
| [|- context[?d {trap_reason: ?a} {buffer: ?b}]] => rewrite (swap_buffer_trap_reason d a b)
| [|- context[?d {realm_params: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_realm_params d a b)
| [|- context[?d {rec_params: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_rec_params d a b)
| [|- context[?d {rec_run: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_rec_run d a b)
| [|- context[?d {retval: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_retval d a b)
| [|- context[?d {locked_g: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_locked_g d a b)
| [|- context[?d {wi_last_level: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_wi_last_level d a b)
| [|- context[?d {wi_llt: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_wi_llt d a b)
| [|- context[?d {wi_index: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_wi_index d a b)
| [|- context[?d {rvic_x0: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_rvic_x0 d a b)
| [|- context[?d {rvic_x1: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_rvic_x1 d a b)
| [|- context[?d {rvic_x2: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_rvic_x2 d a b)
| [|- context[?d {rvic_x3: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_rvic_x3 d a b)
| [|- context[?d {rvic_target: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_rvic_target d a b)
| [|- context[?d {rvic_ns_notify: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_rvic_ns_notify d a b)
| [|- context[?d {psci_x0: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_psci_x0 d a b)
| [|- context[?d {psci_x1: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_cur_rec d a b)
| [|- context[?d {mstage: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_mstage d a b)
| [|- context[?d {trap_reason: ?a} {ns_regs_el2: ?b}]] => rewrite (swap_ns_regs_el2_trap_reason d a b)
| [|- context[?d {rec_params: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_rec_params d a b)
| [|- context[?d {rec_run: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_rec_run d a b)
| [|- context[?d {retval: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_retval d a b)
| [|- context[?d {locked_g: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_locked_g d a b)
| [|- context[?d {wi_last_level: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_wi_last_level d a b)
| [|- context[?d {wi_llt: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_wi_llt d a b)
| [|- context[?d {wi_index: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_wi_index d a b)
| [|- context[?d {rvic_x0: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_rvic_x0 d a b)
| [|- context[?d {rvic_x1: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_rvic_x1 d a b)
| [|- context[?d {rvic_x2: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_rvic_x2 d a b)
| [|- context[?d {rvic_x3: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_rvic_x3 d a b)
| [|- context[?d {rvic_target: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_rvic_target d a b)
| [|- context[?d {rvic_ns_notify: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_rvic_ns_notify d a b)
| [|- context[?d {psci_x0: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_psci_x0 d a b)
| [|- context[?d {psci_x1: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_cur_rec d a b)
| [|- context[?d {mstage: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_mstage d a b)
| [|- context[?d {trap_reason: ?a} {realm_params: ?b}]] => rewrite (swap_realm_params_trap_reason d a b)
| [|- context[?d {rec_run: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_rec_run d a b)
| [|- context[?d {retval: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_retval d a b)
| [|- context[?d {locked_g: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_locked_g d a b)
| [|- context[?d {wi_last_level: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_wi_last_level d a b)
| [|- context[?d {wi_llt: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_wi_llt d a b)
| [|- context[?d {wi_index: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_wi_index d a b)
| [|- context[?d {rvic_x0: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_rvic_x0 d a b)
| [|- context[?d {rvic_x1: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_rvic_x1 d a b)
| [|- context[?d {rvic_x2: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_rvic_x2 d a b)
| [|- context[?d {rvic_x3: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_rvic_x3 d a b)
| [|- context[?d {rvic_target: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_rvic_target d a b)
| [|- context[?d {rvic_ns_notify: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_rvic_ns_notify d a b)
| [|- context[?d {psci_x0: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_psci_x0 d a b)
| [|- context[?d {psci_x1: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_cur_rec d a b)
| [|- context[?d {mstage: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_mstage d a b)
| [|- context[?d {trap_reason: ?a} {rec_params: ?b}]] => rewrite (swap_rec_params_trap_reason d a b)
| [|- context[?d {retval: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_retval d a b)
| [|- context[?d {locked_g: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_locked_g d a b)
| [|- context[?d {wi_last_level: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_wi_last_level d a b)
| [|- context[?d {wi_llt: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_wi_llt d a b)
| [|- context[?d {wi_index: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_wi_index d a b)
| [|- context[?d {rvic_x0: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_rvic_x0 d a b)
| [|- context[?d {rvic_x1: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_rvic_x1 d a b)
| [|- context[?d {rvic_x2: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_rvic_x2 d a b)
| [|- context[?d {rvic_x3: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_rvic_x3 d a b)
| [|- context[?d {rvic_target: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_rvic_target d a b)
| [|- context[?d {rvic_ns_notify: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_rvic_ns_notify d a b)
| [|- context[?d {psci_x0: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_psci_x0 d a b)
| [|- context[?d {psci_x1: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_cur_rec d a b)
| [|- context[?d {mstage: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_mstage d a b)
| [|- context[?d {trap_reason: ?a} {rec_run: ?b}]] => rewrite (swap_rec_run_trap_reason d a b)
| [|- context[?d {locked_g: ?a} {retval: ?b}]] => rewrite (swap_retval_locked_g d a b)
| [|- context[?d {wi_last_level: ?a} {retval: ?b}]] => rewrite (swap_retval_wi_last_level d a b)
| [|- context[?d {wi_llt: ?a} {retval: ?b}]] => rewrite (swap_retval_wi_llt d a b)
| [|- context[?d {wi_index: ?a} {retval: ?b}]] => rewrite (swap_retval_wi_index d a b)
| [|- context[?d {rvic_x0: ?a} {retval: ?b}]] => rewrite (swap_retval_rvic_x0 d a b)
| [|- context[?d {rvic_x1: ?a} {retval: ?b}]] => rewrite (swap_retval_rvic_x1 d a b)
| [|- context[?d {rvic_x2: ?a} {retval: ?b}]] => rewrite (swap_retval_rvic_x2 d a b)
| [|- context[?d {rvic_x3: ?a} {retval: ?b}]] => rewrite (swap_retval_rvic_x3 d a b)
| [|- context[?d {rvic_target: ?a} {retval: ?b}]] => rewrite (swap_retval_rvic_target d a b)
| [|- context[?d {rvic_ns_notify: ?a} {retval: ?b}]] => rewrite (swap_retval_rvic_ns_notify d a b)
| [|- context[?d {psci_x0: ?a} {retval: ?b}]] => rewrite (swap_retval_psci_x0 d a b)
| [|- context[?d {psci_x1: ?a} {retval: ?b}]] => rewrite (swap_retval_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {retval: ?b}]] => rewrite (swap_retval_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {retval: ?b}]] => rewrite (swap_retval_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {retval: ?b}]] => rewrite (swap_retval_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {retval: ?b}]] => rewrite (swap_retval_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {retval: ?b}]] => rewrite (swap_retval_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {retval: ?b}]] => rewrite (swap_retval_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {retval: ?b}]] => rewrite (swap_retval_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {retval: ?b}]] => rewrite (swap_retval_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {retval: ?b}]] => rewrite (swap_retval_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {retval: ?b}]] => rewrite (swap_retval_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {retval: ?b}]] => rewrite (swap_retval_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {retval: ?b}]] => rewrite (swap_retval_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {retval: ?b}]] => rewrite (swap_retval_cur_rec d a b)
| [|- context[?d {mstage: ?a} {retval: ?b}]] => rewrite (swap_retval_mstage d a b)
| [|- context[?d {trap_reason: ?a} {retval: ?b}]] => rewrite (swap_retval_trap_reason d a b)
| [|- context[?d {wi_last_level: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_wi_last_level d a b)
| [|- context[?d {wi_llt: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_wi_llt d a b)
| [|- context[?d {wi_index: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_wi_index d a b)
| [|- context[?d {rvic_x0: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_rvic_x0 d a b)
| [|- context[?d {rvic_x1: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_rvic_x1 d a b)
| [|- context[?d {rvic_x2: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_rvic_x2 d a b)
| [|- context[?d {rvic_x3: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_rvic_x3 d a b)
| [|- context[?d {rvic_target: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_rvic_target d a b)
| [|- context[?d {rvic_ns_notify: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_rvic_ns_notify d a b)
| [|- context[?d {psci_x0: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_psci_x0 d a b)
| [|- context[?d {psci_x1: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_cur_rec d a b)
| [|- context[?d {mstage: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_mstage d a b)
| [|- context[?d {trap_reason: ?a} {locked_g: ?b}]] => rewrite (swap_locked_g_trap_reason d a b)
| [|- context[?d {wi_llt: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_wi_llt d a b)
| [|- context[?d {wi_index: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_wi_index d a b)
| [|- context[?d {rvic_x0: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_rvic_x0 d a b)
| [|- context[?d {rvic_x1: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_rvic_x1 d a b)
| [|- context[?d {rvic_x2: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_rvic_x2 d a b)
| [|- context[?d {rvic_x3: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_rvic_x3 d a b)
| [|- context[?d {rvic_target: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_rvic_target d a b)
| [|- context[?d {rvic_ns_notify: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_rvic_ns_notify d a b)
| [|- context[?d {psci_x0: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_psci_x0 d a b)
| [|- context[?d {psci_x1: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_cur_rec d a b)
| [|- context[?d {mstage: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_mstage d a b)
| [|- context[?d {trap_reason: ?a} {wi_last_level: ?b}]] => rewrite (swap_wi_last_level_trap_reason d a b)
| [|- context[?d {wi_index: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_wi_index d a b)
| [|- context[?d {rvic_x0: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_rvic_x0 d a b)
| [|- context[?d {rvic_x1: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_rvic_x1 d a b)
| [|- context[?d {rvic_x2: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_rvic_x2 d a b)
| [|- context[?d {rvic_x3: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_rvic_x3 d a b)
| [|- context[?d {rvic_target: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_rvic_target d a b)
| [|- context[?d {rvic_ns_notify: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_rvic_ns_notify d a b)
| [|- context[?d {psci_x0: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_psci_x0 d a b)
| [|- context[?d {psci_x1: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_cur_rec d a b)
| [|- context[?d {mstage: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_mstage d a b)
| [|- context[?d {trap_reason: ?a} {wi_llt: ?b}]] => rewrite (swap_wi_llt_trap_reason d a b)
| [|- context[?d {rvic_x0: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_rvic_x0 d a b)
| [|- context[?d {rvic_x1: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_rvic_x1 d a b)
| [|- context[?d {rvic_x2: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_rvic_x2 d a b)
| [|- context[?d {rvic_x3: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_rvic_x3 d a b)
| [|- context[?d {rvic_target: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_rvic_target d a b)
| [|- context[?d {rvic_ns_notify: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_rvic_ns_notify d a b)
| [|- context[?d {psci_x0: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_psci_x0 d a b)
| [|- context[?d {psci_x1: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_cur_rec d a b)
| [|- context[?d {mstage: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_mstage d a b)
| [|- context[?d {trap_reason: ?a} {wi_index: ?b}]] => rewrite (swap_wi_index_trap_reason d a b)
| [|- context[?d {rvic_x1: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_rvic_x1 d a b)
| [|- context[?d {rvic_x2: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_rvic_x2 d a b)
| [|- context[?d {rvic_x3: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_rvic_x3 d a b)
| [|- context[?d {rvic_target: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_rvic_target d a b)
| [|- context[?d {rvic_ns_notify: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_rvic_ns_notify d a b)
| [|- context[?d {psci_x0: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_psci_x0 d a b)
| [|- context[?d {psci_x1: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_cur_rec d a b)
| [|- context[?d {mstage: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_mstage d a b)
| [|- context[?d {trap_reason: ?a} {rvic_x0: ?b}]] => rewrite (swap_rvic_x0_trap_reason d a b)
| [|- context[?d {rvic_x2: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_rvic_x2 d a b)
| [|- context[?d {rvic_x3: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_rvic_x3 d a b)
| [|- context[?d {rvic_target: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_rvic_target d a b)
| [|- context[?d {rvic_ns_notify: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_rvic_ns_notify d a b)
| [|- context[?d {psci_x0: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_psci_x0 d a b)
| [|- context[?d {psci_x1: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_cur_rec d a b)
| [|- context[?d {mstage: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_mstage d a b)
| [|- context[?d {trap_reason: ?a} {rvic_x1: ?b}]] => rewrite (swap_rvic_x1_trap_reason d a b)
| [|- context[?d {rvic_x3: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_rvic_x3 d a b)
| [|- context[?d {rvic_target: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_rvic_target d a b)
| [|- context[?d {rvic_ns_notify: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_rvic_ns_notify d a b)
| [|- context[?d {psci_x0: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_psci_x0 d a b)
| [|- context[?d {psci_x1: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_cur_rec d a b)
| [|- context[?d {mstage: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_mstage d a b)
| [|- context[?d {trap_reason: ?a} {rvic_x2: ?b}]] => rewrite (swap_rvic_x2_trap_reason d a b)
| [|- context[?d {rvic_target: ?a} {rvic_x3: ?b}]] => rewrite (swap_rvic_x3_rvic_target d a b)
| [|- context[?d {rvic_ns_notify: ?a} {rvic_x3: ?b}]] => rewrite (swap_rvic_x3_rvic_ns_notify d a b)
| [|- context[?d {psci_x0: ?a} {rvic_x3: ?b}]] => rewrite (swap_rvic_x3_psci_x0 d a b)
| [|- context[?d {psci_x1: ?a} {rvic_x3: ?b}]] => rewrite (swap_rvic_x3_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {rvic_x3: ?b}]] => rewrite (swap_rvic_x3_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {rvic_x3: ?b}]] => rewrite (swap_rvic_x3_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {rvic_x3: ?b}]] => rewrite (swap_rvic_x3_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {rvic_x3: ?b}]] => rewrite (swap_rvic_x3_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {rvic_x3: ?b}]] => rewrite (swap_rvic_x3_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {rvic_x3: ?b}]] => rewrite (swap_rvic_x3_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {rvic_x3: ?b}]] => rewrite (swap_rvic_x3_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {rvic_x3: ?b}]] => rewrite (swap_rvic_x3_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {rvic_x3: ?b}]] => rewrite (swap_rvic_x3_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {rvic_x3: ?b}]] => rewrite (swap_rvic_x3_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {rvic_x3: ?b}]] => rewrite (swap_rvic_x3_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {rvic_x3: ?b}]] => rewrite (swap_rvic_x3_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {rvic_x3: ?b}]] => rewrite (swap_rvic_x3_cur_rec d a b)
| [|- context[?d {mstage: ?a} {rvic_x3: ?b}]] => rewrite (swap_rvic_x3_mstage d a b)
| [|- context[?d {trap_reason: ?a} {rvic_x3: ?b}]] => rewrite (swap_rvic_x3_trap_reason d a b)
| [|- context[?d {rvic_ns_notify: ?a} {rvic_target: ?b}]] => rewrite (swap_rvic_target_rvic_ns_notify d a b)
| [|- context[?d {psci_x0: ?a} {rvic_target: ?b}]] => rewrite (swap_rvic_target_psci_x0 d a b)
| [|- context[?d {psci_x1: ?a} {rvic_target: ?b}]] => rewrite (swap_rvic_target_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {rvic_target: ?b}]] => rewrite (swap_rvic_target_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {rvic_target: ?b}]] => rewrite (swap_rvic_target_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {rvic_target: ?b}]] => rewrite (swap_rvic_target_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {rvic_target: ?b}]] => rewrite (swap_rvic_target_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {rvic_target: ?b}]] => rewrite (swap_rvic_target_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {rvic_target: ?b}]] => rewrite (swap_rvic_target_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {rvic_target: ?b}]] => rewrite (swap_rvic_target_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {rvic_target: ?b}]] => rewrite (swap_rvic_target_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {rvic_target: ?b}]] => rewrite (swap_rvic_target_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {rvic_target: ?b}]] => rewrite (swap_rvic_target_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {rvic_target: ?b}]] => rewrite (swap_rvic_target_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {rvic_target: ?b}]] => rewrite (swap_rvic_target_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {rvic_target: ?b}]] => rewrite (swap_rvic_target_cur_rec d a b)
| [|- context[?d {mstage: ?a} {rvic_target: ?b}]] => rewrite (swap_rvic_target_mstage d a b)
| [|- context[?d {trap_reason: ?a} {rvic_target: ?b}]] => rewrite (swap_rvic_target_trap_reason d a b)
| [|- context[?d {psci_x0: ?a} {rvic_ns_notify: ?b}]] => rewrite (swap_rvic_ns_notify_psci_x0 d a b)
| [|- context[?d {psci_x1: ?a} {rvic_ns_notify: ?b}]] => rewrite (swap_rvic_ns_notify_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {rvic_ns_notify: ?b}]] => rewrite (swap_rvic_ns_notify_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {rvic_ns_notify: ?b}]] => rewrite (swap_rvic_ns_notify_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {rvic_ns_notify: ?b}]] => rewrite (swap_rvic_ns_notify_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {rvic_ns_notify: ?b}]] => rewrite (swap_rvic_ns_notify_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {rvic_ns_notify: ?b}]] => rewrite (swap_rvic_ns_notify_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {rvic_ns_notify: ?b}]] => rewrite (swap_rvic_ns_notify_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {rvic_ns_notify: ?b}]] => rewrite (swap_rvic_ns_notify_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {rvic_ns_notify: ?b}]] => rewrite (swap_rvic_ns_notify_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {rvic_ns_notify: ?b}]] => rewrite (swap_rvic_ns_notify_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {rvic_ns_notify: ?b}]] => rewrite (swap_rvic_ns_notify_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {rvic_ns_notify: ?b}]] => rewrite (swap_rvic_ns_notify_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {rvic_ns_notify: ?b}]] => rewrite (swap_rvic_ns_notify_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {rvic_ns_notify: ?b}]] => rewrite (swap_rvic_ns_notify_cur_rec d a b)
| [|- context[?d {mstage: ?a} {rvic_ns_notify: ?b}]] => rewrite (swap_rvic_ns_notify_mstage d a b)
| [|- context[?d {trap_reason: ?a} {rvic_ns_notify: ?b}]] => rewrite (swap_rvic_ns_notify_trap_reason d a b)
| [|- context[?d {psci_x1: ?a} {psci_x0: ?b}]] => rewrite (swap_psci_x0_psci_x1 d a b)
| [|- context[?d {psci_x2: ?a} {psci_x0: ?b}]] => rewrite (swap_psci_x0_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {psci_x0: ?b}]] => rewrite (swap_psci_x0_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {psci_x0: ?b}]] => rewrite (swap_psci_x0_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {psci_x0: ?b}]] => rewrite (swap_psci_x0_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {psci_x0: ?b}]] => rewrite (swap_psci_x0_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {psci_x0: ?b}]] => rewrite (swap_psci_x0_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {psci_x0: ?b}]] => rewrite (swap_psci_x0_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {psci_x0: ?b}]] => rewrite (swap_psci_x0_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {psci_x0: ?b}]] => rewrite (swap_psci_x0_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {psci_x0: ?b}]] => rewrite (swap_psci_x0_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {psci_x0: ?b}]] => rewrite (swap_psci_x0_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {psci_x0: ?b}]] => rewrite (swap_psci_x0_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {psci_x0: ?b}]] => rewrite (swap_psci_x0_cur_rec d a b)
| [|- context[?d {mstage: ?a} {psci_x0: ?b}]] => rewrite (swap_psci_x0_mstage d a b)
| [|- context[?d {trap_reason: ?a} {psci_x0: ?b}]] => rewrite (swap_psci_x0_trap_reason d a b)
| [|- context[?d {psci_x2: ?a} {psci_x1: ?b}]] => rewrite (swap_psci_x1_psci_x2 d a b)
| [|- context[?d {psci_x3: ?a} {psci_x1: ?b}]] => rewrite (swap_psci_x1_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {psci_x1: ?b}]] => rewrite (swap_psci_x1_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {psci_x1: ?b}]] => rewrite (swap_psci_x1_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {psci_x1: ?b}]] => rewrite (swap_psci_x1_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {psci_x1: ?b}]] => rewrite (swap_psci_x1_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {psci_x1: ?b}]] => rewrite (swap_psci_x1_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {psci_x1: ?b}]] => rewrite (swap_psci_x1_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {psci_x1: ?b}]] => rewrite (swap_psci_x1_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {psci_x1: ?b}]] => rewrite (swap_psci_x1_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {psci_x1: ?b}]] => rewrite (swap_psci_x1_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {psci_x1: ?b}]] => rewrite (swap_psci_x1_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {psci_x1: ?b}]] => rewrite (swap_psci_x1_cur_rec d a b)
| [|- context[?d {mstage: ?a} {psci_x1: ?b}]] => rewrite (swap_psci_x1_mstage d a b)
| [|- context[?d {trap_reason: ?a} {psci_x1: ?b}]] => rewrite (swap_psci_x1_trap_reason d a b)
| [|- context[?d {psci_x3: ?a} {psci_x2: ?b}]] => rewrite (swap_psci_x2_psci_x3 d a b)
| [|- context[?d {psci_forward_x0: ?a} {psci_x2: ?b}]] => rewrite (swap_psci_x2_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {psci_x2: ?b}]] => rewrite (swap_psci_x2_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {psci_x2: ?b}]] => rewrite (swap_psci_x2_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {psci_x2: ?b}]] => rewrite (swap_psci_x2_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {psci_x2: ?b}]] => rewrite (swap_psci_x2_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {psci_x2: ?b}]] => rewrite (swap_psci_x2_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {psci_x2: ?b}]] => rewrite (swap_psci_x2_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {psci_x2: ?b}]] => rewrite (swap_psci_x2_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {psci_x2: ?b}]] => rewrite (swap_psci_x2_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {psci_x2: ?b}]] => rewrite (swap_psci_x2_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {psci_x2: ?b}]] => rewrite (swap_psci_x2_cur_rec d a b)
| [|- context[?d {mstage: ?a} {psci_x2: ?b}]] => rewrite (swap_psci_x2_mstage d a b)
| [|- context[?d {trap_reason: ?a} {psci_x2: ?b}]] => rewrite (swap_psci_x2_trap_reason d a b)
| [|- context[?d {psci_forward_x0: ?a} {psci_x3: ?b}]] => rewrite (swap_psci_x3_psci_forward_x0 d a b)
| [|- context[?d {psci_forward_x1: ?a} {psci_x3: ?b}]] => rewrite (swap_psci_x3_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {psci_x3: ?b}]] => rewrite (swap_psci_x3_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {psci_x3: ?b}]] => rewrite (swap_psci_x3_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {psci_x3: ?b}]] => rewrite (swap_psci_x3_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {psci_x3: ?b}]] => rewrite (swap_psci_x3_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {psci_x3: ?b}]] => rewrite (swap_psci_x3_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {psci_x3: ?b}]] => rewrite (swap_psci_x3_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {psci_x3: ?b}]] => rewrite (swap_psci_x3_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {psci_x3: ?b}]] => rewrite (swap_psci_x3_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {psci_x3: ?b}]] => rewrite (swap_psci_x3_cur_rec d a b)
| [|- context[?d {mstage: ?a} {psci_x3: ?b}]] => rewrite (swap_psci_x3_mstage d a b)
| [|- context[?d {trap_reason: ?a} {psci_x3: ?b}]] => rewrite (swap_psci_x3_trap_reason d a b)
| [|- context[?d {psci_forward_x1: ?a} {psci_forward_x0: ?b}]] => rewrite (swap_psci_forward_x0_psci_forward_x1 d a b)
| [|- context[?d {psci_forward_x2: ?a} {psci_forward_x0: ?b}]] => rewrite (swap_psci_forward_x0_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {psci_forward_x0: ?b}]] => rewrite (swap_psci_forward_x0_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {psci_forward_x0: ?b}]] => rewrite (swap_psci_forward_x0_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {psci_forward_x0: ?b}]] => rewrite (swap_psci_forward_x0_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {psci_forward_x0: ?b}]] => rewrite (swap_psci_forward_x0_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {psci_forward_x0: ?b}]] => rewrite (swap_psci_forward_x0_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {psci_forward_x0: ?b}]] => rewrite (swap_psci_forward_x0_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {psci_forward_x0: ?b}]] => rewrite (swap_psci_forward_x0_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {psci_forward_x0: ?b}]] => rewrite (swap_psci_forward_x0_cur_rec d a b)
| [|- context[?d {mstage: ?a} {psci_forward_x0: ?b}]] => rewrite (swap_psci_forward_x0_mstage d a b)
| [|- context[?d {trap_reason: ?a} {psci_forward_x0: ?b}]] => rewrite (swap_psci_forward_x0_trap_reason d a b)
| [|- context[?d {psci_forward_x2: ?a} {psci_forward_x1: ?b}]] => rewrite (swap_psci_forward_x1_psci_forward_x2 d a b)
| [|- context[?d {psci_forward_x3: ?a} {psci_forward_x1: ?b}]] => rewrite (swap_psci_forward_x1_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {psci_forward_x1: ?b}]] => rewrite (swap_psci_forward_x1_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {psci_forward_x1: ?b}]] => rewrite (swap_psci_forward_x1_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {psci_forward_x1: ?b}]] => rewrite (swap_psci_forward_x1_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {psci_forward_x1: ?b}]] => rewrite (swap_psci_forward_x1_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {psci_forward_x1: ?b}]] => rewrite (swap_psci_forward_x1_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {psci_forward_x1: ?b}]] => rewrite (swap_psci_forward_x1_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {psci_forward_x1: ?b}]] => rewrite (swap_psci_forward_x1_cur_rec d a b)
| [|- context[?d {mstage: ?a} {psci_forward_x1: ?b}]] => rewrite (swap_psci_forward_x1_mstage d a b)
| [|- context[?d {trap_reason: ?a} {psci_forward_x1: ?b}]] => rewrite (swap_psci_forward_x1_trap_reason d a b)
| [|- context[?d {psci_forward_x3: ?a} {psci_forward_x2: ?b}]] => rewrite (swap_psci_forward_x2_psci_forward_x3 d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {psci_forward_x2: ?b}]] => rewrite (swap_psci_forward_x2_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {psci_forward_x2: ?b}]] => rewrite (swap_psci_forward_x2_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {psci_forward_x2: ?b}]] => rewrite (swap_psci_forward_x2_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {psci_forward_x2: ?b}]] => rewrite (swap_psci_forward_x2_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {psci_forward_x2: ?b}]] => rewrite (swap_psci_forward_x2_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {psci_forward_x2: ?b}]] => rewrite (swap_psci_forward_x2_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {psci_forward_x2: ?b}]] => rewrite (swap_psci_forward_x2_cur_rec d a b)
| [|- context[?d {mstage: ?a} {psci_forward_x2: ?b}]] => rewrite (swap_psci_forward_x2_mstage d a b)
| [|- context[?d {trap_reason: ?a} {psci_forward_x2: ?b}]] => rewrite (swap_psci_forward_x2_trap_reason d a b)
| [|- context[?d {psci_forward_psci_call: ?a} {psci_forward_x3: ?b}]] => rewrite (swap_psci_forward_x3_psci_forward_psci_call d a b)
| [|- context[?d {target_rec: ?a} {psci_forward_x3: ?b}]] => rewrite (swap_psci_forward_x3_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {psci_forward_x3: ?b}]] => rewrite (swap_psci_forward_x3_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {psci_forward_x3: ?b}]] => rewrite (swap_psci_forward_x3_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {psci_forward_x3: ?b}]] => rewrite (swap_psci_forward_x3_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {psci_forward_x3: ?b}]] => rewrite (swap_psci_forward_x3_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {psci_forward_x3: ?b}]] => rewrite (swap_psci_forward_x3_cur_rec d a b)
| [|- context[?d {mstage: ?a} {psci_forward_x3: ?b}]] => rewrite (swap_psci_forward_x3_mstage d a b)
| [|- context[?d {trap_reason: ?a} {psci_forward_x3: ?b}]] => rewrite (swap_psci_forward_x3_trap_reason d a b)
| [|- context[?d {target_rec: ?a} {psci_forward_psci_call: ?b}]] => rewrite (swap_psci_forward_psci_call_target_rec d a b)
| [|- context[?d {el2_stack: ?a} {psci_forward_psci_call: ?b}]] => rewrite (swap_psci_forward_psci_call_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {psci_forward_psci_call: ?b}]] => rewrite (swap_psci_forward_psci_call_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {psci_forward_psci_call: ?b}]] => rewrite (swap_psci_forward_psci_call_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {psci_forward_psci_call: ?b}]] => rewrite (swap_psci_forward_psci_call_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {psci_forward_psci_call: ?b}]] => rewrite (swap_psci_forward_psci_call_cur_rec d a b)
| [|- context[?d {mstage: ?a} {psci_forward_psci_call: ?b}]] => rewrite (swap_psci_forward_psci_call_mstage d a b)
| [|- context[?d {trap_reason: ?a} {psci_forward_psci_call: ?b}]] => rewrite (swap_psci_forward_psci_call_trap_reason d a b)
| [|- context[?d {el2_stack: ?a} {target_rec: ?b}]] => rewrite (swap_target_rec_el2_stack d a b)
| [|- context[?d {el3_stack: ?a} {target_rec: ?b}]] => rewrite (swap_target_rec_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {target_rec: ?b}]] => rewrite (swap_target_rec_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {target_rec: ?b}]] => rewrite (swap_target_rec_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {target_rec: ?b}]] => rewrite (swap_target_rec_cur_rec d a b)
| [|- context[?d {mstage: ?a} {target_rec: ?b}]] => rewrite (swap_target_rec_mstage d a b)
| [|- context[?d {trap_reason: ?a} {target_rec: ?b}]] => rewrite (swap_target_rec_trap_reason d a b)
| [|- context[?d {el3_stack: ?a} {el2_stack: ?b}]] => rewrite (swap_el2_stack_el3_stack d a b)
| [|- context[?d {ns_regs_el3: ?a} {el2_stack: ?b}]] => rewrite (swap_el2_stack_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {el2_stack: ?b}]] => rewrite (swap_el2_stack_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {el2_stack: ?b}]] => rewrite (swap_el2_stack_cur_rec d a b)
| [|- context[?d {mstage: ?a} {el2_stack: ?b}]] => rewrite (swap_el2_stack_mstage d a b)
| [|- context[?d {trap_reason: ?a} {el2_stack: ?b}]] => rewrite (swap_el2_stack_trap_reason d a b)
| [|- context[?d {ns_regs_el3: ?a} {el3_stack: ?b}]] => rewrite (swap_el3_stack_ns_regs_el3 d a b)
| [|- context[?d {realm_regs_el3: ?a} {el3_stack: ?b}]] => rewrite (swap_el3_stack_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {el3_stack: ?b}]] => rewrite (swap_el3_stack_cur_rec d a b)
| [|- context[?d {mstage: ?a} {el3_stack: ?b}]] => rewrite (swap_el3_stack_mstage d a b)
| [|- context[?d {trap_reason: ?a} {el3_stack: ?b}]] => rewrite (swap_el3_stack_trap_reason d a b)
| [|- context[?d {realm_regs_el3: ?a} {ns_regs_el3: ?b}]] => rewrite (swap_ns_regs_el3_realm_regs_el3 d a b)
| [|- context[?d {cur_rec: ?a} {ns_regs_el3: ?b}]] => rewrite (swap_ns_regs_el3_cur_rec d a b)
| [|- context[?d {mstage: ?a} {ns_regs_el3: ?b}]] => rewrite (swap_ns_regs_el3_mstage d a b)
| [|- context[?d {trap_reason: ?a} {ns_regs_el3: ?b}]] => rewrite (swap_ns_regs_el3_trap_reason d a b)
| [|- context[?d {cur_rec: ?a} {realm_regs_el3: ?b}]] => rewrite (swap_realm_regs_el3_cur_rec d a b)
| [|- context[?d {mstage: ?a} {realm_regs_el3: ?b}]] => rewrite (swap_realm_regs_el3_mstage d a b)
| [|- context[?d {trap_reason: ?a} {realm_regs_el3: ?b}]] => rewrite (swap_realm_regs_el3_trap_reason d a b)
| [|- context[?d {mstage: ?a} {cur_rec: ?b}]] => rewrite (swap_cur_rec_mstage d a b)
| [|- context[?d {trap_reason: ?a} {cur_rec: ?b}]] => rewrite (swap_cur_rec_trap_reason d a b)
| [|- context[?d {trap_reason: ?a} {mstage: ?b}]] => rewrite (swap_mstage_trap_reason d a b)
| [|- context[?d {gpt: ?a} {gs: ?b}]] => rewrite (swap_gs_gpt d a b)
| [|- context[?d {gpt_lk: ?a} {gs: ?b}]] => rewrite (swap_gs_gpt_lk d a b)
| [|- context[?d {tlbs: ?a} {gs: ?b}]] => rewrite (swap_gs_tlbs d a b)
| [|- context[?d {rtts: ?a} {gs: ?b}]] => rewrite (swap_gs_rtts d a b)
| [|- context[?d {realms: ?a} {gs: ?b}]] => rewrite (swap_gs_realms d a b)
| [|- context[?d {gpt_lk: ?a} {gpt: ?b}]] => rewrite (swap_gpt_gpt_lk d a b)
| [|- context[?d {tlbs: ?a} {gpt: ?b}]] => rewrite (swap_gpt_tlbs d a b)
| [|- context[?d {rtts: ?a} {gpt: ?b}]] => rewrite (swap_gpt_rtts d a b)
| [|- context[?d {realms: ?a} {gpt: ?b}]] => rewrite (swap_gpt_realms d a b)
| [|- context[?d {tlbs: ?a} {gpt_lk: ?b}]] => rewrite (swap_gpt_lk_tlbs d a b)
| [|- context[?d {rtts: ?a} {gpt_lk: ?b}]] => rewrite (swap_gpt_lk_rtts d a b)
| [|- context[?d {realms: ?a} {gpt_lk: ?b}]] => rewrite (swap_gpt_lk_realms d a b)
| [|- context[?d {rtts: ?a} {tlbs: ?b}]] => rewrite (swap_tlbs_rtts d a b)
| [|- context[?d {realms: ?a} {tlbs: ?b}]] => rewrite (swap_tlbs_realms d a b)
| [|- context[?d {realms: ?a} {rtts: ?b}]] => rewrite (swap_rtts_realms d a b)
| [|- context[?d {gref: ?a} {glock: ?b}]] => rewrite (swap_glock_gref d a b)
| [|- context[?d {gtype: ?a} {glock: ?b}]] => rewrite (swap_glock_gtype d a b)
| [|- context[?d {gcnt: ?a} {glock: ?b}]] => rewrite (swap_glock_gcnt d a b)
| [|- context[?d {ginfo: ?a} {glock: ?b}]] => rewrite (swap_glock_ginfo d a b)
| [|- context[?d {gnorm: ?a} {glock: ?b}]] => rewrite (swap_glock_gnorm d a b)
| [|- context[?d {grec: ?a} {glock: ?b}]] => rewrite (swap_glock_grec d a b)
| [|- context[?d {gro: ?a} {glock: ?b}]] => rewrite (swap_glock_gro d a b)
| [|- context[?d {gaux: ?a} {glock: ?b}]] => rewrite (swap_glock_gaux d a b)
| [|- context[?d {gtype: ?a} {gref: ?b}]] => rewrite (swap_gref_gtype d a b)
| [|- context[?d {gcnt: ?a} {gref: ?b}]] => rewrite (swap_gref_gcnt d a b)
| [|- context[?d {ginfo: ?a} {gref: ?b}]] => rewrite (swap_gref_ginfo d a b)
| [|- context[?d {gnorm: ?a} {gref: ?b}]] => rewrite (swap_gref_gnorm d a b)
| [|- context[?d {grec: ?a} {gref: ?b}]] => rewrite (swap_gref_grec d a b)
| [|- context[?d {gro: ?a} {gref: ?b}]] => rewrite (swap_gref_gro d a b)
| [|- context[?d {gaux: ?a} {gref: ?b}]] => rewrite (swap_gref_gaux d a b)
| [|- context[?d {gcnt: ?a} {gtype: ?b}]] => rewrite (swap_gtype_gcnt d a b)
| [|- context[?d {ginfo: ?a} {gtype: ?b}]] => rewrite (swap_gtype_ginfo d a b)
| [|- context[?d {gnorm: ?a} {gtype: ?b}]] => rewrite (swap_gtype_gnorm d a b)
| [|- context[?d {grec: ?a} {gtype: ?b}]] => rewrite (swap_gtype_grec d a b)
| [|- context[?d {gro: ?a} {gtype: ?b}]] => rewrite (swap_gtype_gro d a b)
| [|- context[?d {gaux: ?a} {gtype: ?b}]] => rewrite (swap_gtype_gaux d a b)
| [|- context[?d {ginfo: ?a} {gcnt: ?b}]] => rewrite (swap_gcnt_ginfo d a b)
| [|- context[?d {gnorm: ?a} {gcnt: ?b}]] => rewrite (swap_gcnt_gnorm d a b)
| [|- context[?d {grec: ?a} {gcnt: ?b}]] => rewrite (swap_gcnt_grec d a b)
| [|- context[?d {gro: ?a} {gcnt: ?b}]] => rewrite (swap_gcnt_gro d a b)
| [|- context[?d {gaux: ?a} {gcnt: ?b}]] => rewrite (swap_gcnt_gaux d a b)
| [|- context[?d {gnorm: ?a} {ginfo: ?b}]] => rewrite (swap_ginfo_gnorm d a b)
| [|- context[?d {grec: ?a} {ginfo: ?b}]] => rewrite (swap_ginfo_grec d a b)
| [|- context[?d {gro: ?a} {ginfo: ?b}]] => rewrite (swap_ginfo_gro d a b)
| [|- context[?d {gaux: ?a} {ginfo: ?b}]] => rewrite (swap_ginfo_gaux d a b)
| [|- context[?d {grec: ?a} {gnorm: ?b}]] => rewrite (swap_gnorm_grec d a b)
| [|- context[?d {gro: ?a} {gnorm: ?b}]] => rewrite (swap_gnorm_gro d a b)
| [|- context[?d {gaux: ?a} {gnorm: ?b}]] => rewrite (swap_gnorm_gaux d a b)
| [|- context[?d {gro: ?a} {grec: ?b}]] => rewrite (swap_grec_gro d a b)
| [|- context[?d {gaux: ?a} {grec: ?b}]] => rewrite (swap_grec_gaux d a b)
| [|- context[?d {gaux: ?a} {gro: ?b}]] => rewrite (swap_gro_gaux d a b)
| [|- context[?d {r_x1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x1 d a b)
| [|- context[?d {r_x2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x2 d a b)
| [|- context[?d {r_x3: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x3 d a b)
| [|- context[?d {r_x4: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x4 d a b)
| [|- context[?d {r_x5: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x5 d a b)
| [|- context[?d {r_x6: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x6 d a b)
| [|- context[?d {r_x7: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x7 d a b)
| [|- context[?d {r_x8: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x8 d a b)
| [|- context[?d {r_x9: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x9 d a b)
| [|- context[?d {r_x10: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x10 d a b)
| [|- context[?d {r_x11: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x11 d a b)
| [|- context[?d {r_x12: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x12 d a b)
| [|- context[?d {r_x13: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x13 d a b)
| [|- context[?d {r_x14: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x14 d a b)
| [|- context[?d {r_x15: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x15 d a b)
| [|- context[?d {r_x16: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x16 d a b)
| [|- context[?d {r_x17: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x17 d a b)
| [|- context[?d {r_x18: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x18 d a b)
| [|- context[?d {r_x19: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x19 d a b)
| [|- context[?d {r_x20: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x20 d a b)
| [|- context[?d {r_x21: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x21 d a b)
| [|- context[?d {r_x22: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x22 d a b)
| [|- context[?d {r_x23: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x23 d a b)
| [|- context[?d {r_x24: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x24 d a b)
| [|- context[?d {r_x25: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x25 d a b)
| [|- context[?d {r_x26: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x26 d a b)
| [|- context[?d {r_x27: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x27 d a b)
| [|- context[?d {r_x28: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x28 d a b)
| [|- context[?d {r_x29: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x29 d a b)
| [|- context[?d {r_x30: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_x30 d a b)
| [|- context[?d {r_lr: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_lr d a b)
| [|- context[?d {r_cntp_ctl_el0: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_cntp_ctl_el0 d a b)
| [|- context[?d {r_cntp_cval_el0: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_cntp_cval_el0 d a b)
| [|- context[?d {r_cntp_tval_el0: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_cntp_tval_el0 d a b)
| [|- context[?d {r_cntv_ctl_el0: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_cntv_ctl_el0 d a b)
| [|- context[?d {r_cntv_cval_el0: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_cntv_cval_el0 d a b)
| [|- context[?d {r_cntv_tval_el0: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_cntv_tval_el0 d a b)
| [|- context[?d {r_sp_el0: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_sp_el0 d a b)
| [|- context[?d {r_pmcr_el0: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_pmcr_el0 d a b)
| [|- context[?d {r_pmuserenr_el0: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_pmuserenr_el0 d a b)
| [|- context[?d {r_tpidrro_el0: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_tpidrro_el0 d a b)
| [|- context[?d {r_tpidr_el0: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_tpidr_el0 d a b)
| [|- context[?d {r_sp_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_sp_el1 d a b)
| [|- context[?d {r_elr_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_elr_el1 d a b)
| [|- context[?d {r_spsr_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_spsr_el1 d a b)
| [|- context[?d {r_csselr_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_csselr_el1 d a b)
| [|- context[?d {r_sctlr_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_sctlr_el1 d a b)
| [|- context[?d {r_actlr_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_actlr_el1 d a b)
| [|- context[?d {r_cpacr_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_cpacr_el1 d a b)
| [|- context[?d {r_zcr_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_zcr_el1 d a b)
| [|- context[?d {r_ttbr0_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_ttbr0_el1 d a b)
| [|- context[?d {r_ttbr1_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_ttbr1_el1 d a b)
| [|- context[?d {r_tcr_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_tcr_el1 d a b)
| [|- context[?d {r_esr_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_esr_el1 d a b)
| [|- context[?d {r_afsr0_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_afsr0_el1 d a b)
| [|- context[?d {r_afsr1_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_afsr1_el1 d a b)
| [|- context[?d {r_far_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_far_el1 d a b)
| [|- context[?d {r_mair_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_mair_el1 d a b)
| [|- context[?d {r_vbar_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_vbar_el1 d a b)
| [|- context[?d {r_contextidr_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_contextidr_el1 d a b)
| [|- context[?d {r_tpidr_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_tpidr_el1 d a b)
| [|- context[?d {r_amair_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_amair_el1 d a b)
| [|- context[?d {r_cntkctl_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_cntkctl_el1 d a b)
| [|- context[?d {r_par_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_par_el1 d a b)
| [|- context[?d {r_mdscr_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_mdscr_el1 d a b)
| [|- context[?d {r_mdccint_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_mdccint_el1 d a b)
| [|- context[?d {r_disr_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_disr_el1 d a b)
| [|- context[?d {r_mpam0_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_mpam0_el1 d a b)
| [|- context[?d {r_cnthctl_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_cnthctl_el2 d a b)
| [|- context[?d {r_cntvoff_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_cntvoff_el2 d a b)
| [|- context[?d {r_cntpoff_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_cntpoff_el2 d a b)
| [|- context[?d {r_vmpidr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_vmpidr_el2 d a b)
| [|- context[?d {r_vttbr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_vttbr_el2 d a b)
| [|- context[?d {r_vtcr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_vtcr_el2 d a b)
| [|- context[?d {r_hcr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_hcr_el2 d a b)
| [|- context[?d {r_actlr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_actlr_el2 d a b)
| [|- context[?d {r_afsr0_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_afsr0_el2 d a b)
| [|- context[?d {r_afsr1_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_afsr1_el2 d a b)
| [|- context[?d {r_amair_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_amair_el2 d a b)
| [|- context[?d {r_cptr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_cptr_el2 d a b)
| [|- context[?d {r_elr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_elr_el2 d a b)
| [|- context[?d {r_esr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_esr_el2 d a b)
| [|- context[?d {r_far_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_far_el2 d a b)
| [|- context[?d {r_hacr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_hacr_el2 d a b)
| [|- context[?d {r_hpfar_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_hpfar_el2 d a b)
| [|- context[?d {r_hstr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_hstr_el2 d a b)
| [|- context[?d {r_mair_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_mair_el2 d a b)
| [|- context[?d {r_mpam_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_mpam_el2 d a b)
| [|- context[?d {r_mpamhcr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_mpamhcr_el2 d a b)
| [|- context[?d {r_pmscr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_pmscr_el2 d a b)
| [|- context[?d {r_sctlr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_sctlr_el2 d a b)
| [|- context[?d {r_scxtnum_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_scxtnum_el2 d a b)
| [|- context[?d {r_sp_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_sp_el2 d a b)
| [|- context[?d {r_spsr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_spsr_el2 d a b)
| [|- context[?d {r_tcr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_tcr_el2 d a b)
| [|- context[?d {r_tfsr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_tfsr_el2 d a b)
| [|- context[?d {r_tpidr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_tpidr_el2 d a b)
| [|- context[?d {r_trfcr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_trfcr_el2 d a b)
| [|- context[?d {r_ttbr0_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_ttbr0_el2 d a b)
| [|- context[?d {r_ttbr1_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_ttbr1_el2 d a b)
| [|- context[?d {r_vbar_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_vbar_el2 d a b)
| [|- context[?d {r_vdisr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_vdisr_el2 d a b)
| [|- context[?d {r_vncr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_vncr_el2 d a b)
| [|- context[?d {r_vpidr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_vpidr_el2 d a b)
| [|- context[?d {r_vsesr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_vsesr_el2 d a b)
| [|- context[?d {r_vstcr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_vstcr_el2 d a b)
| [|- context[?d {r_vsttbr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_vsttbr_el2 d a b)
| [|- context[?d {r_zcr_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_zcr_el2 d a b)
| [|- context[?d {r_icc_sre_el2: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_icc_sre_el2 d a b)
| [|- context[?d {r_icc_hppir1_el1: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_icc_hppir1_el1 d a b)
| [|- context[?d {r_spsr_el3: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_spsr_el3 d a b)
| [|- context[?d {r_elr_el3: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_elr_el3 d a b)
| [|- context[?d {r_esr_el3: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_esr_el3 d a b)
| [|- context[?d {r_scr_el3: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_scr_el3 d a b)
| [|- context[?d {r_tpidr_el3: ?a} {r_x0: ?b}]] => rewrite (swap_r_x0_r_tpidr_el3 d a b)
| [|- context[?d {r_x2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x2 d a b)
| [|- context[?d {r_x3: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x3 d a b)
| [|- context[?d {r_x4: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x4 d a b)
| [|- context[?d {r_x5: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x5 d a b)
| [|- context[?d {r_x6: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x6 d a b)
| [|- context[?d {r_x7: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x7 d a b)
| [|- context[?d {r_x8: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x8 d a b)
| [|- context[?d {r_x9: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x9 d a b)
| [|- context[?d {r_x10: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x10 d a b)
| [|- context[?d {r_x11: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x11 d a b)
| [|- context[?d {r_x12: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x12 d a b)
| [|- context[?d {r_x13: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x13 d a b)
| [|- context[?d {r_x14: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x14 d a b)
| [|- context[?d {r_x15: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x15 d a b)
| [|- context[?d {r_x16: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x16 d a b)
| [|- context[?d {r_x17: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x17 d a b)
| [|- context[?d {r_x18: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x18 d a b)
| [|- context[?d {r_x19: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x19 d a b)
| [|- context[?d {r_x20: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x20 d a b)
| [|- context[?d {r_x21: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x21 d a b)
| [|- context[?d {r_x22: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x22 d a b)
| [|- context[?d {r_x23: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x23 d a b)
| [|- context[?d {r_x24: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x24 d a b)
| [|- context[?d {r_x25: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x25 d a b)
| [|- context[?d {r_x26: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x26 d a b)
| [|- context[?d {r_x27: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x27 d a b)
| [|- context[?d {r_x28: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x28 d a b)
| [|- context[?d {r_x29: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x29 d a b)
| [|- context[?d {r_x30: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_x30 d a b)
| [|- context[?d {r_lr: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_lr d a b)
| [|- context[?d {r_cntp_ctl_el0: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_cntp_ctl_el0 d a b)
| [|- context[?d {r_cntp_cval_el0: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_cntp_cval_el0 d a b)
| [|- context[?d {r_cntp_tval_el0: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_cntp_tval_el0 d a b)
| [|- context[?d {r_cntv_ctl_el0: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_cntv_ctl_el0 d a b)
| [|- context[?d {r_cntv_cval_el0: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_cntv_cval_el0 d a b)
| [|- context[?d {r_cntv_tval_el0: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_cntv_tval_el0 d a b)
| [|- context[?d {r_sp_el0: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_sp_el0 d a b)
| [|- context[?d {r_pmcr_el0: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_pmcr_el0 d a b)
| [|- context[?d {r_pmuserenr_el0: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_pmuserenr_el0 d a b)
| [|- context[?d {r_tpidrro_el0: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_tpidrro_el0 d a b)
| [|- context[?d {r_tpidr_el0: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_tpidr_el0 d a b)
| [|- context[?d {r_sp_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_sp_el1 d a b)
| [|- context[?d {r_elr_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_elr_el1 d a b)
| [|- context[?d {r_spsr_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_spsr_el1 d a b)
| [|- context[?d {r_csselr_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_csselr_el1 d a b)
| [|- context[?d {r_sctlr_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_sctlr_el1 d a b)
| [|- context[?d {r_actlr_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_actlr_el1 d a b)
| [|- context[?d {r_cpacr_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_cpacr_el1 d a b)
| [|- context[?d {r_zcr_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_zcr_el1 d a b)
| [|- context[?d {r_ttbr0_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_ttbr0_el1 d a b)
| [|- context[?d {r_ttbr1_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_ttbr1_el1 d a b)
| [|- context[?d {r_tcr_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_tcr_el1 d a b)
| [|- context[?d {r_esr_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_esr_el1 d a b)
| [|- context[?d {r_afsr0_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_afsr0_el1 d a b)
| [|- context[?d {r_afsr1_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_afsr1_el1 d a b)
| [|- context[?d {r_far_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_far_el1 d a b)
| [|- context[?d {r_mair_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_mair_el1 d a b)
| [|- context[?d {r_vbar_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_vbar_el1 d a b)
| [|- context[?d {r_contextidr_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_contextidr_el1 d a b)
| [|- context[?d {r_tpidr_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_tpidr_el1 d a b)
| [|- context[?d {r_amair_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_amair_el1 d a b)
| [|- context[?d {r_cntkctl_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_cntkctl_el1 d a b)
| [|- context[?d {r_par_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_par_el1 d a b)
| [|- context[?d {r_mdscr_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_mdscr_el1 d a b)
| [|- context[?d {r_mdccint_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_mdccint_el1 d a b)
| [|- context[?d {r_disr_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_disr_el1 d a b)
| [|- context[?d {r_mpam0_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_mpam0_el1 d a b)
| [|- context[?d {r_cnthctl_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_cnthctl_el2 d a b)
| [|- context[?d {r_cntvoff_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_cntvoff_el2 d a b)
| [|- context[?d {r_cntpoff_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_cntpoff_el2 d a b)
| [|- context[?d {r_vmpidr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_vmpidr_el2 d a b)
| [|- context[?d {r_vttbr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_vttbr_el2 d a b)
| [|- context[?d {r_vtcr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_vtcr_el2 d a b)
| [|- context[?d {r_hcr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_hcr_el2 d a b)
| [|- context[?d {r_actlr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_actlr_el2 d a b)
| [|- context[?d {r_afsr0_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_afsr0_el2 d a b)
| [|- context[?d {r_afsr1_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_afsr1_el2 d a b)
| [|- context[?d {r_amair_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_amair_el2 d a b)
| [|- context[?d {r_cptr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_cptr_el2 d a b)
| [|- context[?d {r_elr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_elr_el2 d a b)
| [|- context[?d {r_esr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_esr_el2 d a b)
| [|- context[?d {r_far_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_far_el2 d a b)
| [|- context[?d {r_hacr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_hacr_el2 d a b)
| [|- context[?d {r_hpfar_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_hpfar_el2 d a b)
| [|- context[?d {r_hstr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_hstr_el2 d a b)
| [|- context[?d {r_mair_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_mair_el2 d a b)
| [|- context[?d {r_mpam_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_mpam_el2 d a b)
| [|- context[?d {r_mpamhcr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_mpamhcr_el2 d a b)
| [|- context[?d {r_pmscr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_pmscr_el2 d a b)
| [|- context[?d {r_sctlr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_sctlr_el2 d a b)
| [|- context[?d {r_scxtnum_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_scxtnum_el2 d a b)
| [|- context[?d {r_sp_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_sp_el2 d a b)
| [|- context[?d {r_spsr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_spsr_el2 d a b)
| [|- context[?d {r_tcr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_tcr_el2 d a b)
| [|- context[?d {r_tfsr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_tfsr_el2 d a b)
| [|- context[?d {r_tpidr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_tpidr_el2 d a b)
| [|- context[?d {r_trfcr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_trfcr_el2 d a b)
| [|- context[?d {r_ttbr0_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_ttbr0_el2 d a b)
| [|- context[?d {r_ttbr1_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_ttbr1_el2 d a b)
| [|- context[?d {r_vbar_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_vbar_el2 d a b)
| [|- context[?d {r_vdisr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_vdisr_el2 d a b)
| [|- context[?d {r_vncr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_vncr_el2 d a b)
| [|- context[?d {r_vpidr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_vpidr_el2 d a b)
| [|- context[?d {r_vsesr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_vsesr_el2 d a b)
| [|- context[?d {r_vstcr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_vstcr_el2 d a b)
| [|- context[?d {r_vsttbr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_vsttbr_el2 d a b)
| [|- context[?d {r_zcr_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_zcr_el2 d a b)
| [|- context[?d {r_icc_sre_el2: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_icc_sre_el2 d a b)
| [|- context[?d {r_icc_hppir1_el1: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_icc_hppir1_el1 d a b)
| [|- context[?d {r_spsr_el3: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_spsr_el3 d a b)
| [|- context[?d {r_elr_el3: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_elr_el3 d a b)
| [|- context[?d {r_esr_el3: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_esr_el3 d a b)
| [|- context[?d {r_scr_el3: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_scr_el3 d a b)
| [|- context[?d {r_tpidr_el3: ?a} {r_x1: ?b}]] => rewrite (swap_r_x1_r_tpidr_el3 d a b)
| [|- context[?d {r_x3: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x3 d a b)
| [|- context[?d {r_x4: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x4 d a b)
| [|- context[?d {r_x5: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x5 d a b)
| [|- context[?d {r_x6: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x6 d a b)
| [|- context[?d {r_x7: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x7 d a b)
| [|- context[?d {r_x8: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x8 d a b)
| [|- context[?d {r_x9: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x9 d a b)
| [|- context[?d {r_x10: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x10 d a b)
| [|- context[?d {r_x11: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x11 d a b)
| [|- context[?d {r_x12: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x12 d a b)
| [|- context[?d {r_x13: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x13 d a b)
| [|- context[?d {r_x14: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x14 d a b)
| [|- context[?d {r_x15: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x15 d a b)
| [|- context[?d {r_x16: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x16 d a b)
| [|- context[?d {r_x17: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x17 d a b)
| [|- context[?d {r_x18: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x18 d a b)
| [|- context[?d {r_x19: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x19 d a b)
| [|- context[?d {r_x20: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x20 d a b)
| [|- context[?d {r_x21: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x21 d a b)
| [|- context[?d {r_x22: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x22 d a b)
| [|- context[?d {r_x23: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x23 d a b)
| [|- context[?d {r_x24: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x24 d a b)
| [|- context[?d {r_x25: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x25 d a b)
| [|- context[?d {r_x26: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x26 d a b)
| [|- context[?d {r_x27: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x27 d a b)
| [|- context[?d {r_x28: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x28 d a b)
| [|- context[?d {r_x29: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x29 d a b)
| [|- context[?d {r_x30: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_x30 d a b)
| [|- context[?d {r_lr: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_lr d a b)
| [|- context[?d {r_cntp_ctl_el0: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_cntp_ctl_el0 d a b)
| [|- context[?d {r_cntp_cval_el0: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_cntp_cval_el0 d a b)
| [|- context[?d {r_cntp_tval_el0: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_cntp_tval_el0 d a b)
| [|- context[?d {r_cntv_ctl_el0: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_cntv_ctl_el0 d a b)
| [|- context[?d {r_cntv_cval_el0: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_cntv_cval_el0 d a b)
| [|- context[?d {r_cntv_tval_el0: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_cntv_tval_el0 d a b)
| [|- context[?d {r_sp_el0: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_sp_el0 d a b)
| [|- context[?d {r_pmcr_el0: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_pmcr_el0 d a b)
| [|- context[?d {r_pmuserenr_el0: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_pmuserenr_el0 d a b)
| [|- context[?d {r_tpidrro_el0: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_tpidrro_el0 d a b)
| [|- context[?d {r_tpidr_el0: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_tpidr_el0 d a b)
| [|- context[?d {r_sp_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_sp_el1 d a b)
| [|- context[?d {r_elr_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_elr_el1 d a b)
| [|- context[?d {r_spsr_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_spsr_el1 d a b)
| [|- context[?d {r_csselr_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_csselr_el1 d a b)
| [|- context[?d {r_sctlr_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_sctlr_el1 d a b)
| [|- context[?d {r_actlr_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_actlr_el1 d a b)
| [|- context[?d {r_cpacr_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_cpacr_el1 d a b)
| [|- context[?d {r_zcr_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_zcr_el1 d a b)
| [|- context[?d {r_ttbr0_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_ttbr0_el1 d a b)
| [|- context[?d {r_ttbr1_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_ttbr1_el1 d a b)
| [|- context[?d {r_tcr_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_tcr_el1 d a b)
| [|- context[?d {r_esr_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_esr_el1 d a b)
| [|- context[?d {r_afsr0_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_afsr0_el1 d a b)
| [|- context[?d {r_afsr1_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_afsr1_el1 d a b)
| [|- context[?d {r_far_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_far_el1 d a b)
| [|- context[?d {r_mair_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_mair_el1 d a b)
| [|- context[?d {r_vbar_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_vbar_el1 d a b)
| [|- context[?d {r_contextidr_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_contextidr_el1 d a b)
| [|- context[?d {r_tpidr_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_tpidr_el1 d a b)
| [|- context[?d {r_amair_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_amair_el1 d a b)
| [|- context[?d {r_cntkctl_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_cntkctl_el1 d a b)
| [|- context[?d {r_par_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_par_el1 d a b)
| [|- context[?d {r_mdscr_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_mdscr_el1 d a b)
| [|- context[?d {r_mdccint_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_mdccint_el1 d a b)
| [|- context[?d {r_disr_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_disr_el1 d a b)
| [|- context[?d {r_mpam0_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_mpam0_el1 d a b)
| [|- context[?d {r_cnthctl_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_cnthctl_el2 d a b)
| [|- context[?d {r_cntvoff_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_cntvoff_el2 d a b)
| [|- context[?d {r_cntpoff_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_cntpoff_el2 d a b)
| [|- context[?d {r_vmpidr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_vmpidr_el2 d a b)
| [|- context[?d {r_vttbr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_vttbr_el2 d a b)
| [|- context[?d {r_vtcr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_vtcr_el2 d a b)
| [|- context[?d {r_hcr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_hcr_el2 d a b)
| [|- context[?d {r_actlr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_actlr_el2 d a b)
| [|- context[?d {r_afsr0_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_afsr0_el2 d a b)
| [|- context[?d {r_afsr1_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_afsr1_el2 d a b)
| [|- context[?d {r_amair_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_amair_el2 d a b)
| [|- context[?d {r_cptr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_cptr_el2 d a b)
| [|- context[?d {r_elr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_elr_el2 d a b)
| [|- context[?d {r_esr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_esr_el2 d a b)
| [|- context[?d {r_far_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_far_el2 d a b)
| [|- context[?d {r_hacr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_hacr_el2 d a b)
| [|- context[?d {r_hpfar_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_hpfar_el2 d a b)
| [|- context[?d {r_hstr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_hstr_el2 d a b)
| [|- context[?d {r_mair_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_mair_el2 d a b)
| [|- context[?d {r_mpam_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_mpam_el2 d a b)
| [|- context[?d {r_mpamhcr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_mpamhcr_el2 d a b)
| [|- context[?d {r_pmscr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_pmscr_el2 d a b)
| [|- context[?d {r_sctlr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_sctlr_el2 d a b)
| [|- context[?d {r_scxtnum_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_scxtnum_el2 d a b)
| [|- context[?d {r_sp_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_sp_el2 d a b)
| [|- context[?d {r_spsr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_spsr_el2 d a b)
| [|- context[?d {r_tcr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_tcr_el2 d a b)
| [|- context[?d {r_tfsr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_tfsr_el2 d a b)
| [|- context[?d {r_tpidr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_tpidr_el2 d a b)
| [|- context[?d {r_trfcr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_trfcr_el2 d a b)
| [|- context[?d {r_ttbr0_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_ttbr0_el2 d a b)
| [|- context[?d {r_ttbr1_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_ttbr1_el2 d a b)
| [|- context[?d {r_vbar_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_vbar_el2 d a b)
| [|- context[?d {r_vdisr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_vdisr_el2 d a b)
| [|- context[?d {r_vncr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_vncr_el2 d a b)
| [|- context[?d {r_vpidr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_vpidr_el2 d a b)
| [|- context[?d {r_vsesr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_vsesr_el2 d a b)
| [|- context[?d {r_vstcr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_vstcr_el2 d a b)
| [|- context[?d {r_vsttbr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_vsttbr_el2 d a b)
| [|- context[?d {r_zcr_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_zcr_el2 d a b)
| [|- context[?d {r_icc_sre_el2: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_icc_sre_el2 d a b)
| [|- context[?d {r_icc_hppir1_el1: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_icc_hppir1_el1 d a b)
| [|- context[?d {r_spsr_el3: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_spsr_el3 d a b)
| [|- context[?d {r_elr_el3: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_elr_el3 d a b)
| [|- context[?d {r_esr_el3: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_esr_el3 d a b)
| [|- context[?d {r_scr_el3: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_scr_el3 d a b)
| [|- context[?d {r_tpidr_el3: ?a} {r_x2: ?b}]] => rewrite (swap_r_x2_r_tpidr_el3 d a b)
| [|- context[?d {r_x4: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x4 d a b)
| [|- context[?d {r_x5: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x5 d a b)
| [|- context[?d {r_x6: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x6 d a b)
| [|- context[?d {r_x7: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x7 d a b)
| [|- context[?d {r_x8: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x8 d a b)
| [|- context[?d {r_x9: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x9 d a b)
| [|- context[?d {r_x10: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x10 d a b)
| [|- context[?d {r_x11: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x11 d a b)
| [|- context[?d {r_x12: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x12 d a b)
| [|- context[?d {r_x13: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x13 d a b)
| [|- context[?d {r_x14: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x14 d a b)
| [|- context[?d {r_x15: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x15 d a b)
| [|- context[?d {r_x16: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x16 d a b)
| [|- context[?d {r_x17: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x17 d a b)
| [|- context[?d {r_x18: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x18 d a b)
| [|- context[?d {r_x19: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x19 d a b)
| [|- context[?d {r_x20: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x20 d a b)
| [|- context[?d {r_x21: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x21 d a b)
| [|- context[?d {r_x22: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x22 d a b)
| [|- context[?d {r_x23: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x23 d a b)
| [|- context[?d {r_x24: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x24 d a b)
| [|- context[?d {r_x25: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x25 d a b)
| [|- context[?d {r_x26: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x26 d a b)
| [|- context[?d {r_x27: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x27 d a b)
| [|- context[?d {r_x28: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x28 d a b)
| [|- context[?d {r_x29: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x29 d a b)
| [|- context[?d {r_x30: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_x30 d a b)
| [|- context[?d {r_lr: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_lr d a b)
| [|- context[?d {r_cntp_ctl_el0: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_cntp_ctl_el0 d a b)
| [|- context[?d {r_cntp_cval_el0: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_cntp_cval_el0 d a b)
| [|- context[?d {r_cntp_tval_el0: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_cntp_tval_el0 d a b)
| [|- context[?d {r_cntv_ctl_el0: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_cntv_ctl_el0 d a b)
| [|- context[?d {r_cntv_cval_el0: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_cntv_cval_el0 d a b)
| [|- context[?d {r_cntv_tval_el0: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_cntv_tval_el0 d a b)
| [|- context[?d {r_sp_el0: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_sp_el0 d a b)
| [|- context[?d {r_pmcr_el0: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_pmcr_el0 d a b)
| [|- context[?d {r_pmuserenr_el0: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_pmuserenr_el0 d a b)
| [|- context[?d {r_tpidrro_el0: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_tpidrro_el0 d a b)
| [|- context[?d {r_tpidr_el0: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_tpidr_el0 d a b)
| [|- context[?d {r_sp_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_sp_el1 d a b)
| [|- context[?d {r_elr_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_elr_el1 d a b)
| [|- context[?d {r_spsr_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_spsr_el1 d a b)
| [|- context[?d {r_csselr_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_csselr_el1 d a b)
| [|- context[?d {r_sctlr_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_sctlr_el1 d a b)
| [|- context[?d {r_actlr_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_actlr_el1 d a b)
| [|- context[?d {r_cpacr_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_cpacr_el1 d a b)
| [|- context[?d {r_zcr_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_zcr_el1 d a b)
| [|- context[?d {r_ttbr0_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_ttbr0_el1 d a b)
| [|- context[?d {r_ttbr1_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_ttbr1_el1 d a b)
| [|- context[?d {r_tcr_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_tcr_el1 d a b)
| [|- context[?d {r_esr_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_esr_el1 d a b)
| [|- context[?d {r_afsr0_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_afsr0_el1 d a b)
| [|- context[?d {r_afsr1_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_afsr1_el1 d a b)
| [|- context[?d {r_far_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_far_el1 d a b)
| [|- context[?d {r_mair_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_mair_el1 d a b)
| [|- context[?d {r_vbar_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_vbar_el1 d a b)
| [|- context[?d {r_contextidr_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_contextidr_el1 d a b)
| [|- context[?d {r_tpidr_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_tpidr_el1 d a b)
| [|- context[?d {r_amair_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_amair_el1 d a b)
| [|- context[?d {r_cntkctl_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_cntkctl_el1 d a b)
| [|- context[?d {r_par_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_par_el1 d a b)
| [|- context[?d {r_mdscr_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_mdscr_el1 d a b)
| [|- context[?d {r_mdccint_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_mdccint_el1 d a b)
| [|- context[?d {r_disr_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_disr_el1 d a b)
| [|- context[?d {r_mpam0_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_mpam0_el1 d a b)
| [|- context[?d {r_cnthctl_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_cnthctl_el2 d a b)
| [|- context[?d {r_cntvoff_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_cntvoff_el2 d a b)
| [|- context[?d {r_cntpoff_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_cntpoff_el2 d a b)
| [|- context[?d {r_vmpidr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_vmpidr_el2 d a b)
| [|- context[?d {r_vttbr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_vttbr_el2 d a b)
| [|- context[?d {r_vtcr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_vtcr_el2 d a b)
| [|- context[?d {r_hcr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_hcr_el2 d a b)
| [|- context[?d {r_actlr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_actlr_el2 d a b)
| [|- context[?d {r_afsr0_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_afsr0_el2 d a b)
| [|- context[?d {r_afsr1_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_afsr1_el2 d a b)
| [|- context[?d {r_amair_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_amair_el2 d a b)
| [|- context[?d {r_cptr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_cptr_el2 d a b)
| [|- context[?d {r_elr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_elr_el2 d a b)
| [|- context[?d {r_esr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_esr_el2 d a b)
| [|- context[?d {r_far_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_far_el2 d a b)
| [|- context[?d {r_hacr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_hacr_el2 d a b)
| [|- context[?d {r_hpfar_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_hpfar_el2 d a b)
| [|- context[?d {r_hstr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_hstr_el2 d a b)
| [|- context[?d {r_mair_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_mair_el2 d a b)
| [|- context[?d {r_mpam_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_mpam_el2 d a b)
| [|- context[?d {r_mpamhcr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_mpamhcr_el2 d a b)
| [|- context[?d {r_pmscr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_pmscr_el2 d a b)
| [|- context[?d {r_sctlr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_sctlr_el2 d a b)
| [|- context[?d {r_scxtnum_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_scxtnum_el2 d a b)
| [|- context[?d {r_sp_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_sp_el2 d a b)
| [|- context[?d {r_spsr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_spsr_el2 d a b)
| [|- context[?d {r_tcr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_tcr_el2 d a b)
| [|- context[?d {r_tfsr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_tfsr_el2 d a b)
| [|- context[?d {r_tpidr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_tpidr_el2 d a b)
| [|- context[?d {r_trfcr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_trfcr_el2 d a b)
| [|- context[?d {r_ttbr0_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_ttbr0_el2 d a b)
| [|- context[?d {r_ttbr1_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_ttbr1_el2 d a b)
| [|- context[?d {r_vbar_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_vbar_el2 d a b)
| [|- context[?d {r_vdisr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_vdisr_el2 d a b)
| [|- context[?d {r_vncr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_vncr_el2 d a b)
| [|- context[?d {r_vpidr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_vpidr_el2 d a b)
| [|- context[?d {r_vsesr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_vsesr_el2 d a b)
| [|- context[?d {r_vstcr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_vstcr_el2 d a b)
| [|- context[?d {r_vsttbr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_vsttbr_el2 d a b)
| [|- context[?d {r_zcr_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_zcr_el2 d a b)
| [|- context[?d {r_icc_sre_el2: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_icc_sre_el2 d a b)
| [|- context[?d {r_icc_hppir1_el1: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_icc_hppir1_el1 d a b)
| [|- context[?d {r_spsr_el3: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_spsr_el3 d a b)
| [|- context[?d {r_elr_el3: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_elr_el3 d a b)
| [|- context[?d {r_esr_el3: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_esr_el3 d a b)
| [|- context[?d {r_scr_el3: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_scr_el3 d a b)
| [|- context[?d {r_tpidr_el3: ?a} {r_x3: ?b}]] => rewrite (swap_r_x3_r_tpidr_el3 d a b)
| [|- context[?d {r_x5: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x5 d a b)
| [|- context[?d {r_x6: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x6 d a b)
| [|- context[?d {r_x7: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x7 d a b)
| [|- context[?d {r_x8: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x8 d a b)
| [|- context[?d {r_x9: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x9 d a b)
| [|- context[?d {r_x10: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x10 d a b)
| [|- context[?d {r_x11: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x11 d a b)
| [|- context[?d {r_x12: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x12 d a b)
| [|- context[?d {r_x13: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x13 d a b)
| [|- context[?d {r_x14: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x14 d a b)
| [|- context[?d {r_x15: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x15 d a b)
| [|- context[?d {r_x16: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x16 d a b)
| [|- context[?d {r_x17: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x17 d a b)
| [|- context[?d {r_x18: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x18 d a b)
| [|- context[?d {r_x19: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x19 d a b)
| [|- context[?d {r_x20: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x20 d a b)
| [|- context[?d {r_x21: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x21 d a b)
| [|- context[?d {r_x22: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x22 d a b)
| [|- context[?d {r_x23: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x23 d a b)
| [|- context[?d {r_x24: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x24 d a b)
| [|- context[?d {r_x25: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x25 d a b)
| [|- context[?d {r_x26: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x26 d a b)
| [|- context[?d {r_x27: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x27 d a b)
| [|- context[?d {r_x28: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x28 d a b)
| [|- context[?d {r_x29: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x29 d a b)
| [|- context[?d {r_x30: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_x30 d a b)
| [|- context[?d {r_lr: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_lr d a b)
| [|- context[?d {r_cntp_ctl_el0: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_cntp_ctl_el0 d a b)
| [|- context[?d {r_cntp_cval_el0: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_cntp_cval_el0 d a b)
| [|- context[?d {r_cntp_tval_el0: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_cntp_tval_el0 d a b)
| [|- context[?d {r_cntv_ctl_el0: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_cntv_ctl_el0 d a b)
| [|- context[?d {r_cntv_cval_el0: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_cntv_cval_el0 d a b)
| [|- context[?d {r_cntv_tval_el0: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_cntv_tval_el0 d a b)
| [|- context[?d {r_sp_el0: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_sp_el0 d a b)
| [|- context[?d {r_pmcr_el0: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_pmcr_el0 d a b)
| [|- context[?d {r_pmuserenr_el0: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_pmuserenr_el0 d a b)
| [|- context[?d {r_tpidrro_el0: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_tpidrro_el0 d a b)
| [|- context[?d {r_tpidr_el0: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_tpidr_el0 d a b)
| [|- context[?d {r_sp_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_sp_el1 d a b)
| [|- context[?d {r_elr_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_elr_el1 d a b)
| [|- context[?d {r_spsr_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_spsr_el1 d a b)
| [|- context[?d {r_csselr_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_csselr_el1 d a b)
| [|- context[?d {r_sctlr_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_sctlr_el1 d a b)
| [|- context[?d {r_actlr_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_actlr_el1 d a b)
| [|- context[?d {r_cpacr_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_cpacr_el1 d a b)
| [|- context[?d {r_zcr_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_zcr_el1 d a b)
| [|- context[?d {r_ttbr0_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_ttbr0_el1 d a b)
| [|- context[?d {r_ttbr1_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_ttbr1_el1 d a b)
| [|- context[?d {r_tcr_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_tcr_el1 d a b)
| [|- context[?d {r_esr_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_esr_el1 d a b)
| [|- context[?d {r_afsr0_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_afsr0_el1 d a b)
| [|- context[?d {r_afsr1_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_afsr1_el1 d a b)
| [|- context[?d {r_far_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_far_el1 d a b)
| [|- context[?d {r_mair_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_mair_el1 d a b)
| [|- context[?d {r_vbar_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_vbar_el1 d a b)
| [|- context[?d {r_contextidr_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_contextidr_el1 d a b)
| [|- context[?d {r_tpidr_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_tpidr_el1 d a b)
| [|- context[?d {r_amair_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_amair_el1 d a b)
| [|- context[?d {r_cntkctl_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_cntkctl_el1 d a b)
| [|- context[?d {r_par_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_par_el1 d a b)
| [|- context[?d {r_mdscr_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_mdscr_el1 d a b)
| [|- context[?d {r_mdccint_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_mdccint_el1 d a b)
| [|- context[?d {r_disr_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_disr_el1 d a b)
| [|- context[?d {r_mpam0_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_mpam0_el1 d a b)
| [|- context[?d {r_cnthctl_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_cnthctl_el2 d a b)
| [|- context[?d {r_cntvoff_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_cntvoff_el2 d a b)
| [|- context[?d {r_cntpoff_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_cntpoff_el2 d a b)
| [|- context[?d {r_vmpidr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_vmpidr_el2 d a b)
| [|- context[?d {r_vttbr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_vttbr_el2 d a b)
| [|- context[?d {r_vtcr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_vtcr_el2 d a b)
| [|- context[?d {r_hcr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_hcr_el2 d a b)
| [|- context[?d {r_actlr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_actlr_el2 d a b)
| [|- context[?d {r_afsr0_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_afsr0_el2 d a b)
| [|- context[?d {r_afsr1_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_afsr1_el2 d a b)
| [|- context[?d {r_amair_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_amair_el2 d a b)
| [|- context[?d {r_cptr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_cptr_el2 d a b)
| [|- context[?d {r_elr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_elr_el2 d a b)
| [|- context[?d {r_esr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_esr_el2 d a b)
| [|- context[?d {r_far_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_far_el2 d a b)
| [|- context[?d {r_hacr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_hacr_el2 d a b)
| [|- context[?d {r_hpfar_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_hpfar_el2 d a b)
| [|- context[?d {r_hstr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_hstr_el2 d a b)
| [|- context[?d {r_mair_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_mair_el2 d a b)
| [|- context[?d {r_mpam_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_mpam_el2 d a b)
| [|- context[?d {r_mpamhcr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_mpamhcr_el2 d a b)
| [|- context[?d {r_pmscr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_pmscr_el2 d a b)
| [|- context[?d {r_sctlr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_sctlr_el2 d a b)
| [|- context[?d {r_scxtnum_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_scxtnum_el2 d a b)
| [|- context[?d {r_sp_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_sp_el2 d a b)
| [|- context[?d {r_spsr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_spsr_el2 d a b)
| [|- context[?d {r_tcr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_tcr_el2 d a b)
| [|- context[?d {r_tfsr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_tfsr_el2 d a b)
| [|- context[?d {r_tpidr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_tpidr_el2 d a b)
| [|- context[?d {r_trfcr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_trfcr_el2 d a b)
| [|- context[?d {r_ttbr0_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_ttbr0_el2 d a b)
| [|- context[?d {r_ttbr1_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_ttbr1_el2 d a b)
| [|- context[?d {r_vbar_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_vbar_el2 d a b)
| [|- context[?d {r_vdisr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_vdisr_el2 d a b)
| [|- context[?d {r_vncr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_vncr_el2 d a b)
| [|- context[?d {r_vpidr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_vpidr_el2 d a b)
| [|- context[?d {r_vsesr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_vsesr_el2 d a b)
| [|- context[?d {r_vstcr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_vstcr_el2 d a b)
| [|- context[?d {r_vsttbr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_vsttbr_el2 d a b)
| [|- context[?d {r_zcr_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_zcr_el2 d a b)
| [|- context[?d {r_icc_sre_el2: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_icc_sre_el2 d a b)
| [|- context[?d {r_icc_hppir1_el1: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_icc_hppir1_el1 d a b)
| [|- context[?d {r_spsr_el3: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_spsr_el3 d a b)
| [|- context[?d {r_elr_el3: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_elr_el3 d a b)
| [|- context[?d {r_esr_el3: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_esr_el3 d a b)
| [|- context[?d {r_scr_el3: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_scr_el3 d a b)
| [|- context[?d {r_tpidr_el3: ?a} {r_x4: ?b}]] => rewrite (swap_r_x4_r_tpidr_el3 d a b)
| [|- context[?d {share: ?a} {log: ?b}]] => rewrite (swap_log_share d a b)
| [|- context[?d {priv: ?a} {log: ?b}]] => rewrite (swap_log_priv d a b)
| [|- context[?d {priv: ?a} {share: ?b}]] => rewrite (swap_share_priv d a b)
| [|- context[?d {a_CZ: ?a} {a_CN: ?b}]] => rewrite (swap_a_CN_a_CZ d a b)
| [|- context[?d {a_CC: ?a} {a_CN: ?b}]] => rewrite (swap_a_CN_a_CC d a b)
| [|- context[?d {a_CV: ?a} {a_CN: ?b}]] => rewrite (swap_a_CN_a_CV d a b)
| [|- context[?d {a_DAIFCLR: ?a} {a_CN: ?b}]] => rewrite (swap_a_CN_a_DAIFCLR d a b)
| [|- context[?d {a_SP: ?a} {a_CN: ?b}]] => rewrite (swap_a_CN_a_SP d a b)
| [|- context[?d {a_PC: ?a} {a_CN: ?b}]] => rewrite (swap_a_CN_a_PC d a b)
| [|- context[?d {a_EL3: ?a} {a_CN: ?b}]] => rewrite (swap_a_CN_a_EL3 d a b)
| [|- context[?d {a_CC: ?a} {a_CZ: ?b}]] => rewrite (swap_a_CZ_a_CC d a b)
| [|- context[?d {a_CV: ?a} {a_CZ: ?b}]] => rewrite (swap_a_CZ_a_CV d a b)
| [|- context[?d {a_DAIFCLR: ?a} {a_CZ: ?b}]] => rewrite (swap_a_CZ_a_DAIFCLR d a b)
| [|- context[?d {a_SP: ?a} {a_CZ: ?b}]] => rewrite (swap_a_CZ_a_SP d a b)
| [|- context[?d {a_PC: ?a} {a_CZ: ?b}]] => rewrite (swap_a_CZ_a_PC d a b)
| [|- context[?d {a_EL3: ?a} {a_CZ: ?b}]] => rewrite (swap_a_CZ_a_EL3 d a b)
| [|- context[?d {a_CV: ?a} {a_CC: ?b}]] => rewrite (swap_a_CC_a_CV d a b)
| [|- context[?d {a_DAIFCLR: ?a} {a_CC: ?b}]] => rewrite (swap_a_CC_a_DAIFCLR d a b)
| [|- context[?d {a_SP: ?a} {a_CC: ?b}]] => rewrite (swap_a_CC_a_SP d a b)
| [|- context[?d {a_PC: ?a} {a_CC: ?b}]] => rewrite (swap_a_CC_a_PC d a b)
| [|- context[?d {a_EL3: ?a} {a_CC: ?b}]] => rewrite (swap_a_CC_a_EL3 d a b)
| [|- context[?d {a_DAIFCLR: ?a} {a_CV: ?b}]] => rewrite (swap_a_CV_a_DAIFCLR d a b)
| [|- context[?d {a_SP: ?a} {a_CV: ?b}]] => rewrite (swap_a_CV_a_SP d a b)
| [|- context[?d {a_PC: ?a} {a_CV: ?b}]] => rewrite (swap_a_CV_a_PC d a b)
| [|- context[?d {a_EL3: ?a} {a_CV: ?b}]] => rewrite (swap_a_CV_a_EL3 d a b)
| [|- context[?d {a_SP: ?a} {a_DAIFCLR: ?b}]] => rewrite (swap_a_DAIFCLR_a_SP d a b)
| [|- context[?d {a_PC: ?a} {a_DAIFCLR: ?b}]] => rewrite (swap_a_DAIFCLR_a_PC d a b)
| [|- context[?d {a_EL3: ?a} {a_DAIFCLR: ?b}]] => rewrite (swap_a_DAIFCLR_a_EL3 d a b)
| [|- context[?d {a_PC: ?a} {a_SP: ?b}]] => rewrite (swap_a_SP_a_PC d a b)
| [|- context[?d {a_EL3: ?a} {a_SP: ?b}]] => rewrite (swap_a_SP_a_EL3 d a b)
| [|- context[?d {a_EL3: ?a} {a_PC: ?b}]] => rewrite (swap_a_PC_a_EL3 d a b)
end.

Lemma get_set_reg_same:
  forall regs reg (Hreg: 0 <= reg <= 115) val,
    get_reg reg (set_reg reg val regs) = val.
Proof.
  intros. assert(0 <= reg < 116) by omega.
  destruct_case H; grewrite; simpl_update_reg; reflexivity.
Qed.

Hypothesis get_set_reg_other:
  forall regs reg reg' val,
    reg' <> reg -> get_reg reg' (set_reg reg val regs) = (get_reg reg' regs).

