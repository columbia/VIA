Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiAux2.Spec.
Require Import RefTactics.

Local Open Scope Z_scope.

Definition rec_create_ops_origin (g_rd: Pointer) (g_rec: Pointer) (rd: Pointer) (rec_list: Pointer) (rec: Pointer) (mpidr: Z64) (rec_idx: Z64) (adt: RData) : option RData :=
  match g_rd, g_rec, rd, rec_list, rec, mpidr, rec_idx with
  | (_g_rd_base, _g_rd_ofst), (_g_rec_base, _g_rec_ofst), (_rd_base, _rd_ofst), (_rec_list_base, _rec_list_ofst), (_rec_base, _rec_ofst), VZ64 _mpidr, VZ64 _rec_idx =>
    when adt == granule_set_state_spec (_g_rec_base, _g_rec_ofst) 3 adt;
    when adt == realm_set_rec_entry_spec (VZ64 _rec_idx) (_rec_list_base, _rec_list_ofst) (_g_rec_base, _g_rec_ofst) adt;
    when adt == init_rec_read_only_spec (_rec_base, _rec_ofst) (_g_rec_base, _g_rec_ofst) (VZ64 _rec_idx) adt;
    when adt == init_rec_regs_spec (_rec_base, _rec_ofst) (VZ64 _mpidr) (_rd_base, _rd_ofst) adt;
    when'' _t'1_base, _t'1_ofst == get_rec_rvic_spec (_rec_base, _rec_ofst) adt;
    when adt == init_rec_rvic_state_spec (_t'1_base, _t'1_ofst) adt;
    when' _t'2 == get_rd_par_base_spec (_rd_base, _rd_ofst) adt;
    when adt == set_rec_par_base_spec (_rec_base, _rec_ofst) (VZ64 _t'2) adt;
    when' _t'3 == get_rd_par_end_spec (_rd_base, _rd_ofst) adt;
    when adt == set_rec_par_end_spec (_rec_base, _rec_ofst) (VZ64 _t'3) adt;
    when adt == set_rec_g_rd_spec (_rec_base, _rec_ofst) (_g_rd_base, _g_rd_ofst) adt;
    when'' _t'4_base, _t'4_ofst == get_rd_g_rec_list_spec (_rd_base, _rd_ofst) adt;
    rely prop_dec ((buffer (priv adt)) @ _rd_ofst <> (buffer (priv adt)) @ _rec_ofst);
    rely prop_dec ((buffer (priv adt)) @ _rd_ofst = Some _g_rd_ofst);
    rely prop_dec ((buffer (priv adt)) @ _rec_ofst = Some _g_rec_ofst);
    when adt == set_rec_g_rec_list_spec (_rec_base, _rec_ofst) (_t'4_base, _t'4_ofst) adt;
    when adt == rec_granule_measure_spec (_rd_base, _rd_ofst) (_rec_base, _rec_ofst) (VZ64 4096) adt;
    when adt == set_g_rec_rd_spec (_g_rec_base, _g_rec_ofst) (_g_rd_base, _g_rd_ofst) adt;
    when adt == atomic_granule_get_spec (_g_rd_base, _g_rd_ofst) adt;
    when' _t'5 == get_rec_params_flags_spec  adt;
    when adt == set_rec_runnable_spec (_rec_base, _rec_ofst) (Z.land _t'5 1) adt;
    Some adt
  end.

Definition rec_create_ops_perm (g_rd: Pointer) (g_rec: Pointer) (rd: Pointer) (rec_list: Pointer) (rec: Pointer) (mpidr: Z64) (rec_idx: Z64) (adt: RData) : option RData :=
  match g_rd, g_rec, rd, rec_list, rec, mpidr, rec_idx with
  | (_g_rd_base, _g_rd_ofst), (_g_rec_base, _g_rec_ofst), (_rd_base, _rd_ofst), (_rec_list_base, _rec_list_ofst), (_rec_base, _rec_ofst), VZ64 _mpidr, VZ64 _rec_idx =>
    when adt == granule_set_state_spec (_g_rec_base, _g_rec_ofst) 3 adt;
    when adt == realm_set_rec_entry_spec (VZ64 _rec_idx) (_rec_list_base, _rec_list_ofst) (_g_rec_base, _g_rec_ofst) adt;
    when adt == init_rec_read_only_spec (_rec_base, _rec_ofst) (_g_rec_base, _g_rec_ofst) (VZ64 _rec_idx) adt;
    when adt == init_rec_regs_spec (_rec_base, _rec_ofst) (VZ64 _mpidr) (_rd_base, _rd_ofst) adt;
    when'' _t'1_base, _t'1_ofst == get_rec_rvic_spec (_rec_base, _rec_ofst) adt;
    when adt == init_rec_rvic_state_spec (_t'1_base, _t'1_ofst) adt;
    when' _t'2 == get_rd_par_base_spec (_rd_base, _rd_ofst) adt;
    when adt == set_rec_par_base_spec (_rec_base, _rec_ofst) (VZ64 _t'2) adt;
    when' _t'3 == get_rd_par_end_spec (_rd_base, _rd_ofst) adt;
    when adt == set_rec_par_end_spec (_rec_base, _rec_ofst) (VZ64 _t'3) adt;
    when adt == set_rec_g_rd_spec (_rec_base, _rec_ofst) (_g_rd_base, _g_rd_ofst) adt;
    when'' _t'4_base, _t'4_ofst == get_rd_g_rec_list_spec (_rd_base, _rd_ofst) adt;
    when adt == atomic_granule_get_spec (_g_rd_base, _g_rd_ofst) adt;
    when adt == set_rec_g_rec_list_spec (_rec_base, _rec_ofst) (_t'4_base, _t'4_ofst) adt;
    when adt == rec_granule_measure_spec (_rd_base, _rd_ofst) (_rec_base, _rec_ofst) (VZ64 4096) adt;
    when adt == set_g_rec_rd_spec (_g_rec_base, _g_rec_ofst) (_g_rd_base, _g_rd_ofst) adt;
    when' _t'5 == get_rec_params_flags_spec  adt;
    when adt == set_rec_runnable_spec (_rec_base, _rec_ofst) (Z.land _t'5 1) adt;
    Some adt
  end.

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
   | [H: context [(?map # ?key == ?val) @ ?key] |- _]=> rewrite ZMap.gss in H
   | H:?key1 <> ?key2 |- context [(?map # ?key2 == ?val) @ ?key1] => rewrite (ZMap.gso _ _ H)
   | H:?key1 <> ?key2, H2: context [(?map # ?key2 == ?val) @ ?key1] |- _ => rewrite (ZMap.gso _ _ H) in H2
   | H:?key2 <> ?key1 |- context [(?map # ?key2 == ?val) @ ?key1] => let T := fresh "tmp" in
                                                  let X := fresh "tmp" in
                                                  assert (key1 <> key2) as T by (red; intro X; rewrite X in *; contra); rewrite (ZMap.gso _ _ T); clear T
   | H:?key2 <> ?key1, H2: context [(?map # ?key2 == ?val) @ ?key1] |- _ => let T := fresh "tmp" in
                                                  let X := fresh "tmp" in
                                                  assert (key1 <> key2) as T by (red; intro X; rewrite X in *; contra); rewrite (ZMap.gso _ _ T) in H2; clear T
   | |- context [(?map # ?key == ?val) # ?key == ?val2] => rewrite ZMap.set2
   | H: context [(?map # ?key == ?val) # ?key == ?val2] |- _ => rewrite ZMap.set2 in H
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

Lemma rec_create_permutation_condition:
  forall d d' g_rd g_rec rd rec_list rec mpidr rec_idx
    (Hspec: rec_create_ops_origin g_rd g_rec rd rec_list rec mpidr rec_idx d = Some d'),
    rec_create_ops_perm g_rd g_rec rd rec_list rec mpidr rec_idx d = Some d'.
Proof.
  intros. Local Opaque peq ptr_eq.
  unfold rec_create_ops_origin, rec_create_ops_perm in *.
  repeat autounfold in *. simpl in *.
  repeat simpl_hyp Hspec.
  clear C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20.
  unfold set_rec_g_rec_list_spec, atomic_granule_get_spec in *.
  unfold rec_granule_measure_spec, set_g_rec_rd_spec, set_rec_runnable_spec in *.
  autounfold in *; simpl in *.
  repeat simpl_hyp C25; inv C25; simpl in *.
  repeat simpl_hyp C26; inv C26; simpl in *.
  - repeat simpl_hyp C27; inv C27; simpl in *.
    repeat simpl_hyp C28; inv C28; simpl in *.
    repeat simpl_hyp C29; inv C29; simpl in *.
    inv Hspec. inv C1. inv C8. extract_prop_dec.
    inv Prop4. inv Prop5.
    assert(Hne1: z <> z0).
    red; intro T; inv T. contra.
    repeat (srewrite; simpl_htarget; try rewrite (zmap_comm _ _ Hne1) in *; simpl in * ).
    reflexivity.
    inv C28.
  - repeat simpl_hyp C27; inv C27; simpl in *.
    repeat simpl_hyp C28; inv C28; simpl in *.
    repeat simpl_hyp C29; inv C29; simpl in *.
    inv Hspec. inv C1. inv C8. extract_prop_dec.
    inv Prop4. inv Prop5.
    assert(Hne1: z <> z0).
    red; intro T; inv T. contra.
    repeat (srewrite; simpl_htarget; try rewrite (zmap_comm _ _ Hne1) in *; simpl in * ).
    reflexivity.
    inv C28.
Qed.
