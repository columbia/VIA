Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import RmiSMC.Spec.
Require Import RefTactics.
Require Import Security.RefRel.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Lemma smc_granule_delegate_security:
  forall habd habd' labd addr ret
    (Hspec: smc_granule_delegate_spec addr habd = Some (habd', ret))
    (Hrel: relate_adt habd labd) (rmm_run: cur_rec (priv habd) = None),
  exists labd', smc_granule_delegate_spec addr labd = Some (labd', ret) /\ relate_adt habd' labd'.
Proof.
  intros. destruct Hrel.
  unfold smc_granule_delegate_spec in *.
  repeat autounfold in *.
  repeat (rewrite_sec_rel; simpl_hyp Hspec; simpl in * ); extract_prop_dec; inv Hspec.
  - match goal with
    | [H: query_oracle ?hd = Some ?hd' |- context[query_oracle ?ld]] =>
      exploit (query_oracle_security hd hd' ld H)
    end; try assumption.
    clear id_share rel_secure invs.
    intros (ld & Hld & Hrel0). rewrite Hld.
    destruct Hrel0 as (id_share & invs & rel_secure).
    simpl_query_oracle' C5. simpl_query_oracle' Hld.
    rewrite_sec_rel. simpl_htarget. grewrite.
    eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. destruct_zmap; constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_data s s0 id_share). reflexivity. assumption.
      intros. rewrite (relate_share_g_regs s s0 id_share). reflexivity. assumption.
    + simpl; constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption; autounfold in *.
      * intro gidx. destruct_zmap; simpl. intros; contra. auto.
      * intro gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros. apply rec_rd in H. srewrite. omega. auto.
      * intros rd_gidx. destruct_zmap; simpl. intros; omega.
        intros until b. destruct_zmap; simpl. intros.
        exploit (table_prop rd_gidx H ipa_gidx data_gidx); srewrite; try eassumption.
        reflexivity. intros (? & ? & ?). omega. apply table_prop; assumption.
      * intros until rec_gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega. apply tlb_prop; assumption.
      * intros until rec_gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega. apply running_not_new; assumption.
      * intros rec_gidx. destruct_zmap; simpl. intros; omega. auto.
    + constructor; simpl; try assumption; autounfold in *.
      * intro rd_gidx. destruct_zmap; simpl. intros; omega.
        intros. exploit (mem_rel rd_gidx); try eassumption.
        destruct_zmap; simpl.
        exploit (table_prop rd_gidx); try eassumption.
        intros (? & ? & ?). srewrite. omega. auto.
      * intros rd_gidx rec_gidx. autounfold. destruct_zmap; simpl. intros. omega.
        destruct_zmap. simpl. intros. omega. eapply reg_not_run_rel.
      * intros until rec_gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega. intros.
        apply cur_running in running. srewrite. contra. assumption.
      * intros. rewrite regs_eq_not_realm. reflexivity. assumption.
  - match goal with
    | [H: query_oracle ?hd = Some ?hd' |- context[query_oracle ?ld]] =>
      exploit (query_oracle_security hd hd' ld H)
    end; try assumption.
    clear id_share rel_secure invs.
    intros (ld & Hld & Hrel). rewrite Hld.
    destruct Hrel as (id_share & invs & rel_secure).
    simpl_query_oracle' C5. simpl_query_oracle' Hld.
    rewrite_sec_rel. simpl_htarget. grewrite.
    eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      destruct id_share. assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      destruct id_priv. assumption.
    + simpl; constructor; simpl; rewrite_sec_rel; try assumption.
    + constructor; simpl; assumption.
  - eexists; split. reflexivity.
    constructor; simpl; assumption.
Qed.

Lemma smc_granule_undelegate_security:
  forall habd habd' labd addr ret
         (Hspec: smc_granule_undelegate_spec addr habd = Some (habd', ret))
         (Hrel: relate_adt habd labd),
  exists labd', smc_granule_undelegate_spec addr labd = Some (labd', ret) /\ relate_adt habd' labd'.
Proof.
  intros. destruct Hrel.
  unfold smc_granule_undelegate_spec in *.
  repeat autounfold in *.
  repeat (rewrite_sec_rel; simpl_hyp Hspec; simpl in * ); extract_prop_dec; inv Hspec.
  - match goal with
    | [H: query_oracle ?hd = Some ?hd' |- context[query_oracle ?ld]] =>
      exploit (query_oracle_security hd hd' ld H)
    end; try assumption.
    clear id_share rel_secure invs.
    intros (ld & Hld & Hrel0). rewrite Hld.
    destruct Hrel0 as (id_share & invs & rel_secure).
    simpl_query_oracle' C4. simpl_query_oracle' Hld.
    rewrite_sec_rel. simpl_htarget. grewrite.
    eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. destruct_zmap; constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_data s s0 id_share). reflexivity.
      grewrite. autounfold. omega.
      intros. rewrite (relate_share_g_regs s s0 id_share). reflexivity.
      grewrite. autounfold. omega.
      intros. rewrite (relate_share_g_data s s0 id_share). reflexivity. assumption.
      intros. rewrite (relate_share_g_regs s s0 id_share). reflexivity. assumption.
    + simpl; constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption; autounfold in *.
      * intro gidx. destruct_zmap; simpl. reflexivity. auto.
      * intro gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros. apply rec_rd in H. srewrite. omega. auto.
      * intros rd_gidx. destruct_zmap; simpl. intros; omega.
        intros until b. destruct_zmap; simpl. intros.
        exploit (table_prop rd_gidx H ipa_gidx data_gidx); srewrite; try eassumption.
        reflexivity. intros (? & ? & ?). omega. apply table_prop; assumption.
      * intros until rec_gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega. apply tlb_prop; assumption.
      * intros until rec_gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega. apply running_not_new; assumption.
      * intros rec_gidx. destruct_zmap; simpl. intros; omega. auto.
    + constructor; simpl; try assumption; autounfold in *.
      * intro rd_gidx. destruct_zmap; simpl. intros; omega.
        intros. exploit (mem_rel rd_gidx); try eassumption.
        destruct_zmap; simpl.
        exploit (table_prop rd_gidx); try eassumption.
        intros (? & ? & ?). srewrite. omega. auto.
      * intros rd_gidx rec_gidx. autounfold. destruct_zmap; simpl. intros. omega.
        destruct_zmap. simpl. intros. omega. eapply reg_not_run_rel.
      * intros until rec_gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega. intros.
        apply cur_running in running. srewrite. contra. assumption.
      * intros. rewrite regs_eq_not_realm. reflexivity. assumption.
  - match goal with
    | [H: query_oracle ?hd = Some ?hd' |- context[query_oracle ?ld]] =>
      exploit (query_oracle_security hd hd' ld H)
    end; try assumption.
    clear id_share rel_secure invs.
    intros (ld & Hld & Hrel). rewrite Hld.
    destruct Hrel as (id_share & invs & rel_secure).
    simpl_query_oracle' C4. simpl_query_oracle' Hld.
    rewrite_sec_rel. simpl_htarget. grewrite.
    eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      destruct id_share. assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      destruct id_priv. assumption.
    + simpl; constructor; simpl; rewrite_sec_rel; try assumption.
    + constructor; simpl; assumption.
  - eexists; split. reflexivity.
    constructor; simpl; assumption.
Qed.

Lemma smc_realm_create_security:
  forall habd habd' labd rd_addr realm_param_addr ret
    (Hspec: smc_realm_create_spec rd_addr realm_param_addr habd = Some (habd', ret))
    (Hrel: relate_adt habd labd) (rmm_run: cur_rec (priv habd) = None),
  exists labd', smc_realm_create_spec rd_addr realm_param_addr labd = Some (labd', ret) /\ relate_adt habd' labd'.
Proof.
  intros. destruct Hrel.
  unfold smc_realm_create_spec in *.
  repeat autounfold in *.
  repeat (rewrite_sec_rel; simpl_hyp Hspec; simpl in * ); extract_prop_dec; inv Hspec.
  - repeat (rewrite_sec_rel; grewrite; simpl_htarget; simpl).
    assert(Hnd: gtype (gs (share habd)) @ (__addr_to_gidx z0) <> GRANULE_STATE_DATA). autounfold; omega.
    repeat rewrite (relate_share_g_data _ _ id_share _ Hnd). grewrite.
    simpl in *. red in Prop5. red in Prop6. red in Prop4.
    repeat (rewrite_sec_rel; grewrite; simpl_htarget; simpl).
    match goal with
    | [H: query_oracle ?hd = Some ?hd' |- context[query_oracle ?ld]] =>
      exploit (query_oracle_security hd hd' ld H)
    end; try assumption.
    { duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
      constructor; simpl; try assumption. }
    { duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
      constructor; simpl; try assumption. }
    intros (ld & Hld & Hrel0). rewrite Hld.
    clear id_share rel_secure invs.
    destruct Hrel0 as (id_share & invs & rel_secure).
    simpl_query_oracle' C22. simpl_query_oracle' Hld.
    repeat (rewrite_sec_rel; grewrite; simpl_htarget; simpl).
    eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_data _ _ id_share). reflexivity.
      grewrite. autounfold; omega.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity.
      grewrite. autounfold; omega.
      destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_data _ _ id_share). reflexivity.
      grewrite. autounfold; omega.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity.
      grewrite. autounfold; omega.
      destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_data _ _ id_share). reflexivity.
      grewrite. autounfold; omega.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity.
      grewrite. autounfold; omega.
      destruct id_share; auto.
    + simpl; constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption; autounfold in *.
      * intro gidx.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        auto.
      * intro rd_gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros. srewrite.
        pose proof (rec_rd rd_gidx). apply H0 in H. srewrite. omega.
        destruct_zmap; simpl. intros. srewrite.
        pose proof (rec_rd rd_gidx). apply H0 in H. srewrite. omega.
        destruct_zmap; simpl. intros. srewrite.
        pose proof (rec_rd rd_gidx). apply H0 in H. srewrite. omega.
        auto.
      * intro rd_gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros until b.
        intros. rewrite new_table in H0. inv H0.
        bool_rel_all; omega. grewrite. omega.
        intros until b.
        destruct_zmap; simpl. intros. rewrite <- Heq2 in *.
        exploit (table_prop rd_gidx); try eassumption.
        intros (? & ? & ?). srewrite. omega.
        destruct_zmap; simpl. intros. rewrite <- Heq3 in *.
        exploit (table_prop rd_gidx); try eassumption.
        intros (? & ? & ?). srewrite. omega.
        destruct_zmap; simpl. intros. rewrite <- Heq4 in *.
        exploit (table_prop rd_gidx); try eassumption.
        intros (? & ? & ?). srewrite. omega.
        intros. eapply table_prop; eassumption.
      * intros rd_gidx rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. apply cur_running in running. srewrite. contra. assumption.
        intros. eapply tlb_prop; eassumption.
      * intros rd_gidx rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. apply cur_running in running. srewrite. contra. assumption.
        apply running_not_new; eassumption.
      * intro rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply cur_running.
    + constructor; simpl; try assumption; autounfold in *.
      * intro rd_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. erewrite new_table in Hwalk. inv Hwalk. srewrite. omega.
        intros. destruct_zmap; simpl. rewrite <- Heq2. apply mem_rel; assumption.
        destruct_zmap; simpl. rewrite <- Heq3. apply mem_rel; assumption.
        destruct_zmap; simpl. rewrite <- Heq4. apply mem_rel; assumption.
        apply mem_rel; assumption.
      * intros rd_gidx rec_gidx. autounfold.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. pose proof (rec_rd rec_gidx). apply H in is_rec. srewrite. omega.
        apply reg_not_run_rel.
      * intros until rec_gidx. destruct_zmap; simpl. intros; omega.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. apply cur_running in running. srewrite. contra. assumption.
        apply reg_running_rel.
  - repeat (rewrite_sec_rel; grewrite; simpl_htarget; simpl).
    assert(Hnd: gtype (gs (share habd)) @ (__addr_to_gidx z0) <> GRANULE_STATE_DATA). autounfold; omega.
    repeat rewrite (relate_share_g_data _ _ id_share _ Hnd). grewrite.
    simpl in *. red in Prop5. red in Prop3. red in Prop4.
    repeat (rewrite_sec_rel; grewrite; simpl_htarget; simpl).
    match goal with
    | [H: query_oracle ?hd = Some ?hd' |- context[query_oracle ?ld]] =>
      exploit (query_oracle_security hd hd' ld H)
    end; try assumption.
    { duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
      constructor; simpl; try assumption.}
    { duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
      constructor; simpl; try assumption.}
    intros (ld & Hld & Hrel0). rewrite Hld.
    clear id_share rel_secure invs.
    destruct Hrel0 as (id_share & invs & rel_secure).
    simpl_query_oracle' C22. simpl_query_oracle' Hld.
    repeat (rewrite_sec_rel; grewrite; simpl_htarget; simpl).
    eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + simpl; constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption; autounfold in *.
    + constructor; simpl; try assumption.
  - repeat (rewrite_sec_rel; grewrite; simpl_htarget; simpl).
    assert(Hnd: gtype (gs (share habd)) @ (__addr_to_gidx z0) <> GRANULE_STATE_DATA). autounfold; omega.
    repeat rewrite (relate_share_g_data _ _ id_share _ Hnd). grewrite.
    eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + simpl; constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption; autounfold in *.
    + constructor; simpl; try assumption.
  - repeat (rewrite_sec_rel; grewrite; simpl_htarget; simpl).
    assert(Hnd: gtype (gs (share habd)) @ (__addr_to_gidx z0) <> GRANULE_STATE_DATA). autounfold; omega.
    repeat rewrite (relate_share_g_data _ _ id_share _ Hnd). grewrite.
    eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + simpl; constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption; autounfold in *.
    + constructor; simpl; try assumption.
  - repeat (rewrite_sec_rel; grewrite; simpl_htarget; simpl).
    repeat rewrite (relate_share_g_data _ _ id_share _ Hnd). grewrite.
    eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; try assumption; autounfold in *.
    + constructor; simpl; try assumption.
  - eexists; split. reflexivity.
    constructor; simpl; assumption.
Qed.

Lemma smc_realm_destroy_security:
  forall habd habd' labd rd_addr ret
    (Hspec: smc_realm_destroy_spec rd_addr habd = Some (habd', ret))
    (Hrel: relate_adt habd labd),
  exists labd', smc_realm_destroy_spec rd_addr labd = Some (labd', ret) /\ relate_adt habd' labd'.
Proof.
  Local Opaque peq ptr_eq.
  intros. destruct Hrel.
  unfold smc_realm_destroy_spec in *.
  repeat autounfold in *.
  rewrite_sec_rel.
  simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
  exploit (query_oracle_security habd r labd C3); try assumption.
  clear id_share rel_secure invs.
  intros (ld & Hld & Hrel0). rewrite Hld.
  destruct Hrel0 as (id_share & invs & rel_secure).
  simpl_query_oracle' C3. simpl_query_oracle' Hld.
  repeat (rewrite_sec_rel; simpl_hyp Hspec; simpl in * ); extract_prop_dec; inv Hspec.
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      destruct id_share; auto.
    + constructor; simpl; try assumption; autounfold in *.
      * intro gidx.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        auto.
      * intro rd_gidx. repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. exploit rd_gcnt; try eassumption. eexists. split; eassumption.
        intro T; inv T. intros. pose proof (rec_rd rd_gidx). apply H0 in H. srewrite. omega.
        intros. pose proof (rec_rd rd_gidx). apply H0 in H. srewrite. omega.
        intros. pose proof (rec_rd rd_gidx). apply H0 in H. srewrite. omega.
      * intro rd_gidx. repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros until b. intros.
        exploit (table_prop rd_gidx); try eassumption.
        intros (? & ? & ?).
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        srewrite. omega. srewrite. omega. srewrite. omega.
      * intros rd_gidx rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. apply cur_running in running. srewrite. contra. assumption.
      * intros rd_gidx rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. apply cur_running in running. srewrite. contra. assumption.
      * intro rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply cur_running.
    + constructor; simpl; try assumption; autounfold in *.
      * intro rd_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. exploit table_prop; try eassumption.
        intros (Ha & Hb & Hc).
        destruct_zmap; simpl. srewrite. omega.
        destruct_zmap; simpl. srewrite. omega.
        destruct_zmap; simpl. srewrite. omega.
        apply mem_rel; assumption.
      * intros rd_gidx rec_gidx. autounfold.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_not_run_rel.
      * intros until rec_gidx. destruct_zmap; simpl. intros; omega.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_running_rel.
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - inv Hspec. eexists; split. reflexivity.
    constructor; simpl; assumption.
Qed.

Lemma smc_realm_activate_security:
  forall habd habd' labd addr ret
    (Hspec: smc_realm_activate_spec addr habd = Some (habd', ret))
    (Hrel: relate_adt habd labd),
  exists labd', smc_realm_activate_spec addr labd = Some (labd', ret) /\ relate_adt habd' labd'.
Proof.
  intros. destruct Hrel.
  unfold smc_realm_activate_spec in *.
  repeat autounfold in *.
  repeat (rewrite_sec_rel; simpl_hyp Hspec; simpl in * ); extract_prop_dec; inv Hspec.
  - match goal with
    | [H: query_oracle ?hd = Some ?hd' |- context[query_oracle ?ld]] =>
      exploit (query_oracle_security hd hd' ld H)
    end; try assumption.
    clear id_share rel_secure invs.
    intros (ld & Hld & Hrel0). rewrite Hld.
    destruct Hrel0 as (id_share & invs & rel_secure).
    simpl_query_oracle' C3. simpl_query_oracle' Hld.
    rewrite_sec_rel. simpl_htarget. grewrite.
    eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. destruct_zmap; constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_data s s0 id_share). reflexivity.
      grewrite. autounfold. omega.
      intros. rewrite (relate_share_g_regs s s0 id_share). reflexivity.
      grewrite. autounfold. omega.
      intros. rewrite (relate_share_g_data s s0 id_share). reflexivity. assumption.
      intros. rewrite (relate_share_g_regs s s0 id_share). reflexivity. assumption.
    + constructor; simpl; try assumption; autounfold in *.
      * intro gidx. destruct_zmap; simpl; auto.
      * intro gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros. apply rec_rd in H. srewrite. omega. auto.
      * intros rd_gidx. destruct_zmap; simpl.
        intros until b. destruct_zmap; simpl. intros.
        rewrite <- Heq in H. exploit (table_prop rd_gidx H ipa_gidx data_gidx); srewrite; try eassumption.
        auto. apply table_prop; try assumption.
        intros until b. destruct_zmap; simpl. intros.
        exploit (table_prop rd_gidx H ipa_gidx data_gidx); srewrite; try eassumption. reflexivity.
        auto. apply table_prop; try assumption.
      * intros until rec_gidx. destruct_zmap; simpl.
        destruct_zmap; simpl. intros; omega. apply tlb_prop; assumption.
        destruct_zmap; simpl. intros; omega. apply tlb_prop; assumption.
      * intros until rec_gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega. apply running_not_new; assumption.
      * intros rec_gidx. destruct_zmap; simpl. intros; omega. auto.
    + constructor; simpl; try assumption; autounfold in *.
      * intro rd_gidx. destruct_zmap; simpl.
        intros. rewrite <- Heq in *. exploit (mem_rel rd_gidx); try eassumption.
        destruct_zmap; simpl.
        exploit (table_prop rd_gidx); try eassumption.
        intros (? & ? & ?). srewrite. omega. auto.
        intros. exploit (mem_rel rd_gidx); try eassumption.
        destruct_zmap; simpl.
        exploit (table_prop rd_gidx); try eassumption.
        intros (? & ? & ?). srewrite. omega. auto.
      * intros rd_gidx rec_gidx. autounfold. destruct_zmap; simpl.
        destruct_zmap. simpl. intros. omega. eapply reg_not_run_rel.
        destruct_zmap. simpl. intros. omega. eapply reg_not_run_rel.
      * intros until rec_gidx. destruct_zmap; simpl.
        destruct_zmap; simpl. intros; omega. intros.
        apply cur_running in running. srewrite. contra. assumption.
        destruct_zmap; simpl. intros; omega. intros.
        apply cur_running in running. srewrite. contra. assumption.
  - match goal with
    | [H: query_oracle ?hd = Some ?hd' |- context[query_oracle ?ld]] =>
      exploit (query_oracle_security hd hd' ld H)
    end; try assumption.
    clear id_share rel_secure invs.
    intros (ld & Hld & Hrel0). rewrite Hld.
    destruct Hrel0 as (id_share & invs & rel_secure).
    simpl_query_oracle' C3. simpl_query_oracle' Hld.
    rewrite_sec_rel. simpl_htarget. grewrite.
    eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. destruct_zmap; constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_data s s0 id_share). reflexivity.
      grewrite. autounfold. omega.
      intros. rewrite (relate_share_g_regs s s0 id_share). reflexivity.
      grewrite. autounfold. omega.
      intros. rewrite (relate_share_g_data s s0 id_share). reflexivity. assumption.
      intros. rewrite (relate_share_g_regs s s0 id_share). reflexivity. assumption.
    + constructor; simpl; try assumption; autounfold in *.
      * intro gidx. destruct_zmap; simpl; auto.
      * intro gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros. apply rec_rd in H. srewrite. omega. auto.
      * intros rd_gidx. destruct_zmap; simpl.
        intros until b. destruct_zmap; simpl. intros.
        rewrite <- Heq in H. exploit (table_prop rd_gidx H ipa_gidx data_gidx); srewrite; try eassumption.
        auto. apply table_prop; try assumption.
        intros until b. destruct_zmap; simpl. intros.
        exploit (table_prop rd_gidx H ipa_gidx data_gidx); srewrite; try eassumption. reflexivity.
        auto. apply table_prop; try assumption.
      * intros until rec_gidx. destruct_zmap; simpl.
        destruct_zmap; simpl. intros; omega. apply tlb_prop; assumption.
        destruct_zmap; simpl. intros; omega. apply tlb_prop; assumption.
      * intros until rec_gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega. apply running_not_new; assumption.
      * intros rec_gidx. destruct_zmap; simpl. intros; omega. auto.
    + constructor; simpl; try assumption; autounfold in *.
      * intro rd_gidx. destruct_zmap; simpl.
        intros. rewrite <- Heq in *. exploit (mem_rel rd_gidx); try eassumption.
        destruct_zmap; simpl.
        exploit (table_prop rd_gidx); try eassumption.
        intros (? & ? & ?). srewrite. omega. auto.
        intros. exploit (mem_rel rd_gidx); try eassumption.
        destruct_zmap; simpl.
        exploit (table_prop rd_gidx); try eassumption.
        intros (? & ? & ?). srewrite. omega. auto.
      * intros rd_gidx rec_gidx. autounfold. destruct_zmap; simpl.
        destruct_zmap. simpl. intros. omega. eapply reg_not_run_rel.
        destruct_zmap. simpl. intros. omega. eapply reg_not_run_rel.
      * intros until rec_gidx. destruct_zmap; simpl.
        destruct_zmap; simpl. intros; omega. intros.
        apply cur_running in running. srewrite. contra. assumption.
        destruct_zmap; simpl. intros; omega. intros.
        apply cur_running in running. srewrite. contra. assumption.
  - match goal with
    | [H: query_oracle ?hd = Some ?hd' |- context[query_oracle ?ld]] =>
      exploit (query_oracle_security hd hd' ld H)
    end; try assumption.
    clear id_share rel_secure invs.
    intros (ld & Hld & Hrel). rewrite Hld.
    destruct Hrel as (id_share & invs & rel_secure).
    simpl_query_oracle' C3. simpl_query_oracle' Hld.
    rewrite_sec_rel. simpl_htarget. grewrite.
    eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      destruct id_share. assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      destruct id_priv. assumption.
    + simpl; constructor; simpl; rewrite_sec_rel; try assumption.
    + constructor; simpl; assumption.
  - match goal with
    | [H: query_oracle ?hd = Some ?hd' |- context[query_oracle ?ld]] =>
      exploit (query_oracle_security hd hd' ld H)
    end; try assumption.
    clear id_share rel_secure invs.
    intros (ld & Hld & Hrel). rewrite Hld.
    destruct Hrel as (id_share & invs & rel_secure).
    simpl_query_oracle' C3. simpl_query_oracle' Hld.
    rewrite_sec_rel. simpl_htarget. grewrite.
    eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      destruct id_share. assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      destruct id_priv. assumption.
    + simpl; constructor; simpl; rewrite_sec_rel; try assumption.
    + constructor; simpl; assumption.
  - eexists; split. reflexivity.
    constructor; simpl; assumption.
Qed.

Lemma smc_rec_create_security:
  forall habd habd' labd rec_addr rd_addr mpidr rec_param_addr ret
    (Hspec: smc_rec_create_spec rec_addr rd_addr mpidr rec_param_addr habd = Some (habd', ret))
    (Hrel: relate_adt habd labd) (rmm_run: cur_rec (priv habd) = None),
  exists labd', smc_rec_create_spec rec_addr rd_addr mpidr rec_param_addr labd = Some (labd', ret) /\ relate_adt habd' labd'.
Proof.
  intros. destruct Hrel.
  unfold smc_rec_create_spec in *. repeat autounfold in *.
  simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
  simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
  simpl_hyp Hspec. exploit (query_oracle_security habd r labd C9); try assumption.
  clear id_share rel_secure invs.
  intros (ld & Hld & Hrel0). rewrite Hld.
  destruct Hrel0 as (id_share & invs & rel_secure).
  simpl_query_oracle' C9. simpl_query_oracle' Hld.
  repeat (rewrite_sec_rel; simpl_hyp Hspec; simpl in * ); extract_prop_dec; inv Hspec;
    repeat (grewrite; try simpl_htarget; simpl).
  - rewrite (relate_share_g_data _ _ id_share). grewrite.
    rewrite (relate_share_g_data _ _ id_share). simpl_htarget.
    eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity.
      grewrite. autounfold; omega.
      destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_data _ _ id_share). reflexivity.
      grewrite. autounfold; omega.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity.
      grewrite. autounfold; omega.
      destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_data _ _ id_share). reflexivity.
      grewrite. autounfold; omega.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity.
      grewrite. autounfold; omega. unfold init_grec. simpl.
      destruct id_share; auto.
    + simpl; constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption; autounfold in *.
      * intro gidx.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        auto.
      * intro rd_gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. destruct_zmap; simpl.
        symmetry in Heq2. srewrite. rewrite ZMap.gss. simpl. intros. assumption.
        rewrite ZMap.gss. simpl; intros. assumption.
        destruct_zmap; simpl.
        intros. pose proof (rec_rd rd_gidx). apply H0 in H. srewrite. omega.
        destruct_zmap; simpl.
        intros. pose proof (rec_rd rd_gidx). apply H0 in H. srewrite. omega.
        destruct_zmap; simpl.
        intros. pose proof (rec_rd rd_gidx). apply H0 in H. srewrite. omega.
        auto.
      * intro rd_gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros. rewrite <- Heq0 in *.
        exploit (table_prop rd_gidx); try eassumption.
        intros (? & ? & ?).
        destruct_zmap; simpl. srewrite; omega.
        destruct_zmap; simpl. srewrite; omega.
        destruct_zmap; simpl. srewrite; omega.
        eapply table_prop; eassumption.
        destruct_zmap; simpl. intros; omega. intros.
        exploit (table_prop rd_gidx); try eassumption.
        intros (? & ? & ?).
        destruct_zmap; simpl. srewrite; omega.
        destruct_zmap; simpl. srewrite; omega.
        destruct_zmap; simpl. srewrite; omega.
        eapply table_prop; eassumption.
      * intros rd_gidx rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        exploit (delegate_zero s (__addr_to_gidx z)). assumption.
        intros (Ha & Hb). intros. srewrite. inv running.
        intros. rewrite <- Heq0 in *.
        eapply tlb_prop; eassumption. eapply tlb_prop; eassumption.
      * intros rd_gidx rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. exploit (delegate_zero s (__addr_to_gidx z)). assumption.
        intros (Ha & Hb). intros. srewrite. inv running.
        intros. rewrite <- Heq0 in *.
        eapply running_not_new; eassumption. eapply running_not_new; eassumption.
      * intro rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. exploit (delegate_zero s (__addr_to_gidx z)). assumption.
        intros (Ha & Hb). intros. srewrite. inv running.
        apply cur_running.
    + constructor; simpl; try assumption; autounfold in *.
      * intro rd_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. exploit table_prop; try eassumption. intros (Ha & Hb & Hc).
        destruct_zmap; simpl. srewrite. omega.
        destruct_zmap; simpl. srewrite. omega.
        destruct_zmap; simpl. srewrite. omega.
        apply mem_rel; assumption.
        intros. exploit table_prop; try eassumption. intros (Ha & Hb & Hc).
        destruct_zmap; simpl. srewrite. omega.
        destruct_zmap; simpl. srewrite. omega.
        destruct_zmap; simpl. srewrite. omega.
        apply mem_rel; assumption.
      * intros rd_gidx rec_gidx. autounfold.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. erewrite new_decl_regs. simpl.
        intros. exploit (delegate_zero s (__addr_to_gidx z)). assumption.
        intros (Ha & Hb).
        intros. exploit (delegate_zero s0 (__addr_to_gidx z)). rewrite_sec_rel. assumption.
        intros (Ha' & Hb'). intros. srewrite. reflexivity.
        assumption. bool_rel_all. assumption.
        rewrite <- Heq0. apply reg_not_run_rel. apply reg_not_run_rel.
      * intros until rec_gidx. destruct_zmap; simpl. intros; omega.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. exploit (delegate_zero s (__addr_to_gidx z)). assumption.
        intros (Ha & Hb). intros. srewrite. inv running.
        intros. apply cur_running in running. srewrite. contra. assumption.
        intros. apply cur_running in running. srewrite. contra. assumption.
    + autounfold. bool_rel_all. omega.
    + autounfold. bool_rel_all. omega.
  - rewrite (relate_share_g_data _ _ id_share). grewrite.
    rewrite (relate_share_g_data _ _ id_share). simpl_htarget.
    eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption; autounfold in *.
    + constructor; simpl; try assumption.
    + autounfold. bool_rel_all. omega.
    + autounfold. bool_rel_all. omega.
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - rewrite_sec_rel. extract_prop_dec. simpl_htarget. inv Hspec.
    eexists; split. reflexivity. constructor; assumption.
Qed.

Lemma smc_rec_destroy_security:
  forall habd habd' labd rec_addr ret
    (Hspec: smc_rec_destroy_spec rec_addr habd = Some (habd', ret))
    (Hrel: relate_adt habd labd),
  exists labd', smc_rec_destroy_spec rec_addr labd = Some (labd', ret) /\ relate_adt habd' labd'.
Proof.
  Local Opaque peq ptr_eq.
  intros. destruct Hrel.
  unfold smc_rec_destroy_spec in *.
  repeat autounfold in *.
  rewrite_sec_rel.
  simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
  exploit (query_oracle_security habd r labd C3); try assumption.
  clear id_share rel_secure invs.
  intros (ld & Hld & Hrel0). rewrite Hld.
  destruct Hrel0 as (id_share & invs & rel_secure).
  simpl_query_oracle' C3. simpl_query_oracle' Hld.
  repeat (rewrite_sec_rel; simpl_hyp Hspec; simpl in * ); extract_prop_dec; inv Hspec.
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_data _ _ id_share). reflexivity.
      grewrite. autounfold; omega.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity.
      grewrite. autounfold; omega.
      destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_data _ _ id_share). reflexivity.
      grewrite. autounfold; omega.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity.
      grewrite. autounfold; omega.
      destruct id_share; auto.
    + constructor; simpl; try assumption; autounfold in *.
      * intro gidx.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        auto.
      * intro rd_gidx. repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. pose proof (rec_rd rd_gidx). apply H0 in H. srewrite. omega.
        intros. pose proof (rec_rd rd_gidx). apply H0 in H. srewrite. omega.
        auto.
      * intro rd_gidx. repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros until b. intros.
        rewrite <- Heq in *. exploit (table_prop rd_gidx); try eassumption.
        intros (? & ? & ?).
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        srewrite. omega. srewrite. omega. srewrite. omega.
        intros until b. intros.
        exploit (table_prop rd_gidx); try eassumption.
        intros (? & ? & ?).
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        srewrite. omega. srewrite. omega. srewrite. omega.
      * intros rd_gidx rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. apply cur_running in running. srewrite. contra. assumption.
        apply tlb_prop.
      * intros rd_gidx rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. apply cur_running in running. srewrite. contra. assumption.
        apply running_not_new.
      * intro rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply cur_running.
    + constructor; simpl; try assumption; autounfold in *.
      * intro rd_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. rewrite <- Heq in *.  exploit table_prop; try eassumption.
        intros (Ha & Hb & Hc).
        destruct_zmap; simpl. srewrite. omega.
        destruct_zmap; simpl. srewrite. omega.
        destruct_zmap; simpl. srewrite. omega.
        apply mem_rel; assumption.
        intros. exploit table_prop; try eassumption.
        intros (Ha & Hb & Hc).
        destruct_zmap; simpl. srewrite. omega.
        destruct_zmap; simpl. srewrite. omega.
        destruct_zmap; simpl. srewrite. omega.
        apply mem_rel; assumption.
      * intros rd_gidx rec_gidx. autounfold.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_not_run_rel. apply reg_not_run_rel.
      * intros until rec_gidx. destruct_zmap; simpl.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_running_rel.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_running_rel.
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - inv Hspec. eexists; split. reflexivity.
    constructor; simpl; assumption.
Qed.
