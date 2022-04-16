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
Require Import TableAux.Specs.granule_fill_table.
Require Import TableDataSMC.Specs.smc_rtt_create.
Require Import TableDataSMC.Specs.smc_rtt_destroy.
Require Import TableDataSMC.Specs.smc_rtt_map.
Require Import TableDataSMC.Specs.smc_rtt_unmap.
Require Import TableDataSMC.Specs.smc_data_create.
Require Import TableDataSMC.Specs.smc_data_destroy.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Opaque Z.add Z.mul Z.div Z.shiftl Z.shiftr Z.land Z.lor.

Lemma create_table_secure:
  forall habd habd' labd llt_gidx idx rtt_addr rtt_gidx rd_gidx level map_addr ret
    (Hspec: create_table llt_gidx idx rtt_addr rtt_gidx rd_gidx level map_addr habd = Some (habd', ret))
    (Hrel: relate_adt habd labd) (rmm_run: cur_rec (priv habd) = None),
  exists labd', create_table llt_gidx idx rtt_addr rtt_gidx rd_gidx level map_addr labd = Some (labd', ret) /\ relate_adt habd' labd'.
Proof.
  Local Opaque ptr_eq peq fill_table.
  clear_all_hyp. intros. destruct Hrel.
  unfold create_table in *. repeat autounfold in *. simpl in *.
  repeat (rewrite_sec_rel; simpl_hyp Hspec; simpl in * ); extract_prop_dec; inv Hspec;
    repeat (rewrite (relate_share_g_data _ _ id_share); [|autounfold; bool_rel; grewrite; omega]);
    repeat (grewrite; try simpl_htarget; simpl).
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity. assumption.
      destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity.
      grewrite. autounfold; omega.
      destruct id_share; auto.
    + constructor; simpl; try assumption; autounfold in *.
      * intro gidx.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        auto.
      * intro rd_gidx'. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl.
        intros. pose proof (rec_rd rd_gidx'). apply H0 in H. srewrite. omega.
        destruct_zmap; simpl.
        intros. pose proof (rec_rd rd_gidx'). apply H0 in H. srewrite. omega.
        auto.
      * intro rd_gidx'. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega.
        intros until b. destruct_zmap; simpl.
        apply table_prop. assumption.
        destruct_zmap; simpl. intros.
        exploit (table_prop rd_gidx'); try eassumption.
        grewrite. intros (? & ? & ?). omega.
        apply table_prop. assumption.
      * intros rd_gidx' rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. apply cur_running in running; try assumption. srewrite; contra.
      * intros rd_gidx' rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        eapply running_not_new; eassumption.
      * intro rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply cur_running.
    + constructor; simpl; try assumption; autounfold in *.
      * intro rd_gidx'.
        repeat (destruct_zmap; simpl); try solve[intros; omega]. intros until data_gidx.
        intros. exploit table_prop; try eassumption. intros (Ha & Hb & Hc).
        destruct_zmap; simpl. srewrite. omega.
        destruct_zmap; simpl. srewrite. omega.
        apply mem_rel; assumption.
      * intros rd_gidx' rec_gidx. autounfold.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_not_run_rel.
      * intros until rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_running_rel.
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity. assumption.
      destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity.
      grewrite. autounfold; omega.
      destruct id_share; auto.
    + constructor; simpl; try assumption; autounfold in *.
      * intro gidx.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        auto.
      * intro rd_gidx'. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl.
        intros. pose proof (rec_rd rd_gidx'). apply H0 in H. srewrite. omega.
        destruct_zmap; simpl.
        intros. pose proof (rec_rd rd_gidx'). apply H0 in H. srewrite. omega.
        auto.
      * intro rd_gidx'. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega.
        intros until b. destruct_zmap; simpl.
        apply table_prop. assumption.
        destruct_zmap; simpl. intros.
        exploit (table_prop rd_gidx'); try eassumption.
        grewrite. intros (? & ? & ?). omega.
        apply table_prop. assumption.
      * intros rd_gidx' rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. apply cur_running in running; try assumption. srewrite; contra.
      * intros rd_gidx' rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        eapply running_not_new; eassumption.
      * intro rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply cur_running.
    + constructor; simpl; try assumption; autounfold in *.
      * intro rd_gidx'.
        repeat (destruct_zmap; simpl); try solve[intros; omega]. intros until data_gidx.
        intros. exploit table_prop; try eassumption. intros (Ha & Hb & Hc).
        destruct_zmap; simpl. srewrite. omega.
        destruct_zmap; simpl. srewrite. omega.
        apply mem_rel; assumption.
      * intros rd_gidx' rec_gidx. autounfold.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_not_run_rel.
      * intros until rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_running_rel.
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      rewrite (relate_share_tlbs _ _ id_share). reflexivity.
      intros. destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity. assumption.
      destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity.
      grewrite. autounfold; omega.
      destruct id_share; auto.
    + constructor; simpl; try assumption; autounfold in *.
      * intro gidx.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        auto.
      * intro rd_gidx'. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl.
        intros. pose proof (rec_rd rd_gidx'). apply H0 in H. srewrite. omega.
        destruct_zmap; simpl.
        intros. pose proof (rec_rd rd_gidx'). apply H0 in H. srewrite. omega.
        auto.
      * intro rd_gidx'. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega.
        intros until b. destruct_zmap; simpl.
        apply table_prop. assumption.
        destruct_zmap; simpl. intros.
        exploit (table_prop rd_gidx'); try eassumption.
        grewrite. intros (? & ? & ?). omega.
        apply table_prop. assumption.
      * intros rd_gidx' rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. apply cur_running in running; try assumption. srewrite; contra.
      * intros rd_gidx' rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        eapply running_not_new; eassumption.
      * intro rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply cur_running.
    + constructor; simpl; try assumption; autounfold in *.
      * intro rd_gidx'.
        repeat (destruct_zmap; simpl); try solve[intros; omega]. intros until data_gidx.
        intros. exploit table_prop; try eassumption. intros (Ha & Hb & Hc).
        destruct_zmap; simpl. srewrite. omega.
        destruct_zmap; simpl. srewrite. omega.
        apply mem_rel; assumption.
      * intros rd_gidx' rec_gidx. autounfold.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_not_run_rel.
      * intros until rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_running_rel.
Qed.

Lemma smc_rtt_create_security:
  forall habd habd' labd rtt_addr rd_addr map_addr level ret
    (Hspec: smc_rtt_create_spec rtt_addr rd_addr map_addr level habd = Some (habd', ret))
    (Hrel: relate_adt habd labd) (rmm_run: cur_rec (priv habd) = None),
  exists labd', smc_rtt_create_spec rtt_addr rd_addr map_addr level labd = Some (labd', ret) /\ relate_adt habd' labd'.
Proof.
  Local Opaque ptr_eq peq fill_table.
  intros. destruct Hrel.
  unfold smc_rtt_create_spec in *. repeat autounfold in *.
  simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
  simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
  simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
  exploit (query_oracle_security habd r labd C12); try assumption.
  clear id_share rel_secure invs.
  intros (ld & Hld & Hrel0). rewrite Hld.
  destruct Hrel0 as (id_share & invs & rel_secure).
  simpl_query_oracle' C12. simpl_query_oracle' Hld.
  repeat (rewrite_sec_rel; simpl_hyp Hspec; simpl in * ); extract_prop_dec; inv Hspec;
    repeat (grewrite; try simpl_htarget; simpl);
    repeat (rewrite (relate_share_g_data _ _ id_share); [|autounfold; bool_rel; grewrite; omega]);
    repeat (grewrite; try simpl_htarget; simpl).
  - eapply create_table_secure; try eassumption.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - eapply create_table_secure; try eassumption.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - eapply create_table_secure; try eassumption.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - inv Hspec. eexists; split. reflexivity. constructor; assumption.
Qed.

Lemma destroy_table_secure:
  forall habd habd' labd llt_gidx idx rtt_addr rtt_gidx level map_addr ret
    (Hspec: destroy_table llt_gidx idx rtt_addr rtt_gidx level map_addr habd = Some (habd', ret))
    (Hrel: relate_adt habd labd) (rmm_run: cur_rec (priv habd) = None),
  exists labd', destroy_table llt_gidx idx rtt_addr rtt_gidx level map_addr labd = Some (labd', ret) /\ relate_adt habd' labd'.
Proof.
  Local Opaque ptr_eq peq fill_table.
  clear_all_hyp. intros. destruct Hrel.
  unfold destroy_table in *. repeat autounfold in *. simpl in *.
  repeat (rewrite_sec_rel; simpl_hyp Hspec; simpl in * ); extract_prop_dec; inv Hspec;
    repeat (rewrite (relate_share_g_data _ _ id_share); [|autounfold; bool_rel; grewrite; omega]);
    repeat (grewrite; try simpl_htarget; simpl).
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      rewrite (relate_share_tlbs _ _ id_share). reflexivity.
      intros. destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity. assumption.
      destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      destruct id_share; auto.
    + constructor; simpl; try assumption; autounfold in *.
      * intro gidx.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        auto.
      * intro rd_gidx'. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl.
        intros. pose proof (rec_rd rd_gidx'). apply H0 in H. srewrite. omega.
        destruct_zmap; simpl.
        intros. pose proof (rec_rd rd_gidx'). apply H0 in H. srewrite. omega.
        auto.
      * intro rd_gidx'. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega.
        intros until b. destruct_zmap; simpl.
        apply table_prop. assumption.
        destruct_zmap; simpl. intros.
        exploit (table_prop rd_gidx'); try eassumption.
        grewrite. intros (? & ? & ?). omega.
        apply table_prop. assumption.
      * intros rd_gidx' rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. apply cur_running in running; try assumption. srewrite; contra.
      * intros rd_gidx' rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        eapply running_not_new; eassumption.
      * intro rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply cur_running.
    + constructor; simpl; try assumption; autounfold in *.
      * intro rd_gidx'.
        repeat (destruct_zmap; simpl); try solve[intros; omega]. intros until data_gidx.
        intros. exploit table_prop; try eassumption. intros (Ha & Hb & Hc).
        destruct_zmap; simpl. srewrite. omega.
        destruct_zmap; simpl. srewrite. omega.
        apply mem_rel; assumption.
      * intros rd_gidx' rec_gidx. autounfold.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_not_run_rel.
      * intros until rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_running_rel.
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      rewrite (relate_share_tlbs _ _ id_share). reflexivity.
      intros. destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity. assumption.
      destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      destruct id_share; auto.
    + constructor; simpl; try assumption; autounfold in *.
      * intro gidx.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        auto.
      * intro rd_gidx'. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl.
        intros. pose proof (rec_rd rd_gidx'). apply H0 in H. srewrite. omega.
        destruct_zmap; simpl.
        intros. pose proof (rec_rd rd_gidx'). apply H0 in H. srewrite. omega.
        auto.
      * intro rd_gidx'. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega.
        intros until b. destruct_zmap; simpl.
        apply table_prop. assumption.
        destruct_zmap; simpl. intros.
        exploit (table_prop rd_gidx'); try eassumption.
        grewrite. intros (? & ? & ?). omega.
        apply table_prop. assumption.
      * intros rd_gidx' rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. apply cur_running in running; try assumption. srewrite; contra.
      * intros rd_gidx' rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        eapply running_not_new; eassumption.
      * intro rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply cur_running.
    + constructor; simpl; try assumption; autounfold in *.
      * intro rd_gidx'.
        repeat (destruct_zmap; simpl); try solve[intros; omega]. intros until data_gidx.
        intros. exploit table_prop; try eassumption. intros (Ha & Hb & Hc).
        destruct_zmap; simpl. srewrite. omega.
        destruct_zmap; simpl. srewrite. omega.
        apply mem_rel; assumption.
      * intros rd_gidx' rec_gidx. autounfold.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_not_run_rel.
      * intros until rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_running_rel.
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
Qed.

Lemma smc_rtt_destroy_security:
  forall habd habd' labd rtt_addr rd_addr map_addr level ret
    (Hspec: smc_rtt_destroy_spec rtt_addr rd_addr map_addr level habd = Some (habd', ret))
    (Hrel: relate_adt habd labd) (rmm_run: cur_rec (priv habd) = None),
  exists labd', smc_rtt_destroy_spec rtt_addr rd_addr map_addr level labd = Some (labd', ret) /\ relate_adt habd' labd'.
Proof.
  Local Opaque ptr_eq peq fill_table.
  intros. destruct Hrel.
  unfold smc_rtt_destroy_spec in *. repeat autounfold in *.
  simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
  simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
  simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
  exploit (query_oracle_security habd r labd C13); try assumption.
  clear id_share rel_secure invs.
  intros (ld & Hld & Hrel0). rewrite Hld.
  destruct Hrel0 as (id_share & invs & rel_secure).
  simpl_query_oracle' C13. simpl_query_oracle' Hld.
  repeat (rewrite_sec_rel; simpl_hyp Hspec; simpl in * ); extract_prop_dec; inv Hspec;
    repeat (grewrite; try simpl_htarget; simpl);
    repeat (rewrite (relate_share_g_data _ _ id_share); [|autounfold; bool_rel; grewrite; omega]);
    repeat (grewrite; try simpl_htarget; simpl).
  - eapply destroy_table_secure; try eassumption.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - eapply destroy_table_secure; try eassumption.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - eapply destroy_table_secure; try eassumption.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - inv Hspec. eexists; split. reflexivity. constructor; assumption.
Qed.


Lemma smc_data_create_security:
  forall habd habd' labd data_addr rd_addr map_addr src_addr ret
    (Hspec: smc_data_create_spec data_addr rd_addr map_addr src_addr habd = Some (habd', ret))
    (Hrel: relate_adt habd labd) (rmm_run: cur_rec (priv habd) = None),
  exists labd', smc_data_create_spec data_addr rd_addr map_addr src_addr labd = Some (labd', ret) /\ relate_adt habd' labd'.
Proof.
  intros. destruct Hrel.
  unfold smc_data_create_spec in *. repeat autounfold in *.
  simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
  simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
  simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
  exploit (query_oracle_security habd r labd C13); try assumption.
  clear id_share rel_secure invs.
  intros (ld & Hld & Hrel0). rewrite Hld.
  destruct Hrel0 as (id_share & invs & rel_secure).
  simpl_query_oracle' C13. simpl_query_oracle' Hld.
  repeat (rewrite_sec_rel; simpl_hyp Hspec; simpl in * ); extract_prop_dec; inv Hspec;
    repeat (grewrite; try simpl_htarget; simpl).
  - repeat (rewrite (relate_share_g_data _ _ id_share); [|autounfold; bool_rel; grewrite; omega]).
    repeat (grewrite; try simpl_htarget; simpl). bool_rel_all.
    match type of C24 with | gtype _ @ ?gidx = _ => remember gidx as root_gidx end.
    match type of C30 with | gtype _ @ ?gidx = _ => remember gidx as lv1_gidx end.
    match type of C36 with | gtype _ @ ?gidx = _ => remember gidx as lv2_gidx end.
    match type of C42 with | gtype _ @ ?gidx = _ => remember gidx as lv3_gidx end.
    eexists; split. rewrite (relate_share_rtts _ _ id_share). simpl_htarget. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity. assumption.
      destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity.
      grewrite. autounfold; omega.
      destruct id_share; auto.
    + simpl; constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption; autounfold in *.
      * intro gidx.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        auto.
      * intro rd_gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl.
        intros. pose proof (rec_rd rd_gidx). apply H0 in H. srewrite. omega.
        destruct_zmap; simpl.
        intros. pose proof (rec_rd rd_gidx). apply H0 in H. srewrite. omega.
        auto.
      * intro rd_gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega.
        intros until b. destruct_zmap; simpl.
        destruct_if. intros. inversion H0. srewrite. omega.
        apply table_prop. assumption.
        destruct_zmap; simpl.
        destruct_if. intros. bool_rel_all. auto. intros. auto.
        exploit (table_prop rd_gidx); try eassumption.
        grewrite. intros (? & ? & ?). omega.
        destruct_if. intros. inversion H0. omega.
        apply table_prop. assumption.
      * intros rd_gidx rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. apply cur_running in running; try assumption. srewrite; contra.
      * intros rd_gidx rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        eapply running_not_new; eassumption.
      * intro rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply cur_running.
    + constructor; simpl; try assumption; autounfold in *.
      * intro rd_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega]. intros until data_gidx.
        destruct_if. intros. inv Hwalk. intros.
        exploit table_prop; try eassumption. intros (Ha & Hb & Hc).
        destruct_zmap; simpl. srewrite. omega.
        destruct_zmap; simpl. srewrite. omega.
        apply mem_rel; assumption.
      * intros rd_gidx rec_gidx. autounfold.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_not_run_rel.
      * intros until rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_running_rel.
  - repeat (rewrite (relate_share_g_data _ _ id_share); [|autounfold; bool_rel; grewrite; omega]).
    repeat (grewrite; try simpl_htarget; simpl). bool_rel_all.
    eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption; autounfold in *.
    + constructor; simpl; try assumption.
Qed.

Lemma smc_data_destroy_security:
  forall habd habd' labd rd_addr map_addr ret
    (Hspec: smc_data_destroy_spec rd_addr map_addr habd = Some (habd', ret))
    (Hrel: relate_adt habd labd) (rmm_run: cur_rec (priv habd) = None),
  exists labd', smc_data_destroy_spec rd_addr map_addr labd = Some (labd', ret) /\ relate_adt habd' labd'.
Proof.
  intros. destruct Hrel.
  unfold smc_data_destroy_spec in *. repeat autounfold in *.
  simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
  simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
  exploit (query_oracle_security habd r labd C6); try assumption.
  clear id_share rel_secure invs.
  intros (ld & Hld & Hrel0). rewrite Hld.
  destruct Hrel0 as (id_share & invs & rel_secure).
  simpl_query_oracle' C6. simpl_query_oracle' Hld.
  repeat (rewrite_sec_rel; simpl_hyp Hspec; simpl in * ); extract_prop_dec; inv Hspec;
    repeat (grewrite; try simpl_htarget; simpl).
  - repeat (rewrite (relate_share_g_data _ _ id_share); [|autounfold; bool_rel; grewrite; omega]).
    repeat (grewrite; try simpl_htarget; simpl). bool_rel_all.
    match type of C16 with | gtype _ @ ?gidx = _ => remember gidx as root_gidx end.
    match type of C22 with | gtype _ @ ?gidx = _ => remember gidx as lv1_gidx end.
    match type of C28 with | gtype _ @ ?gidx = _ => remember gidx as lv2_gidx end.
    match type of C34 with | gtype _ @ ?gidx = _ => remember gidx as lv3_gidx end.
    match type of C39 with | gtype _ @ ?gidx = _ => remember gidx as data_gidx end.
    eexists; split. rewrite (relate_share_rtts _ _ id_share). simpl_htarget. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity. assumption.
      destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      destruct id_share; auto.
    + simpl; constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption; autounfold in *.
      * intro gidx.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        auto.
      * intro rd_gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl.
        intros. pose proof (rec_rd rd_gidx). apply H0 in H. srewrite. omega.
        destruct_zmap; simpl.
        intros. pose proof (rec_rd rd_gidx). apply H0 in H. srewrite. omega.
        auto.
      * intro rd_gidx. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl. intros; omega.
        intros until b. destruct_zmap; simpl.
        destruct_if. intros. inversion H0. omega.
        apply table_prop. assumption.
        destruct_zmap; simpl.
        destruct_if. intros. inversion H0. rewrite <- H3 in H1. inv H1.
        intros. exploit (table_prop rd_gidx); try eassumption.
        intros (? & ? & ?).
        exploit (table_prop  (__addr_to_gidx z)); try eassumption.
        intros (Ha' & Hb' & Hc'). repeat srewrite. simpl_bool_eq. inv Case.
        destruct_if. intros. inversion H0. rewrite <- H3 in H1. inv H1.
        apply table_prop. assumption.
      * intros rd_gidx rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. apply cur_running in running; try assumption. srewrite; contra.
      * intros rd_gidx rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        eapply running_not_new; eassumption.
      * intro rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply cur_running.
    + constructor; simpl; try assumption; autounfold in *.
      * intro rd_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega]. intros until data_gidx0.
        destruct_if. intros. inv Hwalk. intros.
        exploit table_prop; try eassumption. intros (Ha & Hb & Hc).
        destruct_zmap; simpl. srewrite. omega.
        destruct_zmap; simpl. rewrite Heq2 in *.
        exploit (table_prop  (__addr_to_gidx z)); try eassumption.
        intros (Ha' & Hb' & Hc'). repeat srewrite. simpl_bool_eq. inv Case.
        apply mem_rel; assumption.
      * intros rd_gidx rec_gidx. autounfold.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_not_run_rel.
      * intros until rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_running_rel.
  - repeat (rewrite (relate_share_g_data _ _ id_share); [|autounfold; bool_rel; grewrite; omega]).
    repeat (grewrite; try simpl_htarget; simpl). bool_rel_all.
    eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
Qed.

Lemma map_table_secure:
  forall habd habd' labd llt_gidx idx level ret
    (Hspec: map_table llt_gidx idx level habd = Some (habd', ret))
    (Hrel: relate_adt habd labd) (rmm_run: cur_rec (priv habd) = None),
  exists labd', map_table llt_gidx idx level labd = Some (labd', ret) /\ relate_adt habd' labd'.
Proof.
  Local Opaque ptr_eq peq.
  intros. destruct Hrel.
  unfold map_table in *. repeat autounfold in *. simpl in *.
  repeat (rewrite_sec_rel; simpl_hyp Hspec; simpl in * ); extract_prop_dec; inv Hspec;
    repeat (rewrite (relate_share_g_data _ _ id_share); [|autounfold; bool_rel; grewrite; omega]);
    repeat (grewrite; try simpl_htarget; simpl).
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity. assumption.
      destruct id_share; auto.
    + constructor; simpl; try assumption; autounfold in *.
      * intro gidx.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        auto.
      * intro rd_gidx'. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl.
        intros. pose proof (rec_rd rd_gidx'). apply H0 in H. srewrite. omega.
        auto.
      * intro rd_gidx'. destruct_zmap; simpl. intros; omega.
        intros until b. destruct_zmap; simpl.
        apply table_prop. assumption.
        apply table_prop. assumption.
      * intros rd_gidx' rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. apply cur_running in running; try assumption. srewrite; contra.
      * intros rd_gidx' rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        eapply running_not_new; eassumption.
      * intro rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply cur_running.
    + constructor; simpl; try assumption; autounfold in *.
      * intro rd_gidx'.
        repeat (destruct_zmap; simpl); try solve[intros; omega]. intros until data_gidx.
        intros. exploit table_prop; try eassumption. intros (Ha & Hb & Hc).
        destruct_zmap; simpl. srewrite. omega.
        apply mem_rel; assumption.
      * intros rd_gidx' rec_gidx. autounfold.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_not_run_rel.
      * intros until rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_running_rel.
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
Qed.

Lemma smc_rtt_map_security:
  forall habd habd' labd rd_addr map_addr level ret
    (Hspec: smc_rtt_map_spec rd_addr map_addr level habd = Some (habd', ret))
    (Hrel: relate_adt habd labd) (rmm_run: cur_rec (priv habd) = None),
  exists labd', smc_rtt_map_spec rd_addr map_addr level labd = Some (labd', ret) /\ relate_adt habd' labd'.
Proof.
  Local Opaque ptr_eq peq.
  intros. destruct Hrel.
  unfold smc_rtt_map_spec in *. repeat autounfold in *.
  simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
  simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
  exploit (query_oracle_security habd r labd C8); try assumption.
  clear id_share rel_secure invs.
  intros (ld & Hld & Hrel0). rewrite Hld.
  destruct Hrel0 as (id_share & invs & rel_secure).
  simpl_query_oracle' C8. simpl_query_oracle' Hld.
  repeat (rewrite_sec_rel; simpl_hyp Hspec; simpl in * ); extract_prop_dec; inv Hspec;
    repeat (grewrite; try simpl_htarget; simpl);
    repeat (rewrite (relate_share_g_data _ _ id_share); [|autounfold; bool_rel; grewrite; omega]);
    repeat (grewrite; try simpl_htarget; simpl).
  - eapply map_table_secure; try eassumption.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - eapply map_table_secure; try eassumption.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - inv Hspec. eexists; split. reflexivity. constructor; assumption.
Qed.

Lemma unmap_table_secure:
  forall habd habd' labd llt_gidx idx level map_addr ret
    (Hspec: unmap_table llt_gidx idx level map_addr habd = Some (habd', ret))
    (Hrel: relate_adt habd labd) (rmm_run: cur_rec (priv habd) = None),
  exists labd', unmap_table llt_gidx idx level map_addr labd = Some (labd', ret) /\ relate_adt habd' labd'.
Proof.
  Local Opaque ptr_eq peq.
  intros. destruct Hrel.
  unfold unmap_table in *. repeat autounfold in *. simpl in *.
  repeat (rewrite_sec_rel; simpl_hyp Hspec; simpl in * ); extract_prop_dec; inv Hspec;
    repeat (rewrite (relate_share_g_data _ _ id_share); [|autounfold; bool_rel; grewrite; omega]);
    repeat (grewrite; try simpl_htarget; simpl).
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      rewrite (relate_share_tlbs _ _ id_share). reflexivity.
      intros. destruct_zmap; simpl.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      intros. rewrite (relate_share_g_regs _ _ id_share). reflexivity. assumption.
      destruct id_share; auto.
    + constructor; simpl; try assumption; autounfold in *.
      * intro gidx.
        destruct_zmap; simpl. intros. apply gpt_false_ns in H. srewrite. omega.
        auto.
      * intro rd_gidx'. destruct_zmap; simpl. intros; omega.
        destruct_zmap; simpl.
        intros. pose proof (rec_rd rd_gidx'). apply H0 in H. srewrite. omega.
        auto.
      * intro rd_gidx'. destruct_zmap; simpl. intros; omega.
        intros until b. destruct_zmap; simpl.
        apply table_prop. assumption.
        apply table_prop. assumption.
      * intros rd_gidx' rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        intros. apply cur_running in running; try assumption. srewrite; contra.
      * intros rd_gidx' rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        eapply running_not_new; eassumption.
      * intro rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply cur_running.
    + constructor; simpl; try assumption; autounfold in *.
      * intro rd_gidx'.
        repeat (destruct_zmap; simpl); try solve[intros; omega]. intros until data_gidx.
        intros. exploit table_prop; try eassumption. intros (Ha & Hb & Hc).
        destruct_zmap; simpl. srewrite. omega.
        apply mem_rel; assumption.
      * intros rd_gidx' rec_gidx. autounfold.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_not_run_rel.
      * intros until rec_gidx.
        repeat (destruct_zmap; simpl); try solve[intros; omega].
        apply reg_running_rel.
  - eexists; split. reflexivity.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
Qed.

Lemma smc_rtt_unmap_security:
  forall habd habd' labd rd_addr map_addr level ret
    (Hspec: smc_rtt_unmap_spec rd_addr map_addr level habd = Some (habd', ret))
    (Hrel: relate_adt habd labd) (rmm_run: cur_rec (priv habd) = None),
  exists labd', smc_rtt_unmap_spec rd_addr map_addr level labd = Some (labd', ret) /\ relate_adt habd' labd'.
Proof.
  Local Opaque ptr_eq peq.
  intros. destruct Hrel.
  unfold smc_rtt_unmap_spec in *. repeat autounfold in *.
  simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
  simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec. simpl_hyp Hspec.
  simpl_hyp Hspec.
  exploit (query_oracle_security habd r labd C9); try assumption.
  clear id_share rel_secure invs.
  intros (ld & Hld & Hrel0). rewrite Hld.
  destruct Hrel0 as (id_share & invs & rel_secure).
  simpl_query_oracle' C9. simpl_query_oracle' Hld.
  repeat (rewrite_sec_rel; simpl_hyp Hspec; simpl in * ); extract_prop_dec; inv Hspec;
    repeat (grewrite; try simpl_htarget; simpl);
    repeat (rewrite (relate_share_g_data _ _ id_share); [|autounfold; bool_rel; grewrite; omega]);
    repeat (grewrite; try simpl_htarget; simpl).
  - eapply unmap_table_secure; try eassumption.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - eapply unmap_table_secure; try eassumption.
    duplicate invs. destruct D. duplicate rel_secure. destruct D. simpl in *.
    constructor; simpl in *; try assumption.
    + constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
    + constructor; simpl; try assumption.
    + constructor; simpl; try assumption.
  - inv Hspec. eexists; split. reflexivity. constructor; assumption.
Qed.
