Require Import SpecDeps.
Require Import RData.
Require Import EventReplay.
Require Import MoverTypes.
Require Import Constants.
Require Import CommonLib.
Require Import AbsAccessor.Spec.
Require Import Security.SecureMachine.
Require Import RefTactics.
Require Import Security.RefRel.
Require Import RMMHandler.Specs.realm_ns_step.

Local Open Scope Z.

Theorem realm_ns_step_security:
  forall habd habd' labd val
    (Hspec: secure_user_step_spec habd = Some (habd', VZ64 val))
    (Hrel: relate_adt habd labd) (Hlog: log labd = log habd),
  exists labd', user_step_spec labd = Some (labd', VZ64 val) /\ relate_adt habd' labd'.
Proof.
  Local Opaque ptr_eq peq.
  intros. inversion Hrel.
  unfold secure_user_step_spec, user_step_spec in *.
  repeat autounfold in *; simpl in *.
  repeat simpl_hyp Hspec; inv Hspec; repeat (rewrite_sec_rel; grewrite).
  - (* realm access mem *)
    unfold repl_realm_access_mem; repeat autounfold.
    hsimpl_func C5;
      repeat (rewrite_sec_rel; grewrite);
      rewrite (relate_share_tlbs _ _ id_share), (relate_share_rtts _ _ id_share); grewrite.
    + (* no mapping *)
      eexists; split. reflexivity.
      constructor; simpl; try assumption; try reflexivity.
      destruct invs. constructor; simpl; try assumption.
      destruct rel_secure. constructor; simpl; try assumption.
    + (* has mapping *)
      assert(Hrd_type: gtype (gs (share habd)) @ rd_gidx = 2).
      destruct invs. bool_rel. rewrite <- C11. apply rec_rd. autounfold. assumption.
      destruct_if.
      * (* tlb miss *)
        destruct (rtts (share habd) rd_gidx (__addr_to_gidx addr)) eqn:Hwalk.
        destruct_if' C13; [| inv C13].
        duplicate rel_secure. destruct D. duplicate invs. destruct D.
        simpl in *. autounfold in *. bool_rel.
        exploit mem_rel; try eapply Hwalk; try eassumption.
        destruct ((sec_mem (realms (share habd)) @ rd_gidx) @ addr) eqn:Hdecl.
        { (* sec has data *)
          intro T. rewrite T. eexists; split. reflexivity.
          constructor; simpl; try assumption; try reflexivity.
          constructor; simpl; rewrite_sec_rel; try reflexivity.
          exploit table_prop; try eapply Hwalk; try eassumption. intros (Ha & Hb).
          intros. destruct_zmap; simpl. constructor; simpl; rewrite_sec_rel; try reflexivity.
          intros. autounfold in *. srewrite. contra. intros.
          symmetry. apply relate_share_g_regs; assumption.
          constructor; simpl; rewrite_sec_rel; try reflexivity.
          intros. symmetry. apply relate_share_g_data; assumption.
          intros. symmetry. apply relate_share_g_regs; assumption.
          constructor; simpl; autounfold; try assumption.
          { constructor; simpl; autounfold; try assumption.
            - intros. pose proof (mem_rel rd_gidx0 is_rd vaddr data_gidx Hwalk0 Hdata) as Hmem.
              destruct_zmap. simpl. destruct_zmap. srewrite. inv Hwalk.
              repeat (simpl_htarget; simpl). reflexivity.
              destruct_zmap; simpl. destruct_zmap.
              assert(__addr_to_gidx vaddr = __addr_to_gidx addr).
              exploit (table_prop rd_gidx); try eassumption. intros (Ha & Hb & Hc).
              exploit (table_prop rd_gidx0); try eassumption. intros (Ha' & Hb' & Hc').
              srewrite. srewrite. reflexivity.
              assert(vaddr = addr). apply addr_eq_gidx_offs. split; assumption. contra.
              srewrite. assumption. srewrite. assumption.
              rewrite ZMap.gso. assumption. red; intro R; rewrite R in *.
              exploit (table_prop rd_gidx); try eassumption. intros (Ha & Hb & Hc).
              exploit (table_prop rd_gidx0); try eassumption. intros (Ha' & Hb' & Hc').
              srewrite. contra.
            - intros. exploit (reg_not_run_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
              intros. repeat (destruct_zmap; simpl); srewrite; assumption.
            - intros. exploit (reg_running_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
              intros. repeat (destruct_zmap; simpl); srewrite; assumption.
          }
        }
        { (* sec doesn't have data *)
          intro T. rewrite T. eexists; split. reflexivity.
          constructor; simpl; try assumption; try reflexivity.
          constructor; simpl; rewrite_sec_rel; try reflexivity.
          exploit table_prop; try eapply Hwalk; try eassumption. intros (Ha & Hb).
          intros. destruct_zmap; simpl. constructor; simpl; rewrite_sec_rel; try reflexivity.
          intros. autounfold in *. srewrite. contra. intros.
          symmetry. apply relate_share_g_regs; assumption.
          constructor; simpl; rewrite_sec_rel; try reflexivity.
          intros. symmetry. apply relate_share_g_data; assumption.
          intros. symmetry. apply relate_share_g_regs; assumption.
          constructor; simpl; autounfold; try assumption.
          { constructor; simpl; autounfold; try assumption.
            - intros. pose proof (mem_rel rd_gidx0 is_rd vaddr data_gidx Hwalk0 Hdata) as Hmem.
              destruct_zmap. simpl. destruct_zmap. srewrite. inv Hwalk.
              repeat (simpl_htarget; simpl). reflexivity.
              destruct_zmap; simpl. destruct_zmap.
              assert(__addr_to_gidx vaddr = __addr_to_gidx addr).
              exploit (table_prop rd_gidx); try eassumption. intros (Ha & Hb & Hc).
              exploit (table_prop rd_gidx0); try eassumption. intros (Ha' & Hb' & Hc').
              srewrite. srewrite. reflexivity.
              assert(vaddr = addr). apply addr_eq_gidx_offs. split; assumption. contra.
              srewrite. assumption. srewrite. assumption.
              rewrite ZMap.gso. assumption. red; intro R; rewrite R in *.
              exploit (table_prop rd_gidx); try eassumption. intros (Ha & Hb & Hc).
              exploit (table_prop rd_gidx0); try eassumption. intros (Ha' & Hb' & Hc').
              srewrite. contra.
            - intros. exploit (reg_not_run_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
              intros. repeat (destruct_zmap; simpl); srewrite; assumption.
            - intros. exploit (reg_running_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
              intros. repeat (destruct_zmap; simpl); srewrite; assumption.
          }
        }
      * (* tlb hit *)
        duplicate rel_secure. destruct D. duplicate invs. destruct D.
        simpl in *. autounfold in *. bool_rel.
        exploit tlb_prop; try eassumption. extract_prop_dec. assumption. reflexivity.
        intros Hwalk.
        exploit mem_rel; try eapply Hwalk; try eassumption.
        destruct ((sec_mem (realms (share habd)) @ rd_gidx) @ addr) eqn:Hdecl.
        { (* sec has data *)
          intro T. rewrite T. eexists; split. reflexivity.
          constructor; simpl; try assumption; try reflexivity.
          constructor; simpl; rewrite_sec_rel; try reflexivity.
          exploit table_prop; try eapply Hwalk; try eassumption. intros (Ha & Hb).
          intros. destruct_zmap; simpl. constructor; simpl; rewrite_sec_rel; try reflexivity.
          intros. autounfold in *. srewrite. contra. intros.
          symmetry. apply relate_share_g_regs; assumption.
          constructor; simpl; rewrite_sec_rel; try reflexivity.
          intros. symmetry. apply relate_share_g_data; assumption.
          intros. symmetry. apply relate_share_g_regs; assumption.
          constructor; simpl; autounfold; try assumption.
          { constructor; simpl; autounfold; try assumption.
            - intros. pose proof (mem_rel rd_gidx0 is_rd vaddr data_gidx Hwalk0 Hdata) as Hmem.
              destruct_zmap. simpl. destruct_zmap. srewrite. inv Hwalk.
              repeat (simpl_htarget; simpl). reflexivity.
              destruct_zmap; simpl. destruct_zmap.
              assert(__addr_to_gidx vaddr = __addr_to_gidx addr).
              exploit (table_prop rd_gidx); try eassumption. intros (Ha & Hb & Hc).
              exploit (table_prop rd_gidx0); try eassumption. intros (Ha' & Hb' & Hc').
              srewrite. srewrite. reflexivity.
              assert(vaddr = addr). apply addr_eq_gidx_offs. split; assumption. contra.
              srewrite. assumption. srewrite. assumption.
              rewrite ZMap.gso. assumption. red; intro R; rewrite R in *.
              exploit (table_prop rd_gidx); try eassumption. intros (Ha & Hb & Hc).
              exploit (table_prop rd_gidx0); try eassumption. intros (Ha' & Hb' & Hc').
              srewrite. contra.
            - intros. exploit (reg_not_run_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
              intros. repeat (destruct_zmap; simpl); srewrite; assumption.
            - intros. exploit (reg_running_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
              intros. repeat (destruct_zmap; simpl); srewrite; assumption.
          }
        }
        { (* sec doesn't have data *)
          intro T. rewrite T. eexists; split. reflexivity.
          constructor; simpl; try assumption; try reflexivity.
          constructor; simpl; rewrite_sec_rel; try reflexivity.
          exploit table_prop; try eapply Hwalk; try eassumption. intros (Ha & Hb).
          intros. destruct_zmap; simpl. constructor; simpl; rewrite_sec_rel; try reflexivity.
          intros. autounfold in *. srewrite. contra. intros.
          symmetry. apply relate_share_g_regs; assumption.
          constructor; simpl; rewrite_sec_rel; try reflexivity.
          intros. symmetry. apply relate_share_g_data; assumption.
          intros. symmetry. apply relate_share_g_regs; assumption.
          constructor; simpl; autounfold; try assumption.
          { constructor; simpl; autounfold; try assumption.
            - intros. pose proof (mem_rel rd_gidx0 is_rd vaddr data_gidx Hwalk0 Hdata) as Hmem.
              destruct_zmap. simpl. destruct_zmap. srewrite. inv Hwalk.
              repeat (simpl_htarget; simpl). reflexivity.
              destruct_zmap; simpl. destruct_zmap.
              assert(__addr_to_gidx vaddr = __addr_to_gidx addr).
              exploit (table_prop rd_gidx); try eassumption. intros (Ha & Hb & Hc).
              exploit (table_prop rd_gidx0); try eassumption. intros (Ha' & Hb' & Hc').
              srewrite. srewrite. reflexivity.
              assert(vaddr = addr). apply addr_eq_gidx_offs. split; assumption. contra.
              srewrite. assumption. srewrite. assumption.
              rewrite ZMap.gso. assumption. red; intro R; rewrite R in *.
              exploit (table_prop rd_gidx); try eassumption. intros (Ha & Hb & Hc).
              exploit (table_prop rd_gidx0); try eassumption. intros (Ha' & Hb' & Hc').
              srewrite. contra.
            - intros. exploit (reg_not_run_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
              intros. repeat (destruct_zmap; simpl); srewrite; assumption.
            - intros. exploit (reg_running_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
              intros. repeat (destruct_zmap; simpl); srewrite; assumption.
          }
        }
  - (* realm access reg *)
    unfold access_reg; repeat autounfold.
     hsimpl_func C5;
      repeat (rewrite_sec_rel; grewrite); bool_rel; extract_prop_dec.
     duplicate rel_secure. destruct D. duplicate invs. destruct D.
     assert(Hrd_type: gtype (gs (share habd)) @ rd_gidx = 2).
     rewrite C1. apply rec_rd. autounfold. assumption.
     exploit (reg_running_rel rd_gidx rec_gidx); autounfold; srewrite; try eassumption; try reflexivity.
     instantiate(1:=reg).
     rewrite decl_gpregs; autounfold; try eassumption. simpl. intro R; rewrite R.
     eexists; split. reflexivity. constructor; simpl; try assumption.
     constructor; simpl; rewrite_sec_rel; try reflexivity.
     destruct id_share. assumption.
     constructor; simpl; rewrite_sec_rel; try reflexivity.
     apply set_gpregs_sys_eq_r. bool_rel_all. omega. destruct id_priv. assumption.
     { constructor; simpl; autounfold; try assumption.
       - srewrite. assumption.
     }
     { constructor; simpl in *; autounfold; try assumption.
       - intros. pose proof (mem_rel rd_gidx0 is_rd vaddr data_gidx Hwalk Hdata) as Hmem.
         destruct_zmap; simpl in *; srewrite; assumption.
       - intros. exploit (reg_not_run_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg0).
         intros. repeat (destruct_zmap; simpl in * ); repeat srewrite; try assumption. inv Prop0.
       - intros. exploit (reg_running_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg0).
         intros. repeat (destruct_zmap; simpl in * ); repeat srewrite; try assumption.
         destruct (zeq reg0 reg). grewrite. bool_rel_all. repeat rewrite get_set_reg_same; try omega. reflexivity.
         repeat rewrite get_set_reg_other; try assumption.
         exploit cur_running; try eapply running; autounfold; try assumption.
         intro T. inv T. contra. repeat srewrite.
         exploit cur_running; try eapply running; autounfold; try assumption.
         intro T; inversion T. srewrite. contra.
       - intros; srewrite. contra.
     }
     bool_rel_all; omega.
  - (* realm trap *)
    unfold realm_trap; repeat autounfold.
    duplicate rel_secure. destruct D. duplicate invs. destruct D.
    hsimpl_func C5; repeat (rewrite_sec_rel; grewrite); bool_rel; extract_prop_dec.
    + intros. eexists; split. reflexivity. constructor; simpl; try assumption.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; try assumption.
      constructor; simpl; try assumption.
    + intros. eexists; split. reflexivity.
      constructor; simpl; try assumption.
      constructor; simpl; rewrite_sec_rel; try reflexivity. destruct id_share; assumption.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl in *; autounfold; try assumption.
     { constructor; simpl in *; autounfold; try assumption.
       - intros. pose proof (mem_rel rd_gidx0 is_rd vaddr data_gidx Hwalk Hdata) as Hmem.
         destruct_zmap; simpl in *; srewrite; assumption.
       - intros. exploit (reg_not_run_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
         intros. repeat (destruct_zmap; simpl in * ); repeat srewrite; try assumption. inv Prop0.
       - intros. exploit (reg_running_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
         intros. repeat (destruct_zmap; simpl in * ); repeat srewrite; try assumption.
         autounfold in *. pose proof (decl_gpregs habd rd_gidx z is_rd is_rec is_rd_rec).
         srewrite. specialize_trivial H0. specialize (H0 reg).
         unfold get_reg in H, H0. unfold get_reg. autounfold in *.
         simpl. destruct (reg =? 0) eqn:Hreg. simpl. rewrite H0 in H. simpl in H. assumption. bool_rel; omega.
         destruct (reg =? 1) eqn:Hreg1. simpl. rewrite H0 in H. simpl in H. assumption. bool_rel; omega.
         destruct (reg =? 2) eqn:Hreg2. simpl. rewrite H0 in H. simpl in H. assumption. bool_rel; omega.
         destruct (reg =? 3) eqn:Hreg3. simpl. rewrite H0 in H. simpl in H. assumption. bool_rel; omega.
         destruct (reg =? 4) eqn:Hreg4. simpl. rewrite H0 in H. simpl in H. assumption. bool_rel; omega.
         destruct (reg =? 5) eqn:Hreg5. simpl. rewrite H0 in H. simpl in H. assumption. bool_rel; omega.
         destruct (reg =? 6) eqn:Hreg6. simpl. rewrite H0 in H. simpl in H. assumption. bool_rel; omega.
         destruct (reg =? 7) eqn:Hreg7. simpl. rewrite H0 in H. simpl in H. assumption. bool_rel; omega. assumption.
         exploit (cur_running rec_gidx0); try assumption. intro R; inv R. contra.
         exploit (cur_running rec_gidx0); try assumption. intro R; inv R. contra.
       - intros; srewrite; contra.
     }
    + intros. eexists; split. reflexivity. constructor; simpl; try assumption.
      constructor; simpl; rewrite_sec_rel; try reflexivity. destruct id_share; assumption.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; try assumption.
     { constructor; simpl in *; autounfold; try assumption.
       - intros. pose proof (mem_rel rd_gidx0 is_rd vaddr data_gidx Hwalk Hdata) as Hmem.
         destruct_zmap; simpl in *; srewrite; assumption.
       - intros. exploit (reg_not_run_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
         intros. repeat (destruct_zmap; simpl in * ); repeat srewrite; try assumption. inv Prop0.
       - intros. exploit (reg_running_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
         intros. repeat (destruct_zmap; simpl in * ); repeat srewrite; try assumption.
         autounfold in *. pose proof (decl_gpregs habd rd_gidx z is_rd is_rec is_rd_rec).
         srewrite. specialize_trivial H0. specialize (H0 reg).
         unfold get_reg in H, H0. unfold get_reg. autounfold in *.
         simpl. destruct (reg =? 0) eqn:Hreg. simpl. rewrite H0 in H. simpl in H. assumption. bool_rel; omega.
         destruct (reg =? 1) eqn:Hreg1. simpl. rewrite H0 in H. simpl in H. assumption. bool_rel; omega.
         destruct (reg =? 2) eqn:Hreg2. simpl. rewrite H0 in H. simpl in H. assumption. bool_rel; omega.
         destruct (reg =? 3) eqn:Hreg3. simpl. rewrite H0 in H. simpl in H. assumption. bool_rel; omega. assumption.
         exploit (cur_running rec_gidx0); try assumption. intro R; inv R. contra.
         exploit (cur_running rec_gidx0); try assumption. intro R; inv R. contra.
       - intros; srewrite; contra.
     }
    + intros. eexists; split. reflexivity. constructor; simpl; try assumption.
      constructor; simpl; rewrite_sec_rel; try reflexivity. destruct id_share; assumption.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      apply set_gpregs_sys_eq_l. apply ISS_RT_range. destruct id_priv. assumption.
      constructor; simpl; try assumption.
     { constructor; simpl in *; autounfold; try assumption.
       - intros. pose proof (mem_rel rd_gidx0 is_rd vaddr data_gidx Hwalk Hdata) as Hmem.
         destruct_zmap; simpl in *; srewrite; assumption.
       - intros. exploit (reg_not_run_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
         intros. repeat (destruct_zmap; simpl in * ); repeat srewrite; try assumption. inv Prop0.
       - intros. exploit (reg_running_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
         intros. repeat (destruct_zmap; simpl in * ); repeat srewrite; try assumption.
         autounfold in *. pose proof (decl_gpregs habd rd_gidx z is_rd is_rec is_rd_rec).
         srewrite. specialize_trivial H0. specialize (H0 reg).
         destruct (zeq reg (__ESR_EL2_SYSREG_ISS_RT (r_esr_el2 (cpu_regs (priv habd))))).
         subst. repeat rewrite get_set_reg_same; try apply ISS_RT_range. simpl.
         rewrite H0 in H. simpl in H. assumption. apply ISS_RT_range.
         pose proof (ISS_RT_range (r_esr_el2 (cpu_regs (priv habd)))). omega.
         pose proof (ISS_RT_range (r_esr_el2 (cpu_regs (priv habd)))). omega.
         repeat rewrite get_set_reg_other. assumption. assumption. assumption.
         exploit (cur_running rec_gidx0); try assumption. intro R; inv R. contra.
         exploit (cur_running rec_gidx0); try assumption. intro R; inv R. contra.
       - intros; srewrite; contra.
     }
    + intros. eexists; split. reflexivity. constructor; simpl; try assumption.
      constructor; simpl; rewrite_sec_rel; try reflexivity. destruct id_share; assumption.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      apply set_gpregs_sys_eq_l. apply ISS_RT_range. destruct id_priv. assumption.
      constructor; simpl; try assumption.
     { constructor; simpl in *; autounfold; try assumption.
       - intros. pose proof (mem_rel rd_gidx0 is_rd vaddr data_gidx Hwalk Hdata) as Hmem.
         destruct_zmap; simpl in *; srewrite; assumption.
       - intros. exploit (reg_not_run_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
         intros. repeat (destruct_zmap; simpl in * ); repeat srewrite; try assumption. inv Prop0.
       - intros. exploit (reg_running_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
         intros. repeat (destruct_zmap; simpl in * ); repeat srewrite; try assumption.
         autounfold in *. pose proof (decl_gpregs habd rd_gidx z is_rd is_rec is_rd_rec).
         srewrite. specialize_trivial H0. specialize (H0 reg).
         destruct (zeq reg (__ESR_EL2_SYSREG_ISS_RT (r_esr_el2 (cpu_regs (priv habd))))).
         subst. repeat rewrite get_set_reg_same; try apply ISS_RT_range. simpl.
         rewrite H0 in H. simpl in H. assumption. apply ISS_RT_range.
         pose proof (ISS_RT_range (r_esr_el2 (cpu_regs (priv habd)))). omega.
         pose proof (ISS_RT_range (r_esr_el2 (cpu_regs (priv habd)))). omega.
         repeat rewrite get_set_reg_other. assumption. assumption. assumption.
         exploit (cur_running rec_gidx0); try assumption. intro R; inv R. contra.
         exploit (cur_running rec_gidx0); try assumption. intro R; inv R. contra.
       - intros; srewrite; contra.
     }
    + intros. eexists; split. reflexivity. constructor; simpl; try assumption.
      constructor; simpl; rewrite_sec_rel; try reflexivity. destruct id_share; assumption.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      apply set_gpregs_sys_eq_l. apply ISS_RT_range. destruct id_priv. assumption.
      constructor; simpl; try assumption.
     { constructor; simpl in *; autounfold; try assumption.
       - intros. pose proof (mem_rel rd_gidx0 is_rd vaddr data_gidx Hwalk Hdata) as Hmem.
         destruct_zmap; simpl in *; srewrite; assumption.
       - intros. exploit (reg_not_run_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
         intros. repeat (destruct_zmap; simpl in * ); repeat srewrite; try assumption. inv Prop0.
       - intros. exploit (reg_running_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
         intros. repeat (destruct_zmap; simpl in * ); repeat srewrite; try assumption.
         autounfold in *. pose proof (decl_gpregs habd rd_gidx z is_rd is_rec is_rd_rec).
         srewrite. specialize_trivial H0. specialize (H0 reg).
         destruct (zeq reg (__ESR_EL2_SYSREG_ISS_RT (r_esr_el2 (cpu_regs (priv habd))))).
         subst. repeat rewrite get_set_reg_same; try apply ISS_RT_range. simpl.
         rewrite H0 in H. simpl in H. assumption. apply ISS_RT_range.
         pose proof (ISS_RT_range (r_esr_el2 (cpu_regs (priv habd)))). omega.
         pose proof (ISS_RT_range (r_esr_el2 (cpu_regs (priv habd)))). omega.
         repeat rewrite get_set_reg_other. assumption. assumption. assumption.
         exploit (cur_running rec_gidx0); try assumption. intro R; inv R. contra.
         exploit (cur_running rec_gidx0); try assumption. intro R; inv R. contra.
       - intros; srewrite; contra.
     }
    + intros. eexists; split. reflexivity. constructor; simpl; try assumption.
      constructor; simpl; rewrite_sec_rel; try reflexivity. destruct id_share; assumption.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      apply set_gpregs_sys_eq_l. apply esr_srt_range. destruct id_priv. assumption.
      constructor; simpl; try assumption.
     { constructor; simpl in *; autounfold; try assumption.
       - intros. pose proof (mem_rel rd_gidx0 is_rd vaddr data_gidx Hwalk Hdata) as Hmem.
         destruct_zmap; simpl in *; srewrite; assumption.
       - intros. exploit (reg_not_run_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
         intros. repeat (destruct_zmap; simpl in * ); repeat srewrite; try assumption. inv Prop0.
       - intros. exploit (reg_running_rel rd_gidx0 rec_gidx0); try eassumption. instantiate(1:=reg).
         intros. repeat (destruct_zmap; simpl in * ); repeat srewrite; try assumption.
         autounfold in *. pose proof (decl_gpregs habd rd_gidx z is_rd is_rec is_rd_rec).
         srewrite. specialize_trivial H0. specialize (H0 reg).
         destruct (zeq reg (__esr_srt (r_esr_el2 (cpu_regs (priv habd))))).
         subst. repeat rewrite get_set_reg_same; try apply esr_srt_range. simpl.
         rewrite H0 in H. simpl in H. assumption. apply esr_srt_range.
         pose proof (esr_srt_range (r_esr_el2 (cpu_regs (priv habd)))). omega.
         pose proof (esr_srt_range (r_esr_el2 (cpu_regs (priv habd)))). omega.
         repeat rewrite get_set_reg_other. assumption. assumption. assumption.
         exploit (cur_running rec_gidx0); try assumption. intro R; inv R. contra.
         exploit (cur_running rec_gidx0); try assumption. intro R; inv R. contra.
       - intros; srewrite; contra.
     }
    + intros. eexists; split. reflexivity. constructor; simpl; try assumption.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; try assumption.
      constructor; simpl; try assumption.
    + intros. eexists; split. reflexivity. constructor; simpl; try assumption.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; try assumption.
      constructor; simpl; try assumption.
    + intros. eexists; split. reflexivity. constructor; simpl; try assumption.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; rewrite_sec_rel; try reflexivity.
      constructor; simpl; try assumption.
      constructor; simpl; try assumption.
  - (* ns access mem *)
    duplicate rel_secure. destruct D. duplicate invs. destruct D.
    unfold repl_ns_access_mem in *. autounfold in *. rewrite_sec_rel.
    repeat simpl_hyp C2; inv C2.
    eexists; split. reflexivity. constructor; simpl; try assumption.
    constructor; simpl; try assumption.
    constructor; simpl; try assumption.
    pose proof (gpt_false_ns _ C5).
    erewrite relate_share_g_data; try eassumption.
    eexists; split. reflexivity. constructor; simpl; try assumption.
    constructor; simpl; rewrite_sec_rel; try reflexivity.
    intros. destruct_zmap.
    constructor; simpl; rewrite_sec_rel; try reflexivity.
    intros. symmetry. apply relate_share_g_regs. assumption. autounfold; omega.
    destruct id_share. apply id_granule.
    { constructor; simpl; try assumption.
      - intros. destruct_zmap; simpl; apply gpt_false_ns; srewrite; try reflexivity.
      - intro rd_gidx. destruct_zmap. simpl. intro R; srewrite; inv H.
        destruct_zmap. simpl. rewrite <- Heq0. apply rec_rd. apply rec_rd.
      - intro rd_gidx. destruct_zmap. simpl. intro R; srewrite; inv H.
        intros. destruct_zmap. srewrite. simpl. eapply table_prop; try eassumption.
        eapply table_prop; try eassumption.
      - intros rd_gidx rec_gidx. destruct_zmap. simpl. intro R; rewrite R in H; inv H.
        destruct_zmap. simpl. intros; srewrite; inv H. apply tlb_prop.
      - intros rd_gidx rec_gidx. destruct_zmap. simpl. intro R; srewrite; inv H.
        destruct_zmap. simpl. intros; srewrite; inv H. apply running_not_new.
       - intro rec_gidx. destruct_zmap. simpl. intro R; srewrite; inv H. apply cur_running.
    }
    { constructor; simpl; try assumption.
      - intro rd_gidx. destruct_zmap. simpl. intro R; srewrite. inv H.
        intros. autounfold in *. exploit (table_prop rd_gidx); try eassumption.
        intros (Ha & Hb & Hc). destruct_zmap. srewrite. inv H.
        apply mem_rel; try assumption.
       - intros rd_gidx rec_gidx. destruct_zmap; simpl. intro R; srewrite; inv H.
         destruct_zmap. simpl. intros. srewrite; inv H. apply reg_not_run_rel; assumption.
       - intros rd_gidx rec_gidx. destruct_zmap; simpl. intro R; srewrite; inv H.
         destruct_zmap. simpl. intros. srewrite; inv H. apply reg_running_rel; assumption.
    }
    autounfold; rewrite H. omega.
  - (* ns access reg *)
    duplicate rel_secure. destruct D. duplicate invs. destruct D.
    unfold access_reg in *. autounfold in *. rewrite_sec_rel.
    repeat simpl_hyp C2; inv C2. pose proof (regs_eq_not_realm C0). srewrite.
    eexists; split. reflexivity. constructor; simpl; try assumption.
    constructor; simpl; rewrite_sec_rel; try reflexivity.
    constructor; simpl; rewrite_sec_rel; try reflexivity.
    { constructor; simpl; try assumption.
      - intros. srewrite. apply cur_running; assumption.
    }
    { constructor; simpl; try assumption.
      - intros. srewrite. apply cur_running in running. inv running. assumption.
      - intros. reflexivity.
    }
  - (* ns trap *)
    duplicate rel_secure. destruct D. duplicate invs. destruct D.
    unfold ns_trap in *. autounfold in *; simpl_hyp C2; inv C2. extract_prop_dec.
    rewrite_sec_rel. simpl_htarget. eexists; split. reflexivity.
    constructor; simpl; try assumption.
    constructor; simpl; rewrite_sec_rel; try reflexivity.
    constructor; simpl; rewrite_sec_rel; try reflexivity.
    constructor; simpl; try assumption.
    constructor; simpl; try assumption.
Qed.
