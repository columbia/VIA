Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Smallstep.
Require Import Events.
Require Import Globalenvs.
Require Import Memory.
Require Import Values.
Require Import Constants.
Require Import RData.
Require Import Asm.
Require Import AsmCode.
Require Import CommonLib.
Require Import RefTactics.
Require Import Assembly.Asm.
Require Import Assembly.AsmCode.
Require Import Assembly.AsmSpec.
Require Import Assembly.AsmProof.
Require Import RefTactics.

Lemma el3_sync_lel_code_proof:
  forall d d' (Hspec: el3_sync_lel_spec d = Some d'),
    StarStep d (d' {priv: (priv d') {cpu_regs: (cpu_regs (priv d')) {r_x30: -1}}
                                    {asm_regs: (asm_regs (priv d')) {a_PC: (-1, -1)} {a_CZ: None}}}).
Proof.
  intros. unfold el3_sync_lel_spec in *.
  autounfold in *.
  hsimpl_hyp Hspec; inv Hspec;
    extract_prop_dec; repeat destruct_con; bool_rel; simpl in *.
  - asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_prep_one_internal_step el3_sync_lel_function.
    simpl. autounfold. simpl. repeat (grewrite; simpl).
    repeat simpl_update_reg; repeat simpl_field; repeat swap_fields; repeat simpl_field. simpl_htarget; try reflexivity.
    asm_prep_one_internal_step el3_sync_lel_function.
    simpl. autounfold. simpl. repeat (grewrite; simpl).
    repeat simpl_update_reg; repeat simpl_field; repeat swap_fields; repeat simpl_field. simpl_htarget; try reflexivity.
    asm_prep_one_internal_step el3_sync_lel_function.
    simpl. autounfold. simpl. repeat (grewrite; simpl).
    repeat simpl_update_reg; repeat simpl_field; repeat swap_fields; repeat simpl_field. simpl_htarget; try reflexivity.
    replace (a_SP (asm_regs (priv d')) + -16 + -16 + -16 + 16 + 16 + 16) with (a_SP (asm_regs (priv d'))) by omega.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    eapply OneStep. eapply exec_step_external.
    reflexivity. eapply handle_std_service_function.
    reflexivity.
    repeat (autounfold; grewrite; simpl).
    repeat simpl_update_reg; repeat simpl_field; repeat swap_fields; repeat simpl_field. simpl.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    replace (a_SP (asm_regs (priv d')) +  -16 + -16 + 16 + 16) with (a_SP (asm_regs (priv d'))) by omega.
    eapply NoStep.
  - asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    eapply realm_save_el2_state; try reflexivity. simpl.
    repeat simpl_update_reg; repeat simpl_field; repeat swap_fields; repeat simpl_field. simpl.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    eapply ns_restore_el2_state; try reflexivity. simpl. repeat autounfold.
    repeat simpl_update_reg; repeat simpl_field; repeat swap_fields; repeat simpl_field. simpl.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_prep_one_internal_step el3_sync_lel_function.
    simpl. unfold mem_load. simpl. unfold get_stack. simpl. repeat (grewrite; simpl).
    unfold shrink_stack. repeat (grewrite; simpl). unfold set_sp, get_sp; simpl.
    grewrite. unfold set_creg. simpl. repeat simpl_field. autounfold.
    repeat (grewrite; simpl).
    repeat simpl_update_reg; repeat simpl_field; repeat swap_fields; repeat simpl_field. reflexivity.
    asm_prep_one_internal_step el3_sync_lel_function.
    simpl. unfold mem_load. simpl. unfold get_stack. simpl. repeat (grewrite; simpl).
    unfold shrink_stack. repeat (grewrite; simpl). unfold set_sp, get_sp; simpl.
    grewrite. unfold set_creg. simpl. repeat simpl_field. autounfold.
    repeat (grewrite; simpl).
    repeat simpl_update_reg; repeat simpl_field; repeat swap_fields; repeat simpl_field. reflexivity.
    asm_prep_one_internal_step el3_sync_lel_function.
    simpl. unfold mem_load. simpl. unfold get_stack. simpl. repeat (grewrite; simpl).
    unfold shrink_stack. repeat (grewrite; simpl). unfold set_sp, get_sp; simpl.
    grewrite. unfold set_creg. simpl. repeat simpl_field. autounfold.
    repeat (grewrite; simpl).
    repeat simpl_update_reg; repeat simpl_field; repeat swap_fields; repeat simpl_field. reflexivity.
    asm_one_internal_step el3_sync_lel_function.
    replace (a_SP (asm_regs (priv d)) + -16 + -16 + -16 + 16 + 16 + 16) with (a_SP (asm_regs (priv d))) by omega.
    simpl.
    eapply NoStep.
  - asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    eapply ns_save_el2_state; try reflexivity. simpl.
    repeat simpl_update_reg; repeat simpl_field; repeat swap_fields; repeat simpl_field. simpl.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    eapply realm_restore_el2_state; try reflexivity. simpl. repeat autounfold.
    repeat simpl_update_reg; repeat simpl_field; repeat swap_fields; repeat simpl_field. simpl.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_one_internal_step el3_sync_lel_function.
    asm_prep_one_internal_step el3_sync_lel_function.
    simpl. unfold mem_load. simpl. unfold get_stack. simpl. repeat (grewrite; simpl).
    unfold shrink_stack. repeat (grewrite; simpl). unfold set_sp, get_sp; simpl.
    grewrite. unfold set_creg. simpl. repeat simpl_field. autounfold.
    repeat (grewrite; simpl).
    repeat simpl_update_reg; repeat simpl_field; repeat swap_fields; repeat simpl_field. reflexivity.
    asm_prep_one_internal_step el3_sync_lel_function.
    simpl. unfold mem_load. simpl. unfold get_stack. simpl. repeat (grewrite; simpl).
    unfold shrink_stack. repeat (grewrite; simpl). unfold set_sp, get_sp; simpl.
    grewrite. unfold set_creg. simpl. repeat simpl_field. autounfold.
    repeat (grewrite; simpl).
    repeat simpl_update_reg; repeat simpl_field; repeat swap_fields; repeat simpl_field. reflexivity.
    asm_prep_one_internal_step el3_sync_lel_function.
    simpl. unfold mem_load. simpl. unfold get_stack. simpl. repeat (grewrite; simpl).
    unfold shrink_stack. repeat (grewrite; simpl). unfold set_sp, get_sp; simpl.
    grewrite. unfold set_creg. simpl. repeat simpl_field. autounfold.
    repeat (grewrite; simpl).
    repeat simpl_update_reg; repeat simpl_field; repeat swap_fields; repeat simpl_field. reflexivity.
    asm_one_internal_step el3_sync_lel_function.
    replace (a_SP (asm_regs (priv d)) + -16 + -16 + -16 + 16 + 16 + 16) with (a_SP (asm_regs (priv d))) by omega.
    eapply NoStep.
 Qed.
