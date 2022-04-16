(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*         Xavier Leroy, Collège de France and INRIA Paris             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Abstract syntax and semantics for AArch64 assembly language *)

Require Import Coqlib Maps.
Require Import AST.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Constants.
Require Import CommonLib.
Require Import RData.
Require Import EventReplay.
Require Import RefTactics.

(** The instruction set.  Most instructions correspond exactly to
  actual AArch64 instructions. See the ARM reference manuals for more
  details.  Some instructions, described below, are
  pseudo-instructions: they expand to canned instruction sequences
  during the printing of the assembly code.  *)

Definition label := Z.

Inductive testcond : Type :=
  | TCeq: testcond    (**r equal *)
  | TCne: testcond    (**r not equal *)
  | TChs: testcond    (**r unsigned higher or same *)
  | TClo: testcond    (**r unsigned lower *)
  | TCmi: testcond    (**r negative *)
  | TCpl: testcond    (**r positive *)
  | TChi: testcond    (**r unsigned higher *)
  | TCls: testcond    (**r unsigned lower or same *)
  | TCge: testcond    (**r signed greater or equal *)
  | TClt: testcond    (**r signed less than *)
  | TCgt: testcond    (**r signed greater *)
  | TCle: testcond.   (**r signed less than or equal *)

Definition ireg := Z.

Inductive addressing: Type :=
  | ADimm (base: ireg) (n: Z)                  (**r base plus immediate offset *)
  | ADreg (base: ireg) (r: ireg)                   (**r base plus reg *)
  | ADlsl (base: ireg) (r: ireg) (n: Z)          (**r base plus reg LSL n *)
  | ADpostincr (base: ireg) (n: Z).            (**r base plus offset; base is updated after *)

Inductive instruction: Type :=
  (** Branches *)
  | Pb (lbl: label)                                                   (**r branch *)
  | Pbc (c: testcond) (lbl: label)                                    (**r conditional branch *)
  | Pbl (id: Z) (sg: signature)                                   (**r jump to function and link *)
  | Pbs (id: Z) (sg: signature)                                   (**r jump to function *)
  | Pblr (r: ireg) (sg: signature)                                    (**r indirect jump and link *)
  | Pbr (r: ireg) (sg: signature)                                     (**r indirect jump *)
  | Pret (r: ireg)                                                    (**r return *)
  | Pcbnz (r: ireg) (lbl: label)                          (**r branch if not zero *)
  | Pcbz (r: ireg) (lbl: label)                           (**r branch if zero *)
  | Ptbnz (r: ireg) (n: Z) (lbl: label)                 (**r branch if bit n is not zero *)
  | Ptbz (r: ireg) (n: Z) (lbl: label)                  (**r branch if bit n is zero *)
  (* Register Insts *)
  | Paddimm (r1 r2: ireg) (imm: Z)  (* add x0, x0, #CPUSTATE_NS_OFFSET *)
  | Psubimm (r1 r2: ireg) (imm: Z)  (* sub sp, sp, #(16 * 6) *)
  | Pand (r1 r2 r3: ireg)  (* and x1, x0, #ESR_EC_SMC_IMM16 *)
  | Pandimm (r1 r2: ireg) (imm: Z)  (* ands x1, x0, #ESR_EC_SMC_IMM16 *)
  | Pcmp (r1 r2: ireg)     (* cmp x1, x2 *)
  | Pcmpimm (r: ireg) (n: Z)     (* cmp x1, #SCR_REALM_WORLD *)
  | Pbic (r1 r2: ireg) (imm: Z)    (* bic x1, x0, *)
  | Pldrimm (Xt: ireg) (imm: Z)  (* ldr x2 =SMC_STD_CALL_BASE *)
  | Pmov (r1 r2: ireg)  (* mrs x0 tpidr_el3 *)
  | Pmovimm (r: ireg) (n: Z)  (* mov x0 #0 *)
  | Pmrs (r1 r2: ireg)  (* mrs x0 tpidr_el3 *)
  | Pmsr (r1 r2: ireg) (* msr scr_el3, x1 *)
  (* Load/Store *)
  | Pldr (r: ireg) (ptr: ireg) (imm: Z)  (* ldr x18 [sp, #16] *)
  | Pldr' (r: ireg) (ptr: ireg) (imm: Z)  (* ldr x18 [sp], #16 *)
  | Pldp (r1 r2: ireg) (ptr: ireg) (imm: Z)  (* ldp x0, x1, [sp], #16 *)
  | Pldp' (r1 r2: ireg) (ptr: ireg) (imm: Z)  (* ldp x0, x1, [sp], #16 *)
  | Pstr (r: ireg) (ptr: ireg) (imm: Z)  (* str x18 [sp, #-16] *)
  | Pstr' (r: ireg) (ptr: ireg) (imm: Z)  (* str x18 [sp, #-16] *)
  | Pstp (r1 r2: ireg) (ptr: ireg) (imm: Z)  (* stp x29, lr, [sp, #-16] *)
  | Pstp' (r1 r2: ireg) (ptr: ireg) (imm: Z)  (* stp x29, lr, [sp, #-16]! *)
  (* Eret *)
  | Peret     (* eret *)
  (** Pseudo-instructions *)
  | Plabel (lbl: label)                                               (**r define a code label *)
  | Pstuck
.

Definition code := list instruction.
Record function : Type := mkfunction { fn_sig: signature; fn_code: code }.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain (but do not enforce)
  the convention that integer registers are mapped to values of
  type [Tint], float registers to values of type [Tfloat],
  and condition bits to either [Vzero] or [Vone]. *)

Definition genv := Genv.t fundef unit.

(** The value of an [ireg] is either the value of the integer register,
    or 0. *)

Definition XZR := -1.
Definition SP := -2.
Definition RA := x30.

Definition get_creg (r: ireg) (d: RData) := get_reg r (cpu_regs (priv d)).

Definition set_creg (r: ireg) (val: Z) (d: RData) := d {priv: (priv d) {cpu_regs: set_reg r val (cpu_regs (priv d))}}.

Definition get_pc d := a_PC (asm_regs (priv d)).

Definition set_pc v d := d {priv: (priv d) {asm_regs: (asm_regs (priv d)) {a_PC: v}}}.

Definition get_sp d :=
  if a_EL3 (asm_regs (priv d)) then
    a_SP (asm_regs (priv d))
  else
    r_sp_el2 (cpu_regs (priv d)).

Definition set_sp v d :=
  if a_EL3 (asm_regs (priv d)) then
    d {priv: (priv d) {asm_regs: (asm_regs (priv d)) {a_SP: v}}}
  else
    d {priv: (priv d) {cpu_regs: (cpu_regs (priv d)) {r_sp_el2: v}}}.

(** Undefining some registers *)

Definition Undef := -9999999999999999999999.
Definition base_mult := 100000000000000000000.

Fixpoint undef_regs (l: list ireg) (d: RData) : RData :=
  match l with
  | nil => d
  | r :: l' => undef_regs l' (set_creg r Undef d)
  end.

(** Undefining the condition codes *)

Definition undef_flags (d: RData) : RData :=
  d {priv: (priv d) {asm_regs: (asm_regs (priv d)) {a_CN: None} {a_CZ: None} {a_CC: None} {a_CV: None}}}.

(** Updating stacks *)

Definition push_stack v d :=
  if a_EL3 (asm_regs (priv d)) then
    d {priv: (priv d) {el3_stack: v :: (el3_stack (priv d))}}
  else
    d {priv: (priv d) {el2_stack: v :: (el2_stack (priv d))}}.

Definition pop_stack d :=
  if a_EL3 (asm_regs (priv d)) then
    match el3_stack (priv d) with
    | v :: stk' =>
      Some (d {priv: (priv d) {el3_stack: stk'}}, v)
    | _ => None
    end
  else
    match el2_stack (priv d) with
    | v :: stk' =>
      Some (d {priv: (priv d) {el2_stack: stk'}}, v)
    | _ => None
    end.

Fixpoint get_stack' (n: nat) (stk: list Z) :=
  match n, stk with
  | O, v :: stk' => Some v
  | O, _ => None
  | S n', v :: stk' => get_stack' n' stk'
  | S n', _ => None
  end.

Fixpoint set_stack' (n: nat) (val: Z) (stk: list Z) :=
  match n, stk with
  | O, v :: stk' => Some (val :: stk')
  | O, _ => None
  | S n', v :: stk' =>
    match set_stack' n' val stk' with
    | Some stk'' => Some (v :: stk'')
    | _ => None
    end
  | S n', _ => None
  end.

Definition get_stack (n: nat) (d: RData) :=
  if a_EL3 (asm_regs (priv d)) then
    get_stack' n (el3_stack (priv d))
  else
    get_stack' n (el2_stack (priv d)).

Definition set_stack (n: nat) (val: Z) (d: RData) :=
  if a_EL3 (asm_regs (priv d)) then
    match set_stack' n val (el3_stack (priv d)) with
    | Some stk' =>
      Some (d {priv: (priv d) {el3_stack: stk'}})
    | _ => None
    end
  else
    match set_stack' n val (el2_stack (priv d)) with
    | Some stk' =>
      Some (d {priv: (priv d) {el2_stack: stk'}})
    | _ => None
    end.

Fixpoint extend_stack' (n: nat) (stk: list Z) :=
  match n with
  | O => stk
  | S n' => Undef :: (extend_stack' n' stk)
  end.

Fixpoint shrink_stack' (n: nat) (stk: list Z) :=
  match n, stk with
  | O, stk => Some stk
  | S n', v :: stk' => shrink_stack' n' stk'
  | _, _ => None
  end.

Definition extend_stack (n: nat) (d: RData) :=
  if a_EL3 (asm_regs (priv d)) then
    Some (d {priv: (priv d) {el3_stack: extend_stack' n (el3_stack (priv d))}})
  else
    Some (d {priv: (priv d) {el2_stack: extend_stack' n (el2_stack (priv d))}}).

Definition shrink_stack (n: nat) (d: RData) :=
  if a_EL3 (asm_regs (priv d)) then
    match shrink_stack' n (el3_stack (priv d)) with
    | Some stk' =>
      Some (d {priv: (priv d) {el3_stack: stk'}})
    | _ => None
    end
  else
    match shrink_stack' n (el2_stack (priv d)) with
    | Some stk' =>
      Some (d {priv: (priv d) {el2_stack: stk'}})
    | _ => None
    end.

(** Accessing memory *)

Parameter percpu_data_start: Z.

Definition get_el3_regs (rid: Z) (regs: RegState) :=
  if rid =? 0 then r_spsr_el3 regs else
  if rid =? 1 then r_elr_el3 regs else
  if rid =? 2 then r_actlr_el2 regs else
  if rid =? 3 then r_afsr0_el2 regs else
  if rid =? 4 then r_afsr1_el2 regs else
  if rid =? 5 then r_amair_el2 regs else
  if rid =? 6 then r_cnthctl_el2 regs else
  if rid =? 7 then r_cntvoff_el2 regs else
  if rid =? 8 then r_cptr_el2 regs else
  if rid =? 9 then r_elr_el2	 regs else
  if rid =? 10 then r_esr_el2	 regs else
  if rid =? 11 then r_far_el2	 regs else
  if rid =? 12 then r_hacr_el2 regs else
  if rid =? 13 then r_hcr_el2	 regs else
  if rid =? 14 then r_hpfar_el2 regs else
  if rid =? 15 then r_hstr_el2 regs else
  if rid =? 16 then r_mair_el2 regs else
  if rid =? 17 then r_mpam_el2 regs else
  if rid =? 18 then r_mpamhcr_el2 regs else
  if rid =? 19 then r_pmscr_el2 regs else
  if rid =? 20 then r_sctlr_el2 regs else
  if rid =? 21 then r_scxtnum_el2 regs else
  if rid =? 22 then r_sp_el2	 regs else
  if rid =? 23 then r_spsr_el2 regs else
  if rid =? 24 then r_tcr_el2	 regs else
  if rid =? 25 then r_tfsr_el2 regs else
  if rid =? 26 then r_tpidr_el2 regs else
  if rid =? 27 then r_trfcr_el2 regs else
  if rid =? 28 then r_ttbr0_el2 regs else
  if rid =? 29 then r_ttbr1_el2 regs else
  if rid =? 30 then r_vbar_el2 regs else
  if rid =? 31 then r_vdisr_el2 regs else
  if rid =? 32 then r_vmpidr_el2 regs else
  if rid =? 33 then r_vncr_el2 regs else
  if rid =? 34 then r_vpidr_el2 regs else
  if rid =? 35 then r_vsesr_el2 regs else
  if rid =? 36 then r_vstcr_el2 regs else
  if rid =? 37 then r_vsttbr_el2 regs else
  if rid =? 38 then r_vtcr_el2 regs else
  if rid =? 39 then r_vttbr_el2 regs else
  if rid =? 40 then r_zcr_el2 regs else 0.

Definition set_el3_regs (rid val: Z) (regs: RegState) :=
  if rid =? 0 then regs {r_spsr_el3: val} else
  if rid =? 1 then regs {r_elr_el3: val} else
  if rid =? 2 then regs {r_actlr_el2: val} else
  if rid =? 3 then regs {r_afsr0_el2: val} else
  if rid =? 4 then regs {r_afsr1_el2: val} else
  if rid =? 5 then regs {r_amair_el2: val} else
  if rid =? 6 then regs {r_cnthctl_el2: val} else
  if rid =? 7 then regs {r_cntvoff_el2: val} else
  if rid =? 8 then regs {r_cptr_el2: val} else
  if rid =? 9 then regs {r_elr_el2	: val} else
  if rid =? 10 then regs {r_esr_el2	: val} else
  if rid =? 11 then regs {r_far_el2	: val} else
  if rid =? 12 then regs {r_hacr_el2: val} else
  if rid =? 13 then regs {r_hcr_el2	: val} else
  if rid =? 14 then regs {r_hpfar_el2: val} else
  if rid =? 15 then regs {r_hstr_el2: val} else
  if rid =? 16 then regs {r_mair_el2: val} else
  if rid =? 17 then regs {r_mpam_el2: val} else
  if rid =? 18 then regs {r_mpamhcr_el2: val} else
  if rid =? 19 then regs {r_pmscr_el2: val} else
  if rid =? 20 then regs {r_sctlr_el2: val} else
  if rid =? 21 then regs {r_scxtnum_el2: val} else
  if rid =? 22 then regs {r_sp_el2	: val} else
  if rid =? 23 then regs {r_spsr_el2: val} else
  if rid =? 24 then regs {r_tcr_el2	: val} else
  if rid =? 25 then regs {r_tfsr_el2: val} else
  if rid =? 26 then regs {r_tpidr_el2: val} else
  if rid =? 27 then regs {r_trfcr_el2: val} else
  if rid =? 28 then regs {r_ttbr0_el2: val} else
  if rid =? 29 then regs {r_ttbr1_el2: val} else
  if rid =? 30 then regs {r_vbar_el2: val} else
  if rid =? 31 then regs {r_vdisr_el2: val} else
  if rid =? 32 then regs {r_vmpidr_el2: val} else
  if rid =? 33 then regs {r_vncr_el2: val} else
  if rid =? 34 then regs {r_vpidr_el2: val} else
  if rid =? 35 then regs {r_vsesr_el2: val} else
  if rid =? 36 then regs {r_vstcr_el2: val} else
  if rid =? 37 then regs {r_vsttbr_el2: val} else
  if rid =? 38 then regs {r_vtcr_el2: val} else
  if rid =? 39 then regs {r_vttbr_el2: val} else
  if rid =? 40 then regs {r_zcr_el2: val} else regs.

Definition mem_load (base: Z) (off: Z) (d: RData) :=
  if base =? SP then
    if (off >=? 0) && (off mod 8 =? 0) then
      get_stack (Z.to_nat (off / 8)) d
    else None
  else
    let b := get_creg base d in
    if b =? percpu_data_start + CPUSTATE_NS_OFFSET then
      if (off >=? 0) && (off mod 8 =? 0) then
        Some (get_el3_regs (off/8) (ns_regs_el3 (priv d)))
      else None
    else
      if b =? percpu_data_start + CPUSTATE_REALM_OFFSET then
        if (off >=? 0) && (off mod 8 =? 0) then
          Some (get_el3_regs (off/8) (realm_regs_el3 (priv d)))
        else None
      else
        rely (peq (Z.to_pos (base / base_mult)) buffer_loc);
        when gidx == ((buffer (priv d)) @ (base mod base_mult));
        let gn := (gs (share d)) @ gidx in
        rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
        rely (ref_accessible gn CPU_ID);
        let gregs := (g_regs (grec gn)) in
        Some (get_reg off gregs).

Definition mem_store (base: Z) (off: Z) (val: Z) (d: RData) :=
  if base =? SP then
    if (off >=? 0) && (off mod 8 =? 0) then
      set_stack (Z.to_nat (off / 8)) val d
    else None
  else
    let b := get_creg base d in
    if b =? percpu_data_start + CPUSTATE_NS_OFFSET then
      if (off >=? 0) && (off mod 8 =? 0) then
        Some (d {priv: (priv d) {ns_regs_el3: set_el3_regs (off/8) val (ns_regs_el3 (priv d))}})
      else None
    else
      if b =? percpu_data_start + CPUSTATE_REALM_OFFSET then
        if (off >=? 0) && (off mod 8 =? 0) then
          Some (d {priv: (priv d) {realm_regs_el3: set_el3_regs (off/8) val (realm_regs_el3 (priv d))}})
        else None
      else
        rely (peq (Z.to_pos (base / base_mult)) buffer_loc);
        when gidx == ((buffer (priv d)) @ (base mod base_mult));
        let gn := (gs (share d)) @ gidx in
        rely (g_tag (ginfo gn) =? GRANULE_STATE_REC);
        rely (ref_accessible gn CPU_ID);
        let gregs := (g_regs (grec gn)) in
        let g' := gn {grec: (grec gn) {g_regs: set_reg off val gregs}} in
        Some (d {share: (share d) {gs: (gs (share d)) # gidx == g'}}).

Section RELSEM.

Variable ge: genv.

(** Looking up instructions in a code sequence by position. *)

Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end.

(** Position corresponding to a label *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Plabel lbl' => if zeq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Plabel lbl else instr <> Plabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  destruct (zeq lbl lbl0); congruence.
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]). *)

Definition nextinstr (d: RData) :=
  match a_PC (asm_regs (priv d)) with
  | (b, ofs) =>
    d {priv: (priv d) {asm_regs: (asm_regs (priv d)) {a_PC: (b, ofs + 1)}}}
  end.

Definition goto_label (f: function) (lbl: label) (d: RData) :=
  match label_pos lbl 0 (fn_code f) with
  | None => None
  | Some pos =>
    match a_PC (asm_regs (priv d)) with
    | (b, ofs) =>
      Some (d {priv: (priv d) {asm_regs: (asm_regs (priv d)) {a_PC: (b, pos)}}})
    end
  end.

(** Testing a condition *)

Definition eval_testcond (c: testcond) (d: RData) : option bool :=
  match c with
  | TCeq =>                             (**r equal *)
      match a_CZ (asm_regs (priv d)) with
      | Some b => Some b
      | _ => None
      end
  | TCne =>                             (**r not equal *)
      match a_CZ (asm_regs (priv d)) with
      | Some b => Some (negb b)
      | _ => None
      end
  | TClo =>                             (**r unsigned less than  *)
      match a_CC (asm_regs (priv d)) with
      | Some b => Some (negb b)
      | _ => None
      end
  | TCls =>                             (**r unsigned less or equal *)
      match a_CC (asm_regs (priv d)), a_CZ (asm_regs (priv d)) with
      | Some b1, Some b2 => Some ((negb b1) || b2)
      | _, _ => None
      end
  | TChs =>                             (**r unsigned greater or equal *)
      match a_CC (asm_regs (priv d)) with
      | Some b => Some b
      | _ => None
      end
  | TChi =>                             (**r unsigned greater *)
      match a_CC (asm_regs (priv d)), a_CZ (asm_regs (priv d)) with
      | Some b1, Some b2 => Some (b1 && (negb b2))
      | _, _ => None
      end
  | TClt =>                             (**r signed less than *)
      match a_CV (asm_regs (priv d)), a_CN (asm_regs (priv d)) with
      | Some b1, Some b2 => Some (xorb b1 b2)
      | _, _ => None
      end
  | TCle =>                             (**r signed less or equal *)
      match a_CV (asm_regs (priv d)), a_CN (asm_regs (priv d)), a_CZ (asm_regs (priv d)) with
      | Some b1, Some b2, Some b3 => Some ((xorb b1 b2) || b3)
      | _, _, _ => None
      end
  | TCge =>                             (**r signed greater or equal *)
      match a_CV (asm_regs (priv d)), a_CN (asm_regs (priv d)) with
      | Some b1, Some b2 => Some (negb (xorb b1 b2))
      | _, _ => None
      end
  | TCgt =>                             (**r signed greater *)
      match a_CV (asm_regs (priv d)), a_CN (asm_regs (priv d)), a_CZ (asm_regs (priv d)) with
      | Some b1, Some b2, Some b3 => Some ((negb (xorb b1 b2)) && (negb b3))
      | _, _, _ => None
      end
  | TCpl =>                             (**r positive *)
      match a_CN (asm_regs (priv d)) with
      | Some b => Some (negb b)
      | _ => None
      end
  | TCmi =>                             (**r negative *)
      match a_CN (asm_regs (priv d)) with
      | Some b => Some b
      | _ => None
      end
  end.

(** Integer "is zero?" test *)

Definition eval_testzero (val: Z) (d: RData) := val =? 0.

(** Integer "bit is set?" test *)

Definition eval_testbit (v: Z) (n: Z): bool :=
  negb ((Z.land (Z.shiftl 1 n) v) =? 0).

(** Evaluating an addressing mode *)

Definition eval_addressing (a: addressing) (d: RData) :=
  match a with
  | ADimm base n => (get_creg base d) + n
  | ADreg base r => (get_creg base d) + (get_creg r d)
  | ADlsl base r n =>  (get_creg base d) + (Z.shiftl (get_creg r d) n)
  | ADpostincr base n => (get_creg base d)
  end.

(** Auxiliaries for memory accesses *)

(** Comparisons *)

Definition compare_long (d: RData) (v1 v2: Z) :=
  d {priv: (priv d) {asm_regs: (asm_regs (priv d)) {a_CZ: Some (v1 =? v2)}}}.

(** Added by Xuheng, set NZCV bits *)
Definition set_nzcv (d: RData) (n: Z) :=
  d {priv: (priv d) {asm_regs: (asm_regs (priv d)) {a_CN: Some (Z.testbit n 3)}
                                                   {a_CZ: Some (Z.testbit n 2)}
                                                   {a_CC: Some (Z.testbit n 1)}
                                                   {a_CV: Some (Z.testbit n 0)}}}.

(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual AArch64 instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the ARMv8 reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above.

    Note that we set to [Vundef] the registers used as temporaries by
    the expansions of the pseudo-instructions, so that the code we
    generate cannot use those registers to hold values that must
    survive the execution of the pseudo-instruction.
*)

Definition exec_instr (f: function) (i: instruction) (d: RData) : option RData :=
  match i with
  (** Branches *)
  | Pb lbl =>
      goto_label f lbl d
  | Pbc cond lbl =>
      match eval_testcond cond d with
      | Some true => goto_label f lbl d
      | Some false => Some (nextinstr d)
      | None => None
      end
  | Pbl id sg =>
    match a_PC (asm_regs (priv d)) with
    | (b, ofs) =>
      Some (set_creg RA (b * 10000 + (ofs+1)) (set_pc (id, 0) d))
    end
  | Pbs id sg =>
      Some (set_pc (id, 0) d)
  | Pblr r sg =>
    match a_PC (asm_regs (priv d)) with
    | (b, ofs) =>
      let val := get_creg r d in
      let b' := r / 10000 in
      let ofs' := r mod 10000 in
      Some (set_creg RA (b * 10000 + ofs) (set_pc (b', ofs') d))
    end
  | Pbr r sg =>
    let val := get_creg r d in
    let b' := r / 10000 in
    let ofs' := r mod 10000 in
    Some (set_pc (b', ofs') d)
  | Pcbnz r lbl =>
    if eval_testzero (get_creg r d) d then
      Some (nextinstr d)
    else
      goto_label f lbl d
  | Pcbz r lbl =>
    if eval_testzero (get_creg r d) d then
      goto_label f lbl d
    else
      Some (nextinstr d)
  | Ptbnz r n lbl =>
      if eval_testbit (get_creg r d) n then
        goto_label f lbl d
      else
        Some (nextinstr d)
  | Ptbz r n lbl =>
      if eval_testbit (get_creg r d) n then
        Some (nextinstr d)
      else
        goto_label f lbl d
  (* Register Insts *)
  | Paddimm r1 r2 imm =>  (* add x0, x0, #CPUSTATE_NS_OFFSET *)
    if (r1 =? SP) || (r2 =? SP) then
      if (r1 =? SP) && (r2 =? SP) && (imm >? 0) && (imm mod 8 =? 0) then
        when d' == shrink_stack (Z.to_nat (imm / 8)) d;
        Some (nextinstr d')
      else None
    else
      Some (nextinstr (set_creg r1 ((get_creg r2 d) + imm) d))
  | Psubimm r1 r2 imm =>  (* add x0, x0, #CPUSTATE_NS_OFFSET *)
    if (r1 =? SP) || (r2 =? SP) then
      if (r1 =? SP) && (r2 =? SP) && (imm >? 0) && (imm mod 8 =? 0) then
        when d' == extend_stack (Z.to_nat (imm / 8)) d;
        Some (nextinstr d')
      else None
    else
      Some (nextinstr (set_creg r1 ((get_creg r2 d) - imm) d))
  | Pand r1 r2 r3 =>  (* and x1, x1, x4 *)
    Some (nextinstr (set_creg r1 (Z.land (get_creg r2 d) (get_creg r3 d)) d))
  | Pandimm r1 r2 imm =>  (* ands x1, x0, #ESR_EC_SMC_IMM16 *)
    Some (nextinstr (set_creg r1 (Z.land (get_creg r2 d) imm) d))
  | Pcmp r1 r2 =>     (* cmp x1, x2 *)
    let val1 := get_creg r1 d in
    let val2 := get_creg r2 d in
    Some (nextinstr (compare_long d val1 val2))
  | Pcmpimm r n =>     (* cmp x1, #SCR_REALM_WORLD *)
    let val := get_creg r d in
    Some (nextinstr (compare_long d val n))
  | Pbic r1 r2 n =>  (* bic x1, x0, #SMC_ARM_ARCH_CALL_MASK *)
    let val := get_creg r2 d in
    Some (nextinstr (set_creg r1 (Z.land val (U64MAX - n)) d))
  | Pldrimm r imm =>  (* ldr x2 =SMC_STD_CALL_BASE *)
    Some (nextinstr (set_creg r imm d))
  | Pmov r1 r2 =>  (* mrs x0 tpidr_el3 *)
    Some (nextinstr (set_creg r1 (get_creg r2 d) d))
  | Pmovimm r imm =>  (* mov x2 #0 *)
    Some (nextinstr (set_creg r imm d))
  | Pmrs r1 r2 =>  (* mrs x0 tpidr_el3 *)
    Some (nextinstr (set_creg r1 (get_creg r2 d) d))
  | Pmsr r1 r2 => (* msr scr_el3, x1 *)
    Some (nextinstr (set_creg r1 (get_creg r2 d) d))
  (* Load/Store *)
  | Pldr r ptr imm => (* ldr x18 [sp], #16 *)
    when val == mem_load ptr imm d;
    Some (nextinstr (set_creg r val d))
  | Pldr' r ptr imm => (* ldr x18 [sp], #16 *)
    when val == mem_load ptr 0 d;
    let d := set_creg r val d in
    if ptr =? SP then
      let sp := get_sp d in
      rely (imm >? 0);
      rely (imm mod 8 =? 0);
      when d == shrink_stack (Z.to_nat (imm / 8)) d;
      Some (nextinstr (set_sp (sp + imm) d))
    else None
  | Pldp r1 r2 ptr imm => (* ldr x18 [sp], #16 *)
    when val1 == mem_load ptr imm d;
    when val2 == mem_load ptr (imm + 8) d;
    Some (nextinstr (set_creg r2 val2 (set_creg r1 val1 d)))
  | Pldp' r1 r2 ptr imm => (* ldr x18 [sp], #16 *)
    when val1 == mem_load ptr 0 d;
    when val2 == mem_load ptr 8 d;
    let d := set_creg r2 val2 (set_creg r1 val1 d) in
    if ptr =? SP then
      let sp := get_sp d in
      rely (imm >? 0);
      rely (imm mod 8 =? 0);
      when d == shrink_stack (Z.to_nat (imm / 8)) d;
      Some (nextinstr (set_sp (sp + imm) d))
    else None
  | Pstr r ptr imm =>  (* str x18 [sp, #-16] *)
    let val := get_creg r d in
    when d' == mem_store ptr imm val d;
    Some (nextinstr d')
  | Pstr' r ptr imm => (* str x18 [sp, #-16] *)
    let val := get_creg r d in
    if ptr =? SP then
      let sp := get_sp d in
      rely (imm <? 0);
      rely (imm mod 8 =? 0);
      when d == extend_stack (Z.to_nat (-imm / 8)) d;
      let d := (set_sp (sp + imm) d) in
      when d' == mem_store SP 0 val d;
      Some (nextinstr d')
    else None
  | Pstp r1 r2 ptr imm =>  (* stp x29, lr, [sp, #-16] *)
    let val1 := get_creg r1 d in
    let val2 := get_creg r2 d in
    when d == mem_store ptr imm val1 d;
    when d' == mem_store ptr (imm + 8) val2 d;
    Some (nextinstr d')
  | Pstp' r1 r2 ptr imm =>  (* stp x29, lr, [sp, #-16]! *)
    let val1 := get_creg r1 d in
    let val2 := get_creg r2 d in
    if ptr =? SP then
      let sp := get_sp d in
      rely (imm <? 0);
      rely (imm mod 8 =? 0);
      when d == extend_stack (Z.to_nat (-imm / 8)) d;
      let d := (set_sp (sp + imm) d) in
      when d == mem_store SP 0 val1 d;
      when d' == mem_store SP 8 val2 d;
      Some (nextinstr d')
    else None
  (* Eret *)
  | Pret r =>
    let val := get_creg RA d in
    let b' := val / 10000 in
    let ofs' := val mod 10000 in
    let d := d {priv: (priv d) {asm_regs: (asm_regs (priv d)) {a_CZ: None}}} in
    Some (set_pc (b', ofs') (set_creg RA (-1) d))
  | Peret =>
    let d := d {priv: (priv d) {asm_regs: (asm_regs (priv d)) {a_CZ: None}}} in
    Some (set_pc (-1, -1) (set_creg RA (-1) d))
  (** Pseudo-instructions *)
  | Pstuck => None
  | _ =>
      Some (nextinstr d)
  end.

(** Translation of the LTL/Linear/Mach view of machine registers
  to the AArch64 view.  Note that no LTL register maps to [X16],
  [X18], nor [X30].
  [X18] is reserved as the platform register and never used by the
  code generated by CompCert.
  [X30] is used for the return address, and can also be used as temporary.
  [X16] can be used as temporary. *)

(** Undefine all registers except SP and callee-save registers *)

Definition undef_caller_save_regs (d: RData) : RData := d.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use AArch64 registers instead of locations. *)

Inductive extcall_arg (d: RData): Z -> Z -> Prop :=
  | extcall_arg_reg: forall r,
      0 <= r < 7 ->
      extcall_arg d r (get_creg r d).

(** Execution of the instruction at [rs#PC]. *)

Parameter ExternalCall: external_function -> genv -> list Z -> RData -> option Z -> RData -> Prop.

Inductive step: RData -> RData -> Prop :=
  | exec_step_internal:
      forall b ofs f i d d',
      get_pc d = (b, ofs) ->
      Genv.find_funct_ptr ge (Z.to_pos b) = Some (Internal f) ->
      find_instr ofs f.(fn_code) = Some i ->
      exec_instr f i d = Some d' ->
      step d d'
  | exec_step_external:
      forall b ef d d',
      get_pc d = (b, 0) ->
      Genv.find_funct_ptr ge (Z.to_pos b) = Some (External ef) ->
      d' = set_pc ((get_creg RA d) / 10000, (get_creg RA d) mod 10000) d ->
      step d d'.

End RELSEM.
