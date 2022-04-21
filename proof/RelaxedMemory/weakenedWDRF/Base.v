(* SPDX-License-Identifier: GPL-2.0 *)
Require Import List.
Require Import Bool.
Require Import NArith PArith ZArith.

Set Implicit Arguments.

Definition Value := nat.
Definition default : Value := 0.
Definition Address := nat.
Definition TID := nat.
Definition RegID := nat.
Definition View := nat.

Inductive Promise :=
| WRITE : TID -> Value -> Address -> Promise 
| PUSH : TID -> Address -> Promise
| PULL : TID -> Address -> Promise
.

Inductive Expr :=
| CONST (val : Value) : Expr
| VAR (reg : RegID) : Expr
| ADD (e1 : Expr) (e2 : Expr) : Expr
.

Inductive InternalEvent :=
| MOV : RegID -> Expr -> InternalEvent
| BRANCH : RegID -> InternalEvent
.

Inductive Event :=
| INTERNAL : InternalEvent -> Event
| ORACLE : RegID -> Value -> Event
| LOAD : Address -> View -> RegID -> Event
| ACQ : View -> Address -> Event
| STORE : Address -> View -> RegID -> Event
| REL : View ->  Address -> Event
.

Definition RegState := RegID -> Value.
Definition MemState := Address -> Value.

Definition update {T : Type} s addr (val : T) :=
    (fun (x : nat) => if beq_nat x addr then val else s x).

(* Lemma about update *)
Lemma update_same :
    forall {T} s addr (val : T), update s addr val addr = val.
Proof.
    intros. unfold update. rewrite <- beq_nat_refl. reflexivity.
Qed.

Lemma update_not_same :
    forall {T} s addr (val : T) addr' (Hneq : addr <> addr'), update s addr val addr' = s addr'.
Proof.
    intros. unfold update. replace (beq_nat addr' addr) with false. easy.
    symmetry. rewrite beq_nat_false_iff. auto.
Qed.

Definition OwnershipMap := Address -> option TID.

Fixpoint eval (e : Expr) (st : RegState) : option Value :=
    match e with
    | CONST val => Some val
    | VAR reg => Some (st reg)
    | ADD e1 e2 => 
        match eval e1 st with
        | None => None
        | Some v1 =>
            match eval e2 st with
            | None => None
            | Some v2 => Some (v1 + v2)
            end
        end
    end.

Lemma eval_exists :
    forall e st, exists v, eval e st = Some v.
Proof.
    induction e; intro. 
    -   esplit; simpl; auto.
    -   esplit; simpl; auto.
    -   specialize (IHe1 st). destruct IHe1 as (v1 & Hv1).
        specialize (IHe2 st). destruct IHe2 as (v2 & Hv2).
        esplit. simpl.
        rewrite Hv1. rewrite Hv2. reflexivity.
Qed.
        

Definition execute_internal (i : InternalEvent) (st : RegState) : option RegState :=
    match i with
    | MOV reg e => 
                match eval e st with
                | None => None
                | Some val => Some (update st reg val)
                end
    | _ => Some st
    end.

Lemma execute_internal_exists : 
        forall i st, exists rs, execute_internal i st = Some rs.
Proof.
    destruct i.
    -   intros. induction e.
        +   simpl. eexists. reflexivity.
        +   simpl. eexists. reflexivity.
        +   simpl. destruct IHe1 as (rs1 & Hrs1).
            destruct IHe2 as (rs2 & Hrs2).
            simpl in *. destruct (eval e1 st); try discriminate. 
            destruct (eval e2 st); try discriminate.
            esplit. reflexivity.
    -   intros. simpl. esplit. reflexivity.
Qed.
