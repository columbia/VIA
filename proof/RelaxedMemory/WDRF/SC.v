(* SPDX-License-Identifier: GPL-2.0 *)
Require Import List.
Import ListNotations.
(* From RecordUpdate Require Import RecordSet.
Import RecordSetNotations. *)

Require Import WDRF.Base.
(* SC trace *)
Inductive GlobalEvent :=
| GE (tid : TID) (e : Event) : GlobalEvent.

Record GlobalState := mkGlobalState{
    memstate : MemState;
    regstates : TID -> RegState
} 
.
(* Instance etaGlobalState : Settable _ :=  settable! mkGlobalState <memstate; regstates>. *)
Definition update_memstate (a : GlobalState) b :=
  mkGlobalState b (regstates a).
Notation "a <|memstate := b |>" := (update_memstate a b) (at level 1).

Definition update_regstates (a : GlobalState) b :=
  mkGlobalState (memstate a) b.
Notation "a <|regstates := b |>" := (update_regstates a b) (at level 1).

Inductive rel_replay_sc : list GlobalEvent -> GlobalState -> Prop :=
| SC_EMPTY : rel_replay_sc [] (mkGlobalState (fun _ => 0) (fun _ _ => 0))
| SC_INTERNAL : forall le gs tid i rs
                    (Hgs : rel_replay_sc le gs)
                    (Hinternal : execute_internal i (regstates gs tid) = Some rs),
                    rel_replay_sc (GE tid (INTERNAL i) :: le) 
                        (gs <|regstates := update (regstates gs) tid rs |>)
| SC_LOAD : forall le gs tid addr view reg
                    (Hgs : rel_replay_sc le gs),
                    rel_replay_sc (GE tid (LOAD addr view reg) :: le)
                        (gs <|regstates := update (regstates gs) tid (update (regstates gs tid) reg (memstate gs addr)) |>)
| SC_STORE : forall le gs tid addr view reg
                    (Hgs : rel_replay_sc le gs),
                    rel_replay_sc (GE tid (STORE addr view reg) :: le)
                        (gs <|memstate := update (memstate gs) addr (regstates gs tid reg) |>)
| SC_ACQ : forall le gs tid view addr
                    (Hgs : rel_replay_sc le gs),
                    rel_replay_sc (GE tid (ACQ view addr) :: le) gs
| SC_REL : forall le gs tid view addr
                    (Hgs : rel_replay_sc le gs),
                    rel_replay_sc (GE tid (REL view addr) :: le) gs.

