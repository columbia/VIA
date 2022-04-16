Require Import Coqlib.
Require Import Maps.
Require Import GenSem.

Require Import Constants.
Require Import CommonLib.
Require Import RData.
Require Import EventReplay.

Open Local Scope Z_scope.

Section MoverDefinitions.

  Inductive IsLeftMover (lvl: Z) (e: Event) : Prop :=
  | LEFT_MOVER
        (MoveT: forall st0 st0' st0'' e' ret ret'
                    (Hcidne: match e with EVT c _ => c end <> match e' with EVT c' _ => c' end)
                    (Hstep_e': ereplay lvl st0 e' = Some (st0', ret'))
                    (Hstep_e: ereplay lvl st0' e = Some (st0'', ret)),
            exists st0'x, ereplay lvl st0 e = Some (st0'x, ret) /\
                    ereplay lvl st0'x e' = Some (st0'', ret'))
        (MoveF: forall st0 st0' e' ret'
                    (Hcidne: match e with EVT c _ => c end <> match e' with EVT c' _ => c' end)
                    (Hstep_e': ereplay lvl st0 e' = Some (st0', ret'))
                    (Hstep_e: ereplay lvl st0' e = None),
            ereplay lvl st0 e = None):
        IsLeftMover lvl e.

  Inductive IsRightMover (lvl: Z) (e: Event) : Prop :=
  | RIGHT_MOVER
      (Move: forall st0 st0' st0'' e' ret ret'
                    (Hcidne: match e with EVT c _ => c end <> match e' with EVT c' _ => c' end)
                    (Hstep_e': ereplay lvl st0 e = Some (st0', ret))
                    (Hstep_e: ereplay lvl st0' e' = Some (st0'', ret')),
          exists st0'x, ereplay lvl st0 e' = Some (st0'x, ret') /\
                        ereplay lvl st0'x e = Some (st0'', ret)):
        IsRightMover lvl e.

  Inductive other_cpu_events: Log -> Prop :=
  | other_cpu_nil: other_cpu_events nil
  | other_cpu_cons:
      forall e l (Hother_cpu_e: match e with EVT c _ => c end <> CPU_ID)
        (Hother_cpu_l: other_cpu_events l),
        other_cpu_events (e :: l).

  Definition left_event_dec:
    forall lvl e, {IsLeftMover lvl e} + {~IsLeftMover lvl e}.
  Proof. intros. eapply prop_dec. Qed.

  Definition right_event_dec:
    forall lvl e, {IsRightMover lvl e} + {~IsRightMover lvl e}.
  Proof. intros. eapply prop_dec. Qed.

  Inductive RightLog (lvl: Z) : Log -> Prop :=
  | RightLogNil: RightLog lvl nil
  | RightLogOracle (l: Log) (o: Oracle): RightLog lvl (o l ++ l)
  | RightLogMover (l: Log) (e: Event)
                  (is_right_mover: IsRightMover lvl e)
                  (is_right_log: RightLog lvl l): RightLog lvl (e :: l).

  Inductive ValidOracle (lvl: Z) (orc: Oracle) :=
  | VALID_ORACLE
      (* oracle only emit valid events *)
      (Hsucc: forall l st (Hrep: Repl lvl l = Some st), exists st', Repl lvl ((orc l) ++ l) = Some st')
      (* oracle return events from other CPUs *)
      (Hother_cpu: forall l,  other_cpu_events (orc l))
      (* if current log is invalid, the oracle will return empty list *)
      (Hfailnil: forall l (Hrep: Repl lvl l = None), orc l = nil)
      (* oracle will return nil if it has been queried*)
      (* Log :: O :: O = Log :: O *)
      (Hdouble_query_nil: forall l, orc (orc l ++ l) = nil)
      (Hright_log_nil: forall l, RightLog lvl l -> orc l = nil):
      ValidOracle lvl orc.

End MoverDefinitions.

Section MoverOracleProperties.

  Lemma replay_some_ind:
    forall lvl e l s em,
      replay lvl (e :: l) em = Some s ->
      exists s' v, replay lvl l em = Some s' /\ ereplay lvl s' e = Some (s, v).
  Proof.
    intros.
    unfold replay in H; simpl in H.
    repeat (simpl_hyp H; contra).
    repeat eexists. inv H. eassumption. inv H. eassumption.
  Qed.

  Lemma replay_some_ind2:
    forall lvl l1 l2 s em,
      replay lvl (l1 ++ l2) em = Some s ->
      exists s', replay lvl l2 em = Some s' /\ replay lvl l1 s' = Some s.
  Proof.
    intros until l2.
    induction l1; intros.
    repeat eexists. eassumption. simpl.
    rewrite <- app_comm_cons in H.
    repeat (simpl_hyp H; contra).
    simpl in H.
    repeat (simpl_hyp H; contra).
    pose proof (IHl1 _ _ C).
    destruct H0 as (? & ? & ?).
    repeat eexists. eassumption.
    grewrite. inv H. reflexivity.
  Qed.

  Lemma replay_simpl_cons:
    forall lvl e l st, replay lvl (e :: l) st = match replay lvl l st with
                                          | Some st' => match ereplay lvl st' e with
                                                       | Some (st'', _) => Some st''
                                                       | _ => None
                                                       end
                                          | _ => None
                                          end.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma replay_simpl_app:
    forall lvl l1 l2 st,  replay lvl (l1 ++ l2) st = match replay lvl l2 st with
                                                | Some st' => replay lvl l1 st'
                                                | _ => None
                                                end.
  Proof.
    induction l1. simpl. intros. destruct (replay lvl l2 st); reflexivity.
    intros. rewrite <- app_comm_cons. simpl. rewrite IHl1.
    destruct (replay lvl l2 st); reflexivity.
  Qed.

End MoverOracleProperties.
