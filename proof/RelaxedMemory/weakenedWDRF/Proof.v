(* SPDX-License-Identifier: GPL-2.0 *)
Require Import List.
Import ListNotations.
(* From RecordUpdate Require Import RecordSet.
)Import RecordSetNotations. *)
(* Require Import PeanoNat. *)

Require Import Psatz.

Require Import weakenedWDRF.Base weakenedWDRF.Promising weakenedWDRF.DRF weakenedWDRF.SC.

Definition get_view (e : Event) : option View :=
    match e with
    | LOAD _ v _ => Some v
    | ACQ v _ => Some v
    | STORE _ v _ => Some v
    | REL v _ => Some v
    | _ => None
    end.

(* construct sc trace from promising trace *)
Inductive rel_global_trace : Trace -> list GlobalEvent -> Prop :=
| GT_EMPTY : forall n lp
                (Hempty : forall p, p <= n -> lp p = None), 
                rel_global_trace (mkTrace n lp (fun _ => [])) []
| GT_INTERNAL : forall t gt i tid
                    (Hgt : rel_global_trace t gt),
                    rel_global_trace 
                        (t
                            <|executions := update (executions t) tid (INTERNAL i :: (executions t tid)) |> 
                        )
                        (GE tid (INTERNAL i) :: gt)
| GT_ORACLE : forall t gt reg val tid
                    (Hgt : rel_global_trace t gt),
                    rel_global_trace
                        (t
                            <|executions := update (executions t) tid (ORACLE reg val :: (executions t tid)) |>
                        )
                        (GE tid (ORACLE reg val) :: gt)
| GT_LOAD : forall t gt addr view reg tid
                    (Hgt : rel_global_trace t gt)
                    (Hlast : forall ms, rel_replay_mem (promiselen t) (promiselist t) ms -> Some (ms addr) = get_value view (promiselist t)),
                    rel_global_trace 
                        (t
                            <|executions := update (executions t) tid (LOAD addr view reg :: (executions t tid)) |> 
                        )
                        (GE tid (LOAD addr view reg) :: gt)
| GT_STORE : forall t gt addr view reg tid val
                    (Hgt : rel_global_trace t gt)
                    (Hmask : promiselist t view = None)
                    (Hlast : forall ms, rel_replay_mem (promiselen t) (promiselist t) ms ->
                        rel_replay_mem (promiselen t) (update (promiselist t) view (Some (WRITE tid val addr))) 
                            (update ms addr val)    
                    )
                    (Hunused : forall e tid, In e (executions t tid) -> get_view e <> Some view),
                    rel_global_trace 
                        (t
                            <|promiselist := update (promiselist t) view (Some (WRITE tid val addr)) |>
                            <|executions := update (executions t) tid (STORE addr view reg :: (executions t tid)) |> 
                        )
                        (GE tid (STORE addr view reg) :: gt)
(* ACQs and RELs are ignored in the global trace *)
| GT_ACQUIRE : forall t gt view addr tid
                    (Hgt : rel_global_trace t gt)
                    (Hmask : promiselist t view = None)
                    (Hlast : forall om n, rel_global_ownership n om (update (promiselist t) view (Some (PULL tid addr))) (fun _ => None) ->
                        exists om', rel_global_ownership n om' (promiselist t) (fun _ => None))
                    (Hunused : forall e tid, In e (executions t tid) -> get_view e <> Some view),
                    rel_global_trace
                        (t
                            <|promiselist := update (promiselist t) view (Some (PULL tid addr)) |>
                            <|executions := update (executions t) tid (ACQ view addr :: (executions t tid)) |> 
                        )
                        gt
| GT_RELEASE : forall t gt view addr tid
                    (Hgt : rel_global_trace t gt)
                    (Hmask : promiselist t view = None)
                    (Hlast : forall om n, rel_global_ownership n om (update (promiselist t) view (Some (PUSH tid addr))) (fun _ => None) ->
                        exists om', rel_global_ownership n om' (promiselist t) (fun _ => None))
                    (Hunused : forall e tid, In e (executions t tid) -> get_view e <> Some view),
                    rel_global_trace
                        (t
                            <|promiselist := update (promiselist t) view (Some (PUSH tid addr)) |>
                            <|executions := update (executions t) tid (REL view addr :: (executions t tid)) |> 
                        )
                        gt.



Inductive same_result : Trace -> list GlobalEvent -> Prop :=
| SAME_RESULT : forall t gt ms gs rs
                    (Hpamem : rel_replay_mem (promiselen t) (promiselist t) ms)
                    (Hpareg : forall tid, rel_replay_reg (promiselist t) (executions t tid) (rs tid))
                    (Hsc : rel_replay_sc gt gs)
                    (Hms : memstate gs = ms)
                    (Hreg : forall tid, regstates gs tid = rs tid)
                    ,
                    same_result t gt.

Lemma replay_mem_exists : forall lp n, exists ms, rel_replay_mem n lp ms.
Proof.
    intro. induction n.
    -   esplit. constructor.
    -   destruct IHn as (ms & Hms). destruct (lp (S n)) eqn:Hsn.
        +   destruct p.
            *   esplit.
                eapply REPLAY_MEM_WRITE. apply Hms. apply Hsn.
            *   esplit.  
                eapply REPLAY_MEM_OTHER. apply Hms. rewrite Hsn. easy.
            *   esplit.  
                eapply REPLAY_MEM_OTHER. apply Hms. rewrite Hsn. easy.
        +   esplit. eapply REPLAY_MEM_OTHER. apply Hms. rewrite Hsn. easy.
Qed.


Lemma replay_sc_exists : forall gt, exists gs, rel_replay_sc gt gs.
Proof.
    intro. induction gt.
    -   esplit. constructor.
    -   destruct a.
        destruct e; destruct IHgt as (gs & Hgs).
        {
            specialize (execute_internal_exists i (regstates gs tid)). intro. destruct H  as (rs & Hrs).
            esplit. constructor. apply Hgs. apply Hrs.
        }
        esplit; constructor; try apply Hgs.
        esplit; constructor; try apply Hgs.
        esplit; constructor; try apply Hgs.
        esplit; constructor; try apply Hgs.
        esplit; constructor; try apply Hgs.
Qed.

Lemma empty_replay_mem :
        forall n lp
            (Hempty : forall p : nat, p <= n -> lp p = None),
            rel_replay_mem n lp (fun addr => 0).
Proof.
    induction n; intros.
    -   constructor.
    -   apply REPLAY_MEM_OTHER. apply IHn.
        intros. apply Hempty. lia.
        rewrite Hempty. easy. easy.
Qed.

Lemma nth_error_inv :
        forall {T} (l : list T) n a b, nth_error (a :: l) n = Some b ->
            (n = 0 /\ a = b) \/ (exists n', n = S n' /\ nth_error l n' = Some b).
Proof.
    intros.
    destruct n.
    left. simpl in *. inversion H. easy.
    right. simpl in *. exists n. split. easy.
    assumption.
Qed.



Lemma localstate_promise_unused_write : 
    forall tid pl ex ls view val addr tid'
        (Hmask : pl view = None)
        (Hunused : forall e, In e ex -> get_view e <> Some view)
        (Hls : rel_promising tid (update pl view (Some (WRITE tid' val addr))) ex ls),
        rel_promising tid pl ex ls.
Proof.
    induction ex; intros.
    -   inversion Hls. constructor.
    -   inversion Hls.
        +   econstructor.
            eapply IHex.
            *   apply Hmask.
            *   intros. apply Hunused. simpl. auto.
            *   apply Hls0.
            *   apply Hexec. 
        +   econstructor. 
            eapply IHex. apply Hmask.
            intros. apply Hunused. simpl. auto. apply Hls0.
        +   econstructor. 
            eapply IHex. apply Hmask.
            intros. apply Hunused. simpl. auto.
            apply Hls0. eapply Le.le_trans. apply previous_promise_incr.
            apply Hmask. apply Hbarrier. 
            apply Hcoh.
            rewrite update_not_same in Hpromise. easy.
            specialize Hunused with a. intro. destruct Hunused.
            simpl. auto. unfold get_view. subst a. rewrite H4. easy.
        +   econstructor.
            eapply IHex. apply Hmask.
            intros. apply Hunused. simpl. auto.
            apply Hls0. rewrite update_not_same in Hpromise. apply Hpromise.
            intro. specialize Hunused with a. destruct Hunused.
            simpl. auto. unfold get_view. subst a. rewrite H4. easy.
        +   constructor.
            eapply IHex. apply Hmask.
            intros. apply Hunused. simpl. auto.
            apply Hls0. apply Hbarrier. apply Hcoh.
            rewrite update_not_same in Hpromise. apply Hpromise.
            intro. specialize Hunused with a. destruct Hunused.
            simpl. auto. unfold get_view. subst a. rewrite H4. easy.
        +   econstructor.
            eapply IHex. apply Hmask.
            intros. apply Hunused. simpl. auto.
            apply Hls0. rewrite update_not_same in Hpromise. apply Hpromise.
            intro. specialize Hunused with a. destruct Hunused.
            simpl. auto. unfold get_view. subst a. rewrite H4. easy.
            apply Hbarrier.
Qed.

Lemma global_ownership_unused_write_aux :
    forall n omr pl view tid val addr om
        (Hmask : pl view = None)
        (Hom : rel_global_ownership n om (update pl view (Some (WRITE tid val addr))) omr),
        rel_global_ownership n om pl omr.
Proof.
    induction n; intros.
    -   inversion Hom. constructor.
    -   inversion Hom.
        +   constructor. eapply IHn.
            apply Hmask. apply Hlp. apply Hown.
            rewrite <- Hlp0. rewrite update_not_same. easy.
            intro. subst. rewrite update_same in Hlp0. discriminate.
        +   econstructor. eapply IHn.
            apply Hmask. apply Hlp. apply Hown.
            rewrite <- Hlp0. rewrite update_not_same. easy.
            intro. subst. rewrite update_same in Hlp0. discriminate.
        +   destruct (Peano_dec.eq_nat_dec view (S n)).
            *   apply GO_NONE. eapply IHn. apply Hmask. apply Hlp.
                subst. apply Hmask.
            *   eapply GO_WRITE. eapply IHn.
            apply Hmask. apply Hlp. apply Hown.
            rewrite update_not_same in Hlp0 by easy.
            apply Hlp0.
        +   destruct (Peano_dec.eq_nat_dec view (S n)).
            *   apply GO_NONE. eapply IHn. apply Hmask. apply Hlp.
                subst. apply Hmask.
            *   eapply GO_NONE. eapply IHn.
            apply Hmask. apply Hlp.
            rewrite update_not_same in Hlp0 by easy.
            apply Hlp0.
Qed. 

Lemma global_ownership_unused_write :
    forall n pl view tid val addr om
        (Hmask : pl view = None)
        (Hom : rel_global_ownership n om (update pl view (Some (WRITE tid val addr))) (fun _ => None)),
        rel_global_ownership n om pl (fun _ => None).
Proof.
    intros. eapply global_ownership_unused_write_aux.
    apply Hmask. apply Hom.
Qed.

Lemma local_ownership_unused_write :
    forall pl ex lo view val addr tid'
        (Hmask : pl view = None)
        (Hunused : forall e, In e ex -> get_view e <> Some view)
        (Hlo : rel_local_ownership (update pl view (Some (WRITE tid' val addr))) ex lo),
        rel_local_ownership pl ex lo.
Proof.
    induction ex; intros.
    -   inversion Hlo. constructor.
    -   inversion Hlo.
        +   constructor. eapply IHex.
            apply Hmask. intros. apply Hunused.
            simpl. right. easy.
            apply Hlo0. apply Hown.
        +   constructor. eapply IHex.
            apply Hmask. intros. apply Hunused.
            simpl. right. easy.
            apply Hlo0. apply Hown.
        +   constructor. eapply IHex.
            apply Hmask. intros. apply Hunused.
            simpl. right. easy.
            apply Hlo0. apply Hown. apply Hview.
        +   constructor. eapply IHex.
            apply Hmask. intros. apply Hunused.
            simpl. right. easy.
            apply Hlo0. apply Hown. apply Hview.
        +   constructor. eapply IHex.
            apply Hmask. intros. apply Hunused.
            simpl. right. easy.
            apply Hlo0.
        +   constructor. eapply IHex.
            apply Hmask. intros. apply Hunused.
            simpl. right. easy.
            apply Hlo0.
Qed.


Lemma regstate_write_unchanged :
    forall pl ex view tid addr rs val
        (Hmask : pl view = None)
        (Hunused : forall e, In e ex -> get_view e <> Some view)
        (Hrs : rel_replay_reg pl ex rs),
        rel_replay_reg (update pl view (Some (WRITE tid val addr))) ex rs.
Proof.
    induction ex; intros.
    -   inversion Hrs. constructor.
    -   inversion Hrs.
        +   econstructor. apply IHex.
            apply Hmask. intros. apply Hunused. simpl. right. easy.
            apply Hs. apply Hinternal.
        +   econstructor. apply IHex.
            apply Hmask. intros. apply Hunused. simpl. right. easy.
            apply Hs.
        +   econstructor. apply IHex.
            apply Hmask. intros. apply Hunused. simpl. right. easy.
            apply Hs. unfold get_value in *.
            rewrite update_not_same. apply Hval.
            intro. edestruct Hunused.
            simpl. left. reflexivity.
            subst a. simpl. subst. reflexivity.
        +   econstructor. apply IHex.
            apply Hmask. intros. apply Hunused. simpl. right. easy.
            apply Hs. unfold get_value in *.
            rewrite update_not_same. apply Hval.
            intro. edestruct Hunused.
            simpl. left. reflexivity.
            subst a. simpl. subst. reflexivity.
        +   econstructor. apply IHex.
            apply Hmask. intros. apply Hunused. simpl. right. easy.
            apply Hs. 
        +   econstructor. apply IHex.
            apply Hmask. intros. apply Hunused. simpl. right. easy.
            apply Hs.  
Qed.

Lemma localstate_promise_unused_pull : 
    forall tid pl ex ls view addr tid'
        (Hmask : pl view = None)
        (Hunused : forall e, In e ex -> get_view e <> Some view)
        (Hls : rel_promising tid (update pl view (Some (PULL tid' addr))) ex ls),
        rel_promising tid pl ex ls.
Proof.
    induction ex; intros.
    -   inversion Hls. constructor.
    -   inversion Hls.
        +   econstructor.
            eapply IHex.
            *   apply Hmask.
            *   intros. apply Hunused. simpl. auto.
            *   apply Hls0.
            *   apply Hexec. 
        +   econstructor. 
            eapply IHex. apply Hmask.
            intros. apply Hunused. simpl. auto. apply Hls0.
        +   econstructor. 
            eapply IHex. apply Hmask.
            intros. apply Hunused. simpl. auto.
            apply Hls0. eapply Le.le_trans. apply previous_promise_incr.
            apply Hmask. apply Hbarrier. 
            apply Hcoh.
            rewrite update_not_same in Hpromise. easy.
            specialize Hunused with a. intro. destruct Hunused.
            simpl. auto. unfold get_view. subst a. rewrite H4. easy.
        +   econstructor.
            eapply IHex. apply Hmask.
            intros. apply Hunused. simpl. auto.
            apply Hls0. rewrite update_not_same in Hpromise. apply Hpromise.
            intro. specialize Hunused with a. destruct Hunused.
            simpl. auto. unfold get_view. subst a. rewrite H4. easy.
        +   constructor.
            eapply IHex. apply Hmask.
            intros. apply Hunused. simpl. auto.
            apply Hls0. apply Hbarrier. apply Hcoh.
            rewrite update_not_same in Hpromise. apply Hpromise.
            intro. specialize Hunused with a. destruct Hunused.
            simpl. auto. unfold get_view. subst a. rewrite H4. easy.
        +   econstructor.
            eapply IHex. apply Hmask.
            intros. apply Hunused. simpl. auto.
            apply Hls0. rewrite update_not_same in Hpromise. apply Hpromise.
            intro. specialize Hunused with a. destruct Hunused.
            simpl. auto. unfold get_view. subst a. rewrite H4. easy.
            apply Hbarrier.
Qed.

Lemma local_ownership_unused_pull :
    forall pl ex lo view addr tid'
        (Hmask : pl view = None)
        (Hunused : forall e, In e ex -> get_view e <> Some view)
        (Hlo : rel_local_ownership (update pl view (Some (PULL tid' addr))) ex lo),
        rel_local_ownership pl ex lo.
Proof.
    induction ex; intros.
    -   inversion Hlo. constructor.
    -   inversion Hlo.
        +   constructor. eapply IHex.
            apply Hmask. intros. apply Hunused.
            simpl. right. easy.
            apply Hlo0. apply Hown.
        +   constructor. eapply IHex.
            apply Hmask. intros. apply Hunused.
            simpl. right. easy.
            apply Hlo0. apply Hown.
        +   constructor. eapply IHex.
            apply Hmask. intros. apply Hunused.
            simpl. right. easy.
            apply Hlo0. apply Hown. apply Hview.
        +   constructor. eapply IHex.
            apply Hmask. intros. apply Hunused.
            simpl. right. easy.
            apply Hlo0. apply Hown. apply Hview.
        +   constructor. eapply IHex.
            apply Hmask. intros. apply Hunused.
            simpl. right. easy.
            apply Hlo0.
        +   constructor. eapply IHex.
            apply Hmask. intros. apply Hunused.
            simpl. right. easy.
            apply Hlo0.
Qed.

Lemma memstate_pull_unchanged :
    forall n pl view ms tid addr
        (Hmask : pl view = None)
        (Hms : rel_replay_mem n pl ms),
        rel_replay_mem n (update pl view (Some (PULL tid addr))) ms.
Proof.
    induction n; intros.
    -   inversion Hms. constructor.
    -   inversion Hms.
        +   econstructor. apply IHn.
            apply Hmask. apply Hlp.
            rewrite update_not_same. apply Hwrite.
            intro. contradict Hwrite. subst. rewrite Hmask. easy.
        +   econstructor. apply IHn.
            apply Hmask. apply Hlp.
            destruct (Peano_dec.eq_nat_dec view (S n)).
            *   subst. rewrite update_same. easy.
            *   rewrite update_not_same by easy. apply Hnotwrite.
Qed.   

Lemma regstate_pull_unchanged :
    forall pl ex view tid addr rs
        (Hmask : pl view = None)
        (Hunused : forall e, In e ex -> get_view e <> Some view)
        (Hrs : rel_replay_reg pl ex rs),
        rel_replay_reg (update pl view (Some (PULL tid addr))) ex rs.
Proof.
    induction ex; intros.
    -   inversion Hrs. constructor.
    -   inversion Hrs.
        +   econstructor. apply IHex.
            apply Hmask. intros. apply Hunused. simpl. right. easy.
            apply Hs. apply Hinternal.
        +   econstructor. apply IHex.
            apply Hmask. intros. apply Hunused. simpl. right. easy.
            apply Hs. 
        +   econstructor. apply IHex.
            apply Hmask. intros. apply Hunused. simpl. right. easy.
            apply Hs. unfold get_value in *.
            rewrite update_not_same. apply Hval.
            intro. edestruct Hunused.
            simpl. left. reflexivity.
            subst a. simpl. subst. reflexivity.
        +   econstructor. apply IHex.
            apply Hmask. intros. apply Hunused. simpl. right. easy.
            apply Hs. unfold get_value in *.
            rewrite update_not_same. apply Hval.
            intro. edestruct Hunused.
            simpl. left. reflexivity.
            subst a. simpl. subst. reflexivity.
        +   econstructor. apply IHex.
            apply Hmask. intros. apply Hunused. simpl. right. easy.
            apply Hs. 
        +   econstructor. apply IHex.
            apply Hmask. intros. apply Hunused. simpl. right. easy.
            apply Hs.  
Qed.

Lemma localstate_promise_unused_push : 
    forall tid pl ex ls view addr tid'
        (Hmask : pl view = None)
        (Hunused : forall e, In e ex -> get_view e <> Some view)
        (Hls : rel_promising tid (update pl view (Some (PUSH tid' addr))) ex ls),
        rel_promising tid pl ex ls.
Proof.
    induction ex; intros.
    -   inversion Hls. constructor.
    -   inversion Hls.
        +   econstructor.
            eapply IHex.
            *   apply Hmask.
            *   intros. apply Hunused. simpl. auto.
            *   apply Hls0.
            *   apply Hexec. 
        +   econstructor. 
            eapply IHex. apply Hmask.
            intros. apply Hunused. simpl. auto. apply Hls0.
        +   econstructor. 
            eapply IHex. apply Hmask.
            intros. apply Hunused. simpl. auto.
            apply Hls0. eapply Le.le_trans. apply previous_promise_incr.
            apply Hmask. apply Hbarrier. 
            apply Hcoh.
            rewrite update_not_same in Hpromise. easy.
            specialize Hunused with a. intro. destruct Hunused.
            simpl. auto. unfold get_view. subst a. rewrite H4. easy.
        +   econstructor.
            eapply IHex. apply Hmask.
            intros. apply Hunused. simpl. auto.
            apply Hls0. rewrite update_not_same in Hpromise. apply Hpromise.
            intro. specialize Hunused with a. destruct Hunused.
            simpl. auto. unfold get_view. subst a. rewrite H4. easy.
        +   constructor.
            eapply IHex. apply Hmask.
            intros. apply Hunused. simpl. auto.
            apply Hls0. apply Hbarrier. apply Hcoh.
            rewrite update_not_same in Hpromise. apply Hpromise.
            intro. specialize Hunused with a. destruct Hunused.
            simpl. auto. unfold get_view. subst a. rewrite H4. easy.
        +   econstructor.
            eapply IHex. apply Hmask.
            intros. apply Hunused. simpl. auto.
            apply Hls0. rewrite update_not_same in Hpromise. apply Hpromise.
            intro. specialize Hunused with a. destruct Hunused.
            simpl. auto. unfold get_view. subst a. rewrite H4. easy.
            apply Hbarrier.
Qed.

Lemma local_ownership_unused_push :
    forall pl ex lo view addr tid'
        (Hmask : pl view = None)
        (Hunused : forall e, In e ex -> get_view e <> Some view)
        (Hlo : rel_local_ownership (update pl view (Some (PUSH tid' addr))) ex lo),
        rel_local_ownership pl ex lo.
Proof.
    induction ex; intros.
    -   inversion Hlo. constructor.
    -   inversion Hlo.
        +   constructor. eapply IHex.
            apply Hmask. intros. apply Hunused.
            simpl. right. easy.
            apply Hlo0. apply Hown.
        +   constructor. eapply IHex.
            apply Hmask. intros. apply Hunused.
            simpl. right. easy.
            apply Hlo0. apply Hown.
        +   constructor. eapply IHex.
            apply Hmask. intros. apply Hunused.
            simpl. right. easy.
            apply Hlo0. apply Hown. apply Hview.
        +   constructor. eapply IHex.
            apply Hmask. intros. apply Hunused.
            simpl. right. easy.
            apply Hlo0. apply Hown. apply Hview.
        +   constructor. eapply IHex.
            apply Hmask. intros. apply Hunused.
            simpl. right. easy.
            apply Hlo0.
        +   constructor. eapply IHex.
            apply Hmask. intros. apply Hunused.
            simpl. right. easy.
            apply Hlo0.
Qed.

Lemma regstate_push_unchanged :
    forall pl ex view tid addr rs
        (Hmask : pl view = None)
        (Hunused : forall e, In e ex -> get_view e <> Some view)
        (Hrs : rel_replay_reg pl ex rs),
        rel_replay_reg (update pl view (Some (PUSH tid addr))) ex rs.
Proof.
    induction ex; intros.
    -   inversion Hrs. constructor.
    -   inversion Hrs.
        +   econstructor. apply IHex.
            apply Hmask. intros. apply Hunused. simpl. right. easy.
            apply Hs. apply Hinternal.
        +   econstructor. apply IHex.
            apply Hmask. intros. apply Hunused. simpl. right. easy.
            apply Hs. 
        +   econstructor. apply IHex.
            apply Hmask. intros. apply Hunused. simpl. right. easy.
            apply Hs. unfold get_value in *.
            rewrite update_not_same. apply Hval.
            intro. edestruct Hunused.
            simpl. left. reflexivity.
            subst a. simpl. subst. reflexivity.
        +   econstructor. apply IHex.
            apply Hmask. intros. apply Hunused. simpl. right. easy.
            apply Hs. unfold get_value in *.
            rewrite update_not_same. apply Hval.
            intro. edestruct Hunused.
            simpl. left. reflexivity.
            subst a. simpl. subst. reflexivity.
        +   econstructor. apply IHex.
            apply Hmask. intros. apply Hunused. simpl. right. easy.
            apply Hs. 
        +   econstructor. apply IHex.
            apply Hmask. intros. apply Hunused. simpl. right. easy.
            apply Hs.  
Qed.

Lemma memstate_push_unchanged :
    forall n pl view ms tid addr
        (Hmask : pl view = None)
        (Hms : rel_replay_mem n pl ms),
        rel_replay_mem n (update pl view (Some (PUSH tid addr))) ms.
Proof.
    induction n; intros.
    -   inversion Hms. constructor.
    -   inversion Hms.
        +   econstructor. apply IHn.
            apply Hmask. apply Hlp.
            rewrite update_not_same. apply Hwrite.
            intro. contradict Hwrite. subst. rewrite Hmask. easy.
        +   econstructor. apply IHn.
            apply Hmask. apply Hlp.
            destruct (Peano_dec.eq_nat_dec view (S n)).
            *   subst. rewrite update_same. easy.
            *   rewrite update_not_same by easy. apply Hnotwrite.
Qed.   

Theorem same_mem :
    forall (t : Trace) (gt : list GlobalEvent)
        (Hsc : rel_global_trace t gt)
        (Hvalid : valid_trace t)
        (Hdrf : DRF t)
        ,
        same_result t gt.
Proof.
    intros. induction Hsc.
    -   (* empty *)
        esplit; simpl in *.
        +   apply empty_replay_mem. easy.
        +   intro. apply REPLAY_REG_EMPTY.
        +   apply SC_EMPTY.
        +   simpl. reflexivity.
        +   simpl. easy.
    -   (* internal *)
        assert (same_result t gt) as IHsame.
        {
            apply IHHsc.
            inversion Hvalid. simpl in *.
            -   constructor.
                +   unfold fulfilled in *. simpl in *. intros v Hp.
                    specialize Hfulfilled with v. apply Hfulfilled in Hp.
                    destruct Hp as (tid0 & e & n & Hp1 & Hp2 & Hp3).
                    destruct (promiselist t v) eqn: Heqp; try easy.                
                    destruct (Peano_dec.eq_nat_dec tid tid0).
                    *   subst. rewrite update_same in Hp1.
                        apply nth_error_inv in Hp1 as [|]. 
                        {   destruct H. subst.
                            destruct p; destruct Hp2; try easy.
                            destruct H0. easy.
                        }
                        {exists tid0, e.
                            destruct H as (n0 & Hn01 & Hn02).
                            exists n0.
                            split. easy. split. easy.
                            intros.
                            destruct (Peano_dec.eq_nat_dec tid0 tid').
                             rewrite e0 in *.
                                specialize Hp3 with tid' (S n') e'.
                                rewrite update_same in Hp3. rewrite Hn01 in Hp3.
                                split; auto.
                                assert (S n0 = S n') by now apply Hp3.
                                inversion H. easy.
                             specialize Hp3 with tid' n' e'.
                                rewrite update_not_same in Hp3 by lia.
                                apply Hp3  in He'; easy.
                        }
                    *   rewrite update_not_same in Hp1 by easy.
                        exists tid0, e, n. split. easy.
                        split. easy. intros.
                        destruct (Peano_dec.eq_nat_dec tid tid').
                        {   rewrite <- e0 in *.
                            specialize Hp3 with tid (S n') e'.
                            rewrite update_same in Hp3.
                            contradict n0. symmetry. apply Hp3.
                            simpl. easy. easy.
                        }
                        {   apply Hp3 with e'.
                            rewrite update_not_same by easy. easy. easy.

                        }
                +   intro. specialize Hconsistent with tid0. destruct Hconsistent as (ls1 & Hls1).
                    destruct (Peano_dec.eq_nat_dec tid tid0).
                    *   subst. rewrite update_same in Hls1.
                        inversion Hls1; exists ls; easy.
                    *   rewrite update_not_same in Hls1 by easy.
                        exists ls1. easy.
            -   (* DRF *)
                inversion Hdrf. simpl in *.
                esplit. apply Hglobal.
                intro. specialize Hlocal with tid0. destruct Hlocal as (lo & Hlo).
                destruct (Peano_dec.eq_nat_dec tid tid0).
                  subst. rewrite update_same in Hlo.
                    inversion Hlo. exists lo. easy.
                  rewrite update_not_same in Hlo by easy.
                    exists lo. easy.               
        }
        clear IHHsc. inversion IHsame.
        destruct (execute_internal_exists i (rs tid)) as (r0 & Hr0).
        set (rs0 := update rs tid r0).
        replace r0 with (rs0 tid) in Hr0 by now unfold rs0; rewrite update_same.
        esplit; simpl in *.
        +   apply Hpamem.
        +   intro. specialize Hpareg with tid0.
            destruct (Peano_dec.eq_nat_dec tid tid0).
            *   subst tid0. rewrite update_same.
                econstructor. apply Hpareg.
                apply Hr0.
            *   rewrite update_not_same by easy.
                replace (rs0 tid0) with (rs tid0).
                apply Hpareg. unfold rs0. rewrite update_not_same by easy.
                reflexivity.
        +   constructor. apply Hsc0.
            rewrite Hreg. apply Hr0.
        +   simpl. apply Hms.
        +   simpl. intro. specialize Hreg with tid0.
            destruct (Peano_dec.eq_nat_dec tid tid0).
            *   subst tid0. rewrite update_same. reflexivity.
            *   unfold rs0.
                rewrite update_not_same by easy.
                rewrite update_not_same by easy.
                apply Hreg.
    -   (* oracle *)
        assert (same_result t gt) as IHsame.
        {
            apply IHHsc.
            inversion Hvalid. simpl in *.
            -   constructor.
                +   unfold fulfilled in *. simpl in *. intros v Hp.
                    specialize Hfulfilled with v. apply Hfulfilled in Hp.
                    destruct Hp as (tid0 & e & n & Hp1 & Hp2 & Hp3).
                    destruct (promiselist t v) eqn: Heqp; try easy.                
                    destruct (Peano_dec.eq_nat_dec tid tid0).
                    *   subst. rewrite update_same in Hp1.
                        apply nth_error_inv in Hp1 as [|]. 
                        {   destruct H. subst.
                            destruct p; destruct Hp2; try easy.
                            destruct H0. easy.
                        }
                        {exists tid0, e.
                            destruct H as (n0 & Hn01 & Hn02).
                            exists n0.
                            split. easy. split. easy.
                            intros.
                            destruct (Peano_dec.eq_nat_dec tid0 tid').
                             rewrite e0 in *.
                                specialize Hp3 with tid' (S n') e'.
                                rewrite update_same in Hp3. rewrite Hn01 in Hp3.
                                split; auto.
                                assert (S n0 = S n') by now apply Hp3.
                                inversion H. easy.
                             specialize Hp3 with tid' n' e'.
                                rewrite update_not_same in Hp3 by lia.
                                apply Hp3  in He'; easy.
                        }
                    *   rewrite update_not_same in Hp1 by easy.
                        exists tid0, e, n. split. easy.
                        split. easy. intros.
                        destruct (Peano_dec.eq_nat_dec tid tid').
                        {   rewrite <- e0 in *.
                            specialize Hp3 with tid (S n') e'.
                            rewrite update_same in Hp3.
                            contradict n0. symmetry. apply Hp3.
                            simpl. easy. easy.
                        }
                        {   apply Hp3 with e'.
                            rewrite update_not_same by easy. easy. easy.

                        }
                +   intro. specialize Hconsistent with tid0. destruct Hconsistent as (ls1 & Hls1).
                    destruct (Peano_dec.eq_nat_dec tid tid0).
                    *   subst. rewrite update_same in Hls1.
                        inversion Hls1; exists ls; easy.
                    *   rewrite update_not_same in Hls1 by easy.
                        exists ls1. easy.
            -   (* DRF *)
                inversion Hdrf. simpl in *.
                esplit. apply Hglobal.
                intro. specialize Hlocal with tid0. destruct Hlocal as (lo & Hlo).
                destruct (Peano_dec.eq_nat_dec tid tid0).
                  subst. rewrite update_same in Hlo.
                    inversion Hlo. exists lo. easy.
                  rewrite update_not_same in Hlo by easy.
                    exists lo. easy.               
        }
        clear IHHsc. inversion IHsame.
        set (r0 := update (rs tid) reg val).
        set (rs0 := update rs tid r0).
        esplit; simpl in *.
        +   apply Hpamem.
        +   instantiate (1:=rs0).
            intro. specialize Hpareg with tid0.
            destruct (Peano_dec.eq_nat_dec tid tid0).
            *   subst tid0. rewrite update_same.
                unfold rs0. rewrite update_same.
                econstructor. apply Hpareg.
            *   rewrite update_not_same by easy.
                replace (rs0 tid0) with (rs tid0).
                apply Hpareg. unfold rs0. rewrite update_not_same by easy.
                reflexivity.
        +   constructor. apply Hsc0.
        +   simpl. apply Hms.
        +   simpl. intro. specialize Hreg with tid0.
            destruct (Peano_dec.eq_nat_dec tid tid0).
            *   subst tid0. rewrite update_same. rewrite Hreg.
                unfold rs0. rewrite update_same. easy.
            *   unfold rs0.
                rewrite update_not_same by easy.
                rewrite update_not_same by easy.
                apply Hreg.
    -   (* LOAD *)
        assert (same_result t gt) as IHsame.
        {
            apply IHHsc.
            -   inversion Hvalid. constructor.
                +   unfold fulfilled in *. simpl in *. intros v Hp.
                    specialize Hfulfilled with v. apply Hfulfilled in Hp.
                    destruct Hp as (tid0 & e & n & Hp1 & Hp2 & Hp3).
                    destruct (promiselist t v) eqn: Heqp; try easy.                
                    destruct (Peano_dec.eq_nat_dec tid tid0).
                    *   subst. rewrite update_same in Hp1.
                        apply nth_error_inv in Hp1 as [|]. 
                          destruct H. subst.
                            destruct p; destruct Hp2; try easy.
                            destruct H0. easy.
                          exists tid0, e.
                            destruct H as (n0 & Hn01 & Hn02).
                            exists n0.
                            split. easy. split. easy.
                            intros.
                            destruct (Peano_dec.eq_nat_dec tid0 tid').
                             rewrite e0 in *.
                                specialize Hp3 with tid' (S n') e'.
                                rewrite update_same in Hp3. rewrite Hn01 in Hp3.
                                split; auto.
                                assert (S n0 = S n') by now apply Hp3.
                                inversion H. easy.
                             specialize Hp3 with tid' n' e'.
                                rewrite update_not_same in Hp3 by lia.
                                apply Hp3  in He'; easy.
                    *   rewrite update_not_same in Hp1 by easy.
                        exists tid0, e, n. split. easy.
                        split. easy. intros.
                        destruct (Peano_dec.eq_nat_dec tid tid').
                          rewrite <- e0 in *.
                            specialize Hp3 with tid (S n') e'.
                            rewrite update_same in Hp3.
                            contradict n0. symmetry. apply Hp3.
                            simpl. easy. easy.
                          apply Hp3 with e'.
                            rewrite update_not_same by easy. easy. easy.  
                +   intro. simpl in *.
                    specialize Hconsistent with tid0. destruct Hconsistent as (ls & Hls).
                    destruct (Peano_dec.eq_nat_dec tid tid0).
                    *   subst. rewrite update_same in Hls.
                        inversion Hls. exists ls0. easy.
                    *   rewrite update_not_same in Hls by easy.
                        exists ls. easy.
            -   inversion Hdrf. simpl in *. esplit.
                apply Hglobal.
                intro. specialize Hlocal with tid0.
                destruct (Peano_dec.eq_nat_dec tid tid0).
                +   subst. rewrite update_same in Hlocal.
                    destruct Hlocal as (lo & Hlo).
                    inversion Hlo. exists lo. apply Hlo0.
                +   rewrite update_not_same in Hlocal by easy.
                    apply Hlocal.
        }
        clear IHHsc. inversion IHsame.
        inversion Hvalid.
        destruct (Hconsistent tid) as (ls & Hls). simpl in *.
        rewrite update_same in Hls.
        inversion Hls.
        set (rs0 := update rs tid (update (rs tid) reg val)).
        esplit; simpl in *.
        +   apply Hpamem.
        +   subst.
            instantiate (1:= update rs tid (update (rs tid) reg val)).
            intro. specialize Hpareg with tid0.
            destruct (Peano_dec.eq_nat_dec tid tid0).
            *   subst. simpl in *. rewrite update_same.
                unfold rs0. rewrite update_same.
                constructor. assumption.
                unfold get_value. rewrite Hpromise. easy.
            *   unfold rs0.
                repeat rewrite update_not_same by easy.
                easy.
        +   constructor. apply Hsc0.
        +   easy.
        +   simpl. intro.
            destruct (Peano_dec.eq_nat_dec tid tid1).
            *   rewrite Hreg. rewrite Hms.
                rewrite e.
                repeat rewrite update_same.
                assert (ms addr = val). (* last read *)
                {
                    apply Hlast in Hpamem.
                    unfold get_value in *. rewrite Hpromise in Hpamem.
                    inversion Hpamem. reflexivity.
                }
                subst. easy.
            *   subst.
                repeat rewrite update_not_same by easy. rewrite Hreg. easy.     
    -   (* STORE *)   
        assert (same_result t gt) as IHsame.
        {
            apply IHHsc.
            inversion Hvalid. simpl in *.
            -   constructor.
                +   unfold fulfilled in *. simpl in *. intros v Hp.
                    specialize Hfulfilled with v.
                    destruct (Peano_dec.eq_nat_dec v view).
                    *   rewrite e in *.
                        rewrite Hmask in *. destruct Hp. easy.
                    *   rewrite update_not_same in Hfulfilled by lia.
                        apply Hfulfilled in Hp.
                        destruct Hp as (tid0 & e & n0 & He & Hp1 & Hp2).
                        exists tid0, e.
                        destruct (Peano_dec.eq_nat_dec tid tid0).
                          rewrite <- e0 in *. rewrite update_same in He.
                            apply nth_error_inv in He as [|].
                              destruct H0. subst.
                                destruct (promiselist t v); try easy.
                                destruct p. destruct Hp1 as (_ & reg0 & Hreg).
                                inversion Hreg. contradict n. easy. easy.
                                destruct Hp1. discriminate.
                              destruct H0 as (n' & Hn'1 & Hn'2).
                                exists n'. split. easy. split. easy.
                                intros.
                                destruct (Peano_dec.eq_nat_dec tid tid').
                                  rewrite <- e1 in *.
                                    specialize Hp2 with tid (S n'0) e'.
                                    rewrite update_same in Hp2.
                                    rewrite Hn'1 in *.
                                    assert (S n' = S n'0) by now apply Hp2.
                                    auto.
                                  specialize Hp2 with tid' n'0 e'.
                                    rewrite update_not_same in Hp2 by lia.
                                    contradict n1. apply Hp2. easy. easy.
                          rewrite update_not_same in He by easy.
                            exists n0. split. easy. split. easy.
                            intros. destruct (Peano_dec.eq_nat_dec tid tid').
                              specialize Hp2 with tid (S n') e'. rewrite <- e0 in *.
                                rewrite update_same in Hp2.
                                contradict n1. symmetry. apply Hp2.
                                simpl. easy. easy.
                              specialize Hp2 with tid' n' e'.
                                rewrite update_not_same in Hp2 by easy.
                                apply Hp2. easy. easy.
                +   intro. specialize Hconsistent with tid0. destruct Hconsistent as (ls1 & Hls1).
                    destruct (Peano_dec.eq_nat_dec tid tid0).
                      subst. rewrite update_same in Hls1.
                        inversion Hls1. exists ls.
                        eapply localstate_promise_unused_write.
                          apply Hmask.
                          intros. eapply Hunused. apply H6.
                          apply Hls.
                      rewrite update_not_same in Hls1 by easy.
                        exists ls1.
                        eapply localstate_promise_unused_write.
                        apply Hmask. intros. eapply Hunused. apply H0. apply Hls1.
            -   (* DRF *)
                inversion Hdrf. simpl in *.
                esplit. 
                +   inversion Hglobal. eexists. eapply global_ownership_unused_write.
                    apply Hmask. apply H0. (* last write *)
                +   intro. specialize Hlocal with tid0. destruct Hlocal  as (lo & Hlo).
                    destruct (Peano_dec.eq_nat_dec tid tid0).
                      subst. rewrite update_same in Hlo.
                        inversion Hlo. exists lo0.
                        eapply local_ownership_unused_write. apply Hmask.
                        intros. eapply Hunused. apply H5. subst. apply Hlo0.
                      rewrite update_not_same in Hlo by easy.
                        exists lo.
                        eapply local_ownership_unused_write. apply Hmask.
                        intros. eapply Hunused. apply H0. subst. apply Hlo.        
        }
        clear IHHsc. inversion IHsame.
        esplit; simpl in *.
        +   apply Hlast. apply Hpamem. 
        +   intro. specialize Hpareg with tid0.
            destruct (Peano_dec.eq_nat_dec tid tid0).
            *   subst. rewrite update_same.
                apply REPLAY_REG_STORE. 
                eapply regstate_write_unchanged. apply Hmask.
                intros. eapply Hunused. apply H. apply Hpareg.
                unfold get_value. rewrite update_same.
                inversion Hvalid.
                specialize Hconsistent with tid0. destruct Hconsistent.
                simpl in *. rewrite update_same in H0. inversion H0.
                rewrite update_same in Hpromise. inversion Hpromise.
                erewrite rel_promising_localstate. reflexivity.
                apply Hls. apply regstate_write_unchanged.
                apply Hmask. intro. apply Hunused. easy. 
            *   rewrite update_not_same by easy.
                eapply regstate_write_unchanged. apply Hmask.
                intros. eapply Hunused. apply H1. apply Hpareg.
        +   constructor. apply Hsc0. 
        +   simpl. rewrite Hreg. rewrite Hms.
            replace (rs tid reg) with val. easy.
            inversion Hvalid. specialize Hconsistent with tid.
            destruct Hconsistent. simpl in *. rewrite update_same in H2.
            inversion H2. rewrite update_same in Hpromise. inversion Hpromise.
            erewrite rel_promising_localstate. reflexivity.
            apply Hls. apply regstate_write_unchanged. apply Hmask.
            intro. eapply Hunused. easy.
        +   simpl. intro. specialize Hreg with tid0.
            apply Hreg.
    -   (* ACQ *)
        assert (same_result t gt) as IHsame.
        {
            apply IHHsc.
            inversion Hvalid. simpl in *.
            -   constructor.
                +   unfold fulfilled in *. simpl in *. intros v Hp.
                    specialize Hfulfilled with v.
                    destruct (Peano_dec.eq_nat_dec v view).
                    *   rewrite e in *.
                        rewrite Hmask in *. destruct Hp. easy.
                    *   rewrite update_not_same in Hfulfilled by lia.
                        apply Hfulfilled in Hp.
                        destruct Hp as (tid0 & e & n0 & He & Hp1 & Hp2).
                        exists tid0, e.
                        destruct (Peano_dec.eq_nat_dec tid tid0).
                          rewrite <- e0 in *. rewrite update_same in He.
                            apply nth_error_inv in He as [|].
                              destruct H0. subst.
                                destruct (promiselist t v); try easy.
                                destruct p. destruct Hp1 as (_ & reg & Hreg). discriminate.
                                destruct Hp1. inversion H0. contradict n. easy. easy.
                              destruct H0 as (n' & Hn'1 & Hn'2).
                                exists n'. split. easy. split. easy.
                                intros.
                                destruct (Peano_dec.eq_nat_dec tid tid').
                                  rewrite <- e1 in *.
                                    specialize Hp2 with tid (S n'0) e'.
                                    rewrite update_same in Hp2.
                                    rewrite Hn'1 in *.
                                    assert (S n' = S n'0) by now apply Hp2.
                                    auto.
                                  specialize Hp2 with tid' n'0 e'.
                                    rewrite update_not_same in Hp2 by lia.
                                    contradict n1. apply Hp2. easy. easy.
                          rewrite update_not_same in He by easy.
                            exists n0. split. easy. split. easy.
                            intros. destruct (Peano_dec.eq_nat_dec tid tid').
                              specialize Hp2 with tid (S n') e'. rewrite <- e0 in *.
                                rewrite update_same in Hp2.
                                contradict n1. symmetry. apply Hp2.
                                simpl. easy. easy.
                              specialize Hp2 with tid' n' e'.
                                rewrite update_not_same in Hp2 by easy.
                                apply Hp2. easy. easy.
                +   intro. specialize Hconsistent with tid0. destruct Hconsistent as (ls1 & Hls1).
                    destruct (Peano_dec.eq_nat_dec tid tid0).
                      subst. rewrite update_same in Hls1.
                        inversion Hls1. exists ls. 
                        eapply localstate_promise_unused_pull.
                        apply Hmask. intros. eapply Hunused. apply H5. apply Hls.
                      rewrite update_not_same in Hls1 by easy.
                        exists ls1. eapply localstate_promise_unused_pull.
                        apply Hmask. intros. eapply Hunused. apply H0. apply Hls1.
            -   (* DRF *)
                inversion Hdrf. simpl in *.
                esplit. 
                +   inversion Hglobal. eapply Hlast. apply H0.
                +   intro. specialize Hlocal with tid0. destruct Hlocal as (lo & Hlo).
                    destruct (Peano_dec.eq_nat_dec tid tid0).
                      subst. rewrite update_same in Hlo.
                        inversion Hlo. exists lo0.
                        eapply local_ownership_unused_pull.
                        apply Hmask. intros. eapply Hunused. apply H4.
                        apply Hlo0.
                      rewrite update_not_same in Hlo by easy.
                        exists lo. eapply local_ownership_unused_pull.
                        apply Hmask. intros. eapply Hunused. apply H0. subst. apply Hlo.             
        }
        clear IHHsc. inversion IHsame.
        esplit; simpl in *.
        +   apply memstate_pull_unchanged. apply Hmask. apply Hpamem.
        +   instantiate (1:= rs).
            intro. specialize Hpareg with tid0.
            destruct (Peano_dec.eq_nat_dec tid tid0).
            *   subst. rewrite update_same.
                constructor.
                apply regstate_pull_unchanged. apply Hmask.
                intros. eapply Hunused. apply H. apply Hpareg.
            *   rewrite update_not_same by easy.
                apply regstate_pull_unchanged. apply Hmask.
                intros. eapply Hunused. apply H1. apply Hpareg.
        +   apply Hsc0. 
        +   simpl. apply Hms.
        +   simpl. intro. specialize Hreg with tid0.
            apply Hreg.
    -   (* REL *)
        assert (same_result t gt) as IHsame.
        {
            apply IHHsc.
            inversion Hvalid. simpl in *.
            -   constructor.
                +   unfold fulfilled in *. simpl in *. intros v Hp.
                    specialize Hfulfilled with v.
                    destruct (Peano_dec.eq_nat_dec v view).
                    *   rewrite e in *.
                        rewrite Hmask in *. destruct Hp. easy.
                    *   rewrite update_not_same in Hfulfilled by lia.
                        apply Hfulfilled in Hp.
                        destruct Hp as (tid0 & e & n0 & He & Hp1 & Hp2).
                        exists tid0, e.
                        destruct (Peano_dec.eq_nat_dec tid tid0).
                          rewrite <- e0 in *. rewrite update_same in He.
                            apply nth_error_inv in He as [|].
                              destruct H0. subst.
                                destruct (promiselist t v); try easy.
                                destruct p. destruct Hp1 as (_ & reg & Hreg). discriminate.
                                easy.
                                destruct Hp1. inversion H0. contradict n. easy.
                              destruct H0 as (n' & Hn'1 & Hn'2).
                                exists n'. split. easy. split. easy.
                                intros.
                                destruct (Peano_dec.eq_nat_dec tid tid').
                                  rewrite <- e1 in *.
                                    specialize Hp2 with tid (S n'0) e'.
                                    rewrite update_same in Hp2.
                                    rewrite Hn'1 in *.
                                    assert (S n' = S n'0) by now apply Hp2.
                                    auto.
                                  specialize Hp2 with tid' n'0 e'.
                                    rewrite update_not_same in Hp2 by lia.
                                    contradict n1. apply Hp2. easy. easy.
                          rewrite update_not_same in He by easy.
                            exists n0. split. easy. split. easy.
                            intros. destruct (Peano_dec.eq_nat_dec tid tid').
                              specialize Hp2 with tid (S n') e'. rewrite <- e0 in *.
                                rewrite update_same in Hp2.
                                contradict n1. symmetry. apply Hp2.
                                simpl. easy. easy.
                              specialize Hp2 with tid' n' e'.
                                rewrite update_not_same in Hp2 by easy.
                                apply Hp2. easy. easy.
                +   intro. specialize Hconsistent with tid0. destruct Hconsistent as (ls1 & Hls1).
                    destruct (Peano_dec.eq_nat_dec tid tid0).
                      subst. rewrite update_same in Hls1.
                        inversion Hls1. exists ls.
                        eapply localstate_promise_unused_push.
                        apply Hmask. intros. eapply Hunused. apply H5. rewrite H1. apply Hls.
                      rewrite update_not_same in Hls1 by easy.
                        exists ls1. eapply localstate_promise_unused_push.
                        apply Hmask. intros. eapply Hunused. apply H0. apply Hls1.
            -   (* DRF *)
                inversion Hdrf. simpl in *.
                esplit. 
                +   inversion Hglobal. eapply Hlast. apply H0.
                +   intro. specialize Hlocal with tid0. destruct Hlocal as (lo & Hlo).
                    destruct (Peano_dec.eq_nat_dec tid tid0).
                      subst. rewrite update_same in Hlo.
                        inversion Hlo. exists lo0.
                        eapply local_ownership_unused_push.
                        apply Hmask. intros. eapply Hunused. apply H4.
                        apply Hlo0.
                      rewrite update_not_same in Hlo by easy.
                        exists lo. eapply local_ownership_unused_push.
                        apply Hmask. intros. eapply Hunused. apply H0. subst. apply Hlo.              
        }
        clear IHHsc. inversion IHsame.
        esplit; simpl in *.
        +   apply memstate_push_unchanged. apply Hmask. apply Hpamem.
        +   instantiate (1:=rs).
            intro. specialize Hpareg with tid0.
            destruct (Peano_dec.eq_nat_dec tid tid0).
            *   subst. rewrite update_same.
                constructor.
                apply regstate_push_unchanged. apply Hmask.
                intros. eapply Hunused. apply H. apply Hpareg.
            *   rewrite update_not_same by easy.
                apply regstate_push_unchanged. apply Hmask.
                intros. eapply Hunused. apply H1. apply Hpareg.
        +   apply Hsc0. 
        +   simpl. apply Hms.
        +   simpl. intro. specialize Hreg with tid0.
            apply Hreg.
Qed.
