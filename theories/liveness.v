Require Import Lra.
Require Import Lia.

Require Import PP.Ppsimplmathcomp.
From mathcomp.ssreflect
Require Import all_ssreflect.

From mathcomp.finmap
Require Import finmap.
From mathcomp.finmap
Require Import multiset.
From mathcomp.finmap Require Import order.
Import Order.Theory Order.Syntax Order.Def.

Open Scope mset_scope.
Open Scope fmap_scope.
Open Scope fset_scope.

Require Import Coq.Reals.Reals.
Require Import Coq.Relations.Relation_Definitions.
Require Interval.Interval_tactic.

Require Import Relation_Operators.

From Algorand
Require Import boolp Rstruct R_util fmap_ext.

From Algorand
Require Import local_state global_state.

From Algorand
Require Import algorand_model safety_helpers quorums safety.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** LIVENESS **)

Lemma utr_nomsg_preserves_sensibility : forall uid us us' ms,
  sensible_ustate us -> uid # us ~> (us', ms) ->
  sensible_ustate us'.
Proof.
  let use_hyp H := (unfold valid_rps in H;simpl in H; decompose record H) in
  let tidy _ :=
  (match goal with
    | [ |- context C [ next_deadline (?s + 1 - 1) ] ] =>
      replace (s + 1 - 1) with s by (rewrite addn1;rewrite subn1;symmetry;apply Nat.pred_succ)
    | [ H : is_true (3 < ?s) |- context C [next_deadline ?s] ] =>
      rewrite (step_later_deadlines H)
  end) in
  intros uid us us' ms H_sensible Hstep;
  remember (us',ms) as ustep_output eqn:H_output;
  destruct Hstep; injection H_output; intros; subst;
  match goal with
  | [H_sensible : sensible_ustate ?s |- _] => is_var s;
     destruct s;unfold sensible_ustate in * |- *;
     decompose record H_sensible;clear H_sensible;simpl in * |- *
  end;
  try (
    match goal with
    | [H: propose_ok _ _ _ _ _ _ |- _] => unfold propose_ok in H; use_hyp H
    | [H: repropose_ok _ _ _ _ _ |- _] => unfold repropose_ok in H; use_hyp H
    | [H: no_propose_ok _ _ _ _ |- _] => unfold no_propose_ok in H; use_hyp H
    | [H: softvote_new_ok _ _ _ _ _ |- _] => unfold softvote_new_ok in H; use_hyp H
    | [H: softvote_repr_ok _ _ _ _ _ |- _] => unfold softvote_repr_ok in H; use_hyp H
    | [H: no_softvote_ok _ _ _ _ |- _] => unfold no_softvote_ok in H; use_hyp H
    | [H: certvote_ok _ _ _ _ _ _ |- _] => unfold certvote_ok in H; use_hyp H
    | [H: no_certvote_ok _ _ _ _ |- _] => unfold no_certvote_ok in H; use_hyp H
    | [H: nextvote_val_ok _ _ _ _ _ _ _ |- _] => unfold nextvote_val_ok in H; use_hyp H
    | [H: nextvote_open_ok _ _ _ _ _ _ _ |- _] => unfold nextvote_open_ok in H; use_hyp H
    | [H: nextvote_stv_ok _ _ _ _ _ _ _ /\ _ |- _] => destruct H as [H Hs]; unfold nextvote_stv_ok in H; use_hyp H
    | [H: no_nextvote_ok _ _ _ _ _ |- _] => unfold no_nextvote_ok in H; use_hyp H
    | [H: set_softvotes _ _ _ _ |- _] => unfold set_softvotes in H; use_hyp H
    | [H: certvote_timeout_ok _ _ _ _ |- _] => unfold timout_ok in H; use_hyp H
    | _ => idtac
    end;
    repeat (tidy ());intuition lra).
   - split => //; split => //.
     by admit.
   - split => //; split => //.
     by admit.
   - split => //; split => //.
     by admit.
   - split => //; split => //.
     by admit.
Admitted.

(* The global transition relation preserves sensibility of global states *)
Lemma gtr_preserves_sensibility : forall gs gs',
  sensible_gstate gs -> GTransition gs gs' ->
  sensible_gstate gs'.
Proof using.
  let use_hyp H := (unfold valid_rps in H;simpl in H; decompose record H) in
  intros gs gs' H_sensible Hstep;
  destruct Hstep.

  * destruct pre. unfold tick_update, tick_users. simpl.
    admit.
  * apply utr_msg_preserves_sensibility in H1;
      [|unfold sensible_gstate in H_sensible;decompose record H_sensible;done].
    destruct pre;unfold sensible_gstate in * |- *.
    unfold delivery_result;simpl in * |- *.
    { intuition.
      * move :H5. clear.
        move/(f_equal (fun f => uid \in f)).
        change (uid \in ?f) with (uid \in domf f).
          by rewrite dom_setf fset1U1 in_fset0.
      * admit.
      * rewrite ffunE. simpl.
        set test := (uid0 == uid);destruct test eqn:H_eq;subst test.
        assumption.
        change (uid0 \in ?f) with (uid0 \in domf f) in k.
        rewrite dom_setf in_fset1U H_eq /= in k.
        by rewrite in_fnd;apply H6.
    }
  * apply utr_nomsg_preserves_sensibility in H0;
      [|unfold sensible_gstate in H_sensible;decompose record H_sensible;done].
    destruct pre;unfold sensible_gstate in * |- *.
    unfold step_result;simpl in * |- *.
    { intuition.
      * move:H4; clear.
        move/(f_equal (fun f => uid \in f)).
        change (uid \in ?f) with (uid \in domf f).
          by rewrite dom_setf fset1U1 in_fset0.
      * admit.
      * rewrite ffunE. simpl.
        set test := (uid0 == uid);destruct test eqn:H_eq;subst test.
        assumption.
        change (uid0 \in ?f) with (uid0 \in domf f) in k.
        rewrite dom_setf in_fset1U H_eq /= in k.
        by rewrite in_fnd;apply H5.
    }
  * (* recover from partition *)
    admit.
  * (* make partitioned *)
    admit.
  * (* corrupt user *)
    admit.
  * (* replay message *)
    admit.
  * (* forge message *)
Admitted.

(* Generalization of preservation of sensibility to paths *)
Lemma greachable_preserves_sensibility : forall g0 g,
  greachable g0 g -> sensible_gstate g0 -> sensible_gstate g.
Proof using.
  move => g0 g [p Hp] Hg.
  destruct p. inversion Hp.
  unfold is_trace in Hp.
  destruct Hp as [Hg' Hpath].
  subst g1.
  elim: p g0 g Hg Hpath => /= [g g0 Hg|]; first by rewrite Hg.
  move => g p IH g1 g0 Hl.
  move/andP => [Ht Hp] Hs.
  move/IH: Hp => Hp.
  move/Hp: Hl; apply.
  move: Ht.
  move/asboolP.
  exact: gtr_preserves_sensibility.
Qed.

Lemma at_most_one_certval_in_p
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start: state_before_round r0 g0):
  forall ix g, onth trace ix = Some g ->
  forall uid u, g.(users).[? uid] = Some u ->
  forall r, r0 <= r ->
  forall p v1 v2,
    v1 \in certvals u r p -> v2 \in certvals u r p -> v1 = v2.
Proof.
  clear -H_path H_start.
  move => ix g H_onth uid u H_lookup r H_round p v1 v2.
  unfold certvals, vote_values, soft_weight.
  rewrite !mem_filter.
  move => /andP [Hv1_q Hv1in].
  move => /andP [Hv2_q Hv2in].
  have H_votes_checked := (softvote_credentials_checked H_path H_start H_onth H_lookup H_round).

  have Hq := quorums_s_honest_overlap trace.
  specialize (Hq r p 2 _ _ (H_votes_checked _ _) Hv1_q (H_votes_checked _ _) Hv2_q).

  move: Hq => [softvoter [H_voted_v1 [H_voted_v2 H_softvoter_honest]]].
  assert (softvoted_in_path trace softvoter r p v1) as H_sent_v1. {
  apply (softvotes_sent H_path H_start H_onth H_lookup H_round).
  move:H_voted_v1 => /imfsetP /= [] x /andP [H_x_in].
  unfold matchValue. destruct x. move => /eqP ? /= ?;subst.
  assumption.
  assumption.
  }
  assert (softvoted_in_path trace softvoter r p v2) as H_sent_v2. {
  apply (softvotes_sent H_path H_start H_onth H_lookup H_round).
  move:H_voted_v2 => /imfsetP /= [] x /andP [H_x_in].
  unfold matchValue. destruct x. move => /eqP ? /= ?;subst.
  assumption.
  assumption.
  }
  move: H_sent_v1 => [ix_v1 H_sent_v1].
  move: H_sent_v2 => [ix_v2 H_sent_v2].

  by case:(no_two_softvotes_in_p H_path H_sent_v1 H_sent_v2).
Qed.

(* A user has (re-)proposed a value/block for a given round/period along a
   given path *)
Definition proposed_in_path_at ix path uid r p v b : Prop :=
  exists g1 g2, step_in_path_at g1 g2 ix path /\
    (user_sent uid (Proposal, val v, r, p, uid) g1 g2 /\
     user_sent uid (Block, val b, r, p, uid) g1 g2 \/
     user_sent uid (Reproposal, repr_val v uid p, r, p, uid) g1 g2).

(* A block proposer (potential leader) for a given round/period along a path*)
Definition block_proposer_in_path_at ix path uid r p v b : Prop :=
  uid \in committee r p 1 /\
  valid_block_and_hash b v /\
  proposed_in_path_at ix path uid r p v b.

(* The block proposer (the leader) for a given round/period along a path*)
Definition leader_in_path_at ix path uid r p v b : Prop :=
  block_proposer_in_path_at ix path uid r p v b /\
  forall id, id \in committee r p 1 /\ id <> uid ->
    (credential uid r p 1 < credential id r p 1)%O.

(* a trace is partition-free if it's either empty or it's a valid trace that
   starts at an unparitioned state and does not involve a partitioning
   transition -- Note: not compatible with is_trace above *)

Definition partition_free g0 trace : Prop :=
  is_trace g0 trace /\
  is_unpartitioned g0 /\
  forall n, ~ step_at trace n lbl_enter_partition.

Lemma partition_state : forall g,
  is_unpartitioned g ->
  is_partitioned (make_partitioned g).
Proof.
  intros g unp_H.
  unfold is_unpartitioned,is_partitioned in unp_H.
  unfold is_partitioned, make_partitioned, flip_partition_flag.
  simpl. assumption.
Qed.

(* is_partitioned as a proposition *)
Lemma is_partitionedP : forall g : GState,
  reflect
    (g.(network_partition) = true)
    (is_partitioned g).
Admitted.

Lemma partition_free_step : forall g0 g1,
  is_unpartitioned g0 -> GTransition g0 g1 ->
  ~ related_by lbl_enter_partition g0 g1 ->
  is_unpartitioned g1.
Proof.
intros g0 g1 g0unp_H g0g1step_H notpstep_H.
unfold related_by in notpstep_H. intuition.
unfold make_partitioned in H0. unfold flip_partition_flag in H0. simpl in * |- *.
(* almost all cases are straightforward *)
destruct g0g1step_H ; auto.
(* except recover_from_partitioned, which is handled separately *)
  unfold is_unpartitioned in g0unp_H. rewrite H in g0unp_H. auto.
Qed.

Lemma partition_free_prefix : forall g0 n trace,
  n > 0 ->
  partition_free g0 trace ->
  partition_free g0 (take n trace).
Proof.
Admitted.

Lemma partition_free_suffix : forall g0 n trace,
  n < size trace ->
  partition_free g0 trace ->
  partition_free g0 (drop n trace).
Proof.
Admitted.

(* Whether the effect of a message is recored in the user state *)
Definition message_recorded ustate msg : Prop :=
  match msg with
  | (Block, val b, r,_,_) =>
       b \in ustate.(blocks) r
  | (Proposal, val v, r, p, uid) =>
       exists c, (uid, c, v, true) \in ustate.(proposals) r p
  | (Reproposal, repr_val v uid' p', r, p, uid) =>
       exists c, (uid, c, v, false) \in ustate.(proposals) r p
  | (Softvote, val v, r, p, uid) =>
       (uid, v) \in ustate.(softvotes) r p
  | (Certvote, val v, r, p, uid) =>
       (uid, v) \in ustate.(certvotes) r p
  | (Nextvote_Open, step_val s, r, p, uid) =>
       uid \in ustate.(nextvotes_open) r p s
  | (Nextvote_Val, next_val v s, r, p, uid) =>
       (uid, v) \in ustate.(nextvotes_val) r p s
  | _ => True
  end.

(* The effect of the message is recorded in the state of the target user on or
   before the message's deadline *)
Definition msg_timely_delivered msg deadline gstate target : Prop :=
  Rle gstate.(now) deadline /\
  exists ustate, gstate.(users).[? target] = Some ustate /\
  message_recorded ustate msg.

(* If a message is sent along a partition-free trace, and the trace is long enough,
   then the message is received by all honest users in a timely fashion
 *)
(* Note: this probably needs revision *)
Lemma sent_msg_timely_received : forall sender msg g0 g1 trace,
  let deadline := msg_deadline msg g0.(now) in
    user_sent sender msg g0 g1 ->
    path gtransition g0 (g1 :: trace) ->
    partition_free g0 (g1 :: trace) ->
    Rle deadline (last g0 (g1 :: trace)).(now) ->
    exists ix g, ohead (drop ix (g1 :: trace)) = Some g
      /\ (forall target, target \in honest_users g.(users) ->
            msg_timely_delivered msg deadline g target).
Admitted.


(* If the block proposer of period r.1 is honest, then a certificate for round r
is produced at period r.1 *)
(* Need the assumption of no partition?? *)
Lemma prop_a : forall g0 g1 trace uid r v b,
  path gtransition g0 (g1 :: trace) ->
  partition_free g0 (g0 :: g1 :: trace) ->
  leader_in_path_at 0 (g0 :: g1 :: trace) uid r 1 v b ->
  user_honest_at 0 (g0 :: g1 :: trace) uid ->
  certified_in_period trace r 1 v.
Proof.
intros g0 g1 trace sender r v b tr_H pfree_tr_H leader_H honest_H.
destruct leader_H as [proposer_H crommitte_H].
destruct proposer_H as [poleader_H [vb_H proposed_H]].
destruct proposed_H as [g' prop_sent_H].
destruct prop_sent_H as [g'' [prop_step_H prop_sent_H]]. destruct prop_step_H. subst.
  (* Need to identify: - the step and state at which the message is received
                      - the user who is receiving the message *)
destruct prop_sent_H as [propsent_H | repropsent_H].
  destruct propsent_H as [propsent_H blocksent_H].
  pose proof (@sent_msg_timely_received sender (Proposal, val v, r, 1, sender) g' g'' trace). simpl in * |- *.
Admitted.


(* If some period r.p, p >= 2 is reached with unique starting value bot and the
   leader is honest, then the leader’s proposal is certified. *)
(* TODO: all users need starting value bot or just leader? *)
Lemma prop_c : forall ix path uid r p v b,
  p >= 2 ->
  all (fun u => user_stv_val_at ix path u p None) (domf (users_at ix path)) ->
  leader_in_path_at ix path uid r 1 v b ->
  user_honest_at ix path uid ->
  certified_in_period path r p v.
Admitted.

(* softvote quorum of all honest users implies certvote quorum *)
Lemma honest_softvote_quorum_implies_certvote : forall (softvote_quorum : {fset UserId}) ix path r p v,
  (forall voter : UserId, voter \in softvote_quorum ->
                                    voter \in domf (honest_users (users_at ix path))) ->
  softvote_quorum `<=` committee r p 3 ->
  tau_c <= #|softvote_quorum| ->
  (forall voter : UserId, voter \in softvote_quorum
                                    -> softvoted_in_path_at ix path voter r p v) ->
  (forall voter : UserId, voter \in softvote_quorum
                                    -> certvoted_in_path path voter r p v).
Proof.
Abort.

(* Honest user softvotes starting value *)
Lemma stv_not_bot_softvote : forall ix path r p v uid,
  uid \in domf (honest_users (users_at ix path)) ->
  user_stv_val_at ix path uid p (Some v) ->
  softvoted_in_path_at ix path uid r p v.
Abort.

(* If some period r.p with p >= 2 is reached, and all honest users have starting
   value H(B), then a certificate for H(B) that period is produced by the honest
   users. *)
(* TODO: need to say quorum for certificate is only *honest* users? *)
Lemma prop_e : forall ix path r p v b,
  p >= 2 ->
  all (fun u => user_stv_val_at ix path u p (Some v))
      (domf (honest_users (users_at ix path))) ->
  valid_block_and_hash b v ->
  certified_in_period path r p v.
Proof.
  intros.
  exists (domf (honest_users (users_at ix path))).
  (* quorum subset of committee at step 3 *)
  assert (domf (honest_users (users_at ix path)) `<=` committee r p 3) by admit.
  (* at least t_H honest users *)
  assert (tau_c <= #|domf (honest_users (users_at ix path))|) by admit.
  repeat split; try assumption.
Admitted.

(* If any honest user is in period r.p with starting value bottom, then within
time (2*lambda+Lambda), every honest user in period r.p will either certify a
value (i.e., will get a certificate) or move to the next period *)
Lemma prop_f : forall r p g0 g1 g2 path_seq uid,
    path gtransition g0 path_seq ->
    g2 = last g0 path_seq ->
    g1 = last g0 (drop 1 path_seq) ->
    user_honest uid g1 ->
    user_stv_val uid g1 p None ->
    (exists v, certvoted_in_path path_seq uid r p v
               \/ period_advance_at 1 path_seq uid r p g1 g2) .
Admitted.
