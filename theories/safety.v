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

Require Import Relation_Operators.

From Algorand
Require Import boolp Rstruct R_util fmap_ext.

From Algorand
Require Import local_state global_state.

From Algorand
Require Import algorand_model safety_helpers quorums.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ----------------------------- *)
(* Round does not contain a fork *)
(* ----------------------------- *)

(* To show there is not a fork in a particular round, we will take a history
   that extends before any honest node has made a transition in that round *)
Definition user_before_round r (u : UState) : Prop :=
  (u.(round) < r \/
   (u.(round) = r /\
    u.(step) = 1 /\ u.(period) = 1 /\ u.(timer) = 0%R /\ u.(deadline) = 0%R))
  /\ (forall r' p, r <= r' -> nilp (u.(proposals) r' p))
  /\ (forall r', r <= r' -> nilp (u.(blocks) r'))
  /\ (forall r' p, r <= r' -> nilp (u.(softvotes) r' p))
  /\ (forall r' p, r <= r' -> nilp (u.(certvotes) r' p))
  /\ (forall r' p s, r <= r' -> nilp (u.(nextvotes_open) r' p s))
  /\ (forall r' p s, r <= r' -> nilp (u.(nextvotes_val) r' p s)).

Definition users_before_round (r:nat) (g : GState) : Prop :=
  forall i (Hi : i \in g.(users)), user_before_round r (g.(users).[Hi]).

Definition messages_before_round (r:nat) (g : GState) : Prop :=
  forall (mailbox: {mset R * Msg}), mailbox \in codomf (g.(msg_in_transit)) ->
  forall deadline msg, (deadline,msg) \in mailbox ->
     msg_round msg < r.

Definition state_before_round r (g:GState) : Prop :=
  users_before_round r g
  /\ messages_before_round r g
  /\ (forall msg, msg \in g.(msg_history) -> msg_round msg < r).

(* ------------------------------------------------------ *)
(* Lemmas connecting pending, sent, and received messages *)
(* ------------------------------------------------------ *)

(* The two main lemmas proved in this section are pending_sent_or_forged and
   received_was_sent. The former connects a message in transit to a previously
   sent (or forged) message. The latter, which relies on the proof of
   pending_sent_or_forged, states that if a message was received, and the sender
   field of that message was a user who is honest, then that user must have sent
   that message at some point earlier in the trace *)

(* message in history was sent - used in pending_sent_or_forged *)
Lemma replay_had_original
      g0 trace (H_path: is_trace g0 trace)
      r (H_start: state_before_round r g0):
  forall g ix, onth trace ix = Some g ->
  forall (msg:Msg), msg \in g.(msg_history) ->
    r <= msg_round msg ->
    exists send_ix, user_sent_at send_ix trace (msg_sender msg) msg.
Proof using.
  clear -H_path H_start.
  move => g ix H_g msg H_msg H_r.
  pose proof (path_gsteps_onth H_path H_g (P:=fun g => msg \in g.(msg_history))).
  cbv beta in H.
  have H_msg0: msg \notin g0.(msg_history)
    by clear -H_start H_r;apply/negP => H_msg;
       move: H_start => [] _ [] _ {H_msg}/(_ _ H_msg);rewrite ltnNge H_r.

  move:(H H_msg0 H_msg). clear -H_path.
  move => [n [g1 [g2 [H_step [H_pre H_post]]]]].
  exists n, g1, g2;split;[assumption|].
  apply (transition_from_path H_path), transitions_labeled in H_step.
  move: H_step => [lbl H_rel];clear -H_pre H_post H_rel.
  destruct lbl;
    try (exfalso;apply /negP: H_post;
         simpl in H_rel;decompose record H_rel;clear H_rel;subst g2;
         simpl;assumption).
  * (* deliver *)
    unfold user_sent.
    suff: s = msg_sender msg /\ msg \in l.
    move => [<- H_l].
    exists l;split;[|left;exists r, m];assumption.
    simpl in H_rel;decompose record H_rel;clear H_rel.
    move: H_post H_pre;subst g2.
    rewrite in_msetD.
    move=> /orP []; [by move => Hp Hn;exfalso;apply/negP: Hp|].
    rewrite in_seq_mset.
    move => H_l. split;[|assumption].
    by apply (utransition_msg_sender_good H H_l).
  * (* internal *)
    unfold user_sent.
    suff: s = msg_sender msg /\ msg \in l.
    move => [<- H_l].
    exists l;split;[|right];assumption.
    simpl in H_rel;decompose record H_rel;clear H_rel.
    move: H_post H_pre;subst g2.
    rewrite in_msetD.
    move=> /orP [];
      [by move => Hp Hn;exfalso;apply/negP: Hp|].
    rewrite in_seq_mset.
    move => H_l. split;[|assumption].
    by apply (utransition_internal_sender_good H0 H_l).
Qed.

(* Pending message was sent or forged earlier in trace *)
Lemma pending_sent_or_forged
      g0 trace (H_path: is_trace g0 trace)
      r (H_start: state_before_round r g0):
    forall g_pending pending_ix,
      onth trace pending_ix = Some g_pending ->
    forall uid (key_msg : uid \in g_pending.(msg_in_transit)) d pending_msg,
      (d,pending_msg) \in g_pending.(msg_in_transit).[key_msg] ->
    let sender := msg_sender pending_msg in
    r <= msg_round pending_msg ->
    exists send_ix g1 g2, step_in_path_at g1 g2 send_ix trace
      /\ (user_sent sender pending_msg g1 g2
          \/ user_forged pending_msg g1 g2).
Proof using.
  clear -H_path H_start.
  intros g_pending pending_ix H_g uid key_msg d msg H_msg sender H_round.
  subst sender.
  set P := fun g => match g.(msg_in_transit).[? uid] with
                  | Some msg_mset => has (fun (p:R*Msg) => p.2 == msg) msg_mset
                  | None => false
                    end.
  have H_P: P g_pending by rewrite /P in_fnd;apply/hasP;exists (d,msg).
  have H_P0: ~~P g0.
  {
  unfold P;simpl.
  clear -H_start H_round.
  case Hmb: (_.[?uid]) => [mb|//].
  move: H_start => [_ [H_msgs _]].
  rewrite leqNgt in H_round.
  apply/contraNN: H_round.

  move /hasP =>[[d msg'] H_in /eqP /= ?];subst msg'.
  apply: H_msgs H_in.
  by apply/codomfP;exists uid.
  }
  (* msg has round >= r, while g0 comes before r, and so msg \notin mmailbox0 *)
  (* if the user does not have a mailbox, then it's already true*)
  move: {H_P0 H_P}(path_gsteps_onth H_path H_g H_P0 H_P).
  subst P;cbv beta.

  move => [n [g1 [g2 [H_step [H_pre H_post]]]]].

  move: (H_step) => /(transition_from_path H_path) /transitions_labeled [lbl H_rel].
  destruct lbl.
    (* tick *)
    exfalso;apply /negP: H_post;simpl in H_rel;decompose record H_rel;clear H_rel;subst g2;
      simpl;assumption.
    (* deliver *)
    exists n,g1,g2;split;[assumption|].
    left. unfold user_sent.
    suff: s = msg_sender msg /\ msg \in l
      by move => [<- H_l];exists l;split;[|left;exists r0, m];assumption.

    simpl in H_rel;decompose record H_rel;clear H_rel.
    suff: msg \in l by split;[apply (utransition_msg_sender_good H)|];assumption.
    move: H_post H_pre;subst g2;apply broadcasts_prop;
    by rewrite fnd_set;case:ifP => [/eqP ->|_];
                                     [rewrite in_fnd;exact:msubD1set|exact:msubset_refl].
    (* internal *)
    exists n,g1,g2;split;[assumption|].
    left. unfold user_sent.
    suff: s = msg_sender msg /\ msg \in l by
        move => [<- H_l];exists l;split;[|right];assumption.

    simpl in H_rel;decompose record H_rel;clear H_rel.
    suff: msg \in l by split;[apply (utransition_internal_sender_good H0)|];assumption.
    move: H_post H_pre;subst g2;apply broadcasts_prop;
    by apply msubset_refl.
    (* exit partition *)
    exfalso. apply /negP: H_post. simpl in H_rel;decompose record H_rel;clear H_rel. subst g2.
    unfold recover_from_partitioned, reset_msg_delays.
    (* reset_msg_delays preserves the set of messages, but not their deadlines *)
    apply/contraNN:H_pre;clear.
    cbn -[eq_op] => H_post.
    case:fndP => H_in;move:H_post;
       [rewrite updf_update //
       |by rewrite not_fnd //;
           change (uid \notin ?f) with (uid \notin domf f);
        rewrite -updf_domf].
    by rewrite /reset_user_msg_delays map_mset_has (eq_has (a2:=(fun p => p.2 == msg))).
    (* enter partition *)
    exfalso;apply /negP: H_post;simpl in H_rel;decompose record H_rel;clear H_rel;subst g2;
      simpl;assumption.
    (* corrupt user *)
    exfalso;apply /negP: H_post;simpl in H_rel;decompose record H_rel;clear H_rel;subst g2.
    unfold corrupt_user_result, drop_mailbox_of_user; simpl.
    (* the empty msg mset cannot have a message *)
    set m1 := (msg_in_transit g1).[? s].
    by destruct m1;[rewrite fnd_set;case:ifP;[rewrite enum_mset0|]|].
    (* replay a message *)
    (* replayed message must have originally been sent honestly *)
    rename s into target.
    move: H_rel => /= [ustate_key [hist_msg [H_tgt_honest [H_msg_history H_g2]]]].
    pose proof (replay_had_original H_path H_start (step_in_path_onth_pre H_step) H_msg_history).
    move: H.
    suff ->: hist_msg = msg.
    move/(_ H_round) => [send_ix [g3 [g4]]];clear => H. exists send_ix, g3, g4.
    tauto.
    subst g2.
    symmetry; apply /eqP. rewrite -mem_seq1.
    apply/broadcasts_prop: H_post H_pre.
    apply msubset_refl.
    (* forge a message *)
    exists n,g1,g2;split;[assumption|].
    right.
    unfold user_forged.
    suff ->: msg = (m,e,n0,n1,s) by assumption.
    simpl in H_rel;decompose record H_rel;clear H_rel;subst g2.
    apply/eqP;rewrite -mem_seq1.
    apply/broadcasts_prop: H_post H_pre.
    apply msubset_refl.
Qed.

(* A message from an honest user was actually sent in the trace. Used to relate
   an honest user having received a quorum of messages to some honest user
   having sent those messages - used in received_was_sent *)
(* TODO: hopefully the statement can be cleaned up *)
Lemma pending_honest_sent: forall g0 trace (H_path: is_trace g0 trace),
    forall r, state_before_round r g0 ->
    forall g_pending pending_ix,
      onth trace pending_ix = Some g_pending ->
    forall uid (key_msg : uid \in g_pending.(msg_in_transit)) d pending_msg,
      (d,pending_msg) \in g_pending.(msg_in_transit).[key_msg] ->
    let sender := msg_sender pending_msg in
    honest_during_step (msg_step pending_msg) sender trace ->
    r <= msg_round pending_msg ->
    exists send_ix, user_sent_at send_ix trace sender pending_msg.
Proof using.
  clear.
  move => g0 trace H_path r H_start g ix H_g
             uid key_msg d msg H_msg sender H_honest H_round.
  have [send_ix [g1 [g2 [H_step H_send]]]]
    := pending_sent_or_forged H_path H_start H_g H_msg H_round.
  exists send_ix, g1, g2.
  split;[assumption|].
  case:H_send => [//|H_forged];exfalso.
  destruct msg as [[[[mty v] r1] p] forger].
  rewrite /user_forged /= in H_forged;decompose record H_forged;clear H_forged.
  move:H => [H_corrupt H_le].
  have {H_honest} := all_onth H_honest (step_in_path_onth_pre H_step).
  rewrite /upred' (in_fnd x) H_corrupt implybF => /negP;apply;apply /step_leP.
  refine (step_le_trans H_le _).
  apply/step_leP;rewrite /msg_step /step_leb !eq_refl !ltnn /=.
  have: mtype_matches_step mty v x0 by assumption.
  by clear;destruct mty,v;simpl;destruct 1.
Qed.

(* This lemma connects message receipt to the sending of a message, used to
   reach back to an earlier honest transition. *)
Lemma received_was_sent g0 trace (H_path: is_trace g0 trace)
    r0 (H_start: state_before_round r0 g0)
    u d msg (H_recv: msg_received u d msg trace):
    let: (_,_,r,_,sender) := msg in
    r0 <= r ->
    honest_during_step (msg_step msg) (sender:UserId) trace ->
    exists ix, user_sent_at ix trace sender msg.
Proof using.
  clear -H_path H_start H_recv.
  move: H_recv => [ix_r [ms H_deliver]].
  rewrite {1}[msg]surjective_pairing
          [msg.1]surjective_pairing
          [msg.1.1]surjective_pairing
          [msg.1.1.1]surjective_pairing.
  set msg_r := msg.1.1.2.
  set sender := msg.2.
  move => H_round H_honest_sender.

  move:H_deliver => [g1_d [g2_d [H_step_d H_rel_d]]].
  have {H_step_d}H_g1_d := step_in_path_onth_pre H_step_d.

  move:H_rel_d => [ukey1 [upost H_step]].
  move:H_step => [H_ustep] [H_honest_recv] [key_mailbox] [H_msg_in H_g2_d].
  clear g2_d H_g2_d.

  pose proof (pending_honest_sent H_path H_start H_g1_d H_msg_in) as H.
  specialize (H H_honest_sender H_round).
  exact H.
Qed.

(* Now we have lemmas showing that transitions preserve various invariants *)

(* ------------------- *)
(* Uniqueness of votes *)
(* ------------------- *)

(* a user can only certvote one value during given round/period *)
Lemma vote_value_unique uid r p g1 g2 v:
  user_sent uid (Certvote,val v,r,p,uid) g1 g2 ->
  user_honest uid g1 ->
  forall v2, user_sent uid (Certvote,val v2,r,p,uid) g1 g2 -> v2 = v.
Proof using.
  move => H_sent H_honest v2 H_sent2.
  unfold user_sent in H_sent, H_sent2.
  destruct H_sent as [ms [H_msg [[d1 [in1 H_step]]|H_step]]];
  destruct H_sent2 as [ms2 [H_msg2 [[d2 [in2 H_step2]]|H_step2]]];
  pose proof (transition_label_unique H_step H_step2) as H;
  try (discriminate H);[injection H as -> -> ->|injection H as ->];clear H_step2;
    revert H_msg H_msg2;simpl in H_step;decompose record H_step;
    let H:=  match goal with
    | [H : _ # _ ; _ ~> _ |- _] => H
    | [H : _ # _ ~> _ |- _] => H
    end
    in clear -H;set result := (x0,ms) in H;change ms with result.2;clearbody result;revert H;
  destruct 1;simpl;clear;move/Iter.In_mem => H_msg;try (exfalso;exact H_msg);
     move/Iter.In_mem => H_msg2;simpl in H_msg, H_msg2;intuition congruence.
Qed.

(* a user can only softvote one value during given round/period *)
Lemma softvote_value_unique uid r p g1 g2 v:
  user_sent uid (Softvote,val v,r,p,uid) g1 g2 ->
  user_honest uid g1 ->
  forall v2, user_sent uid (Softvote,val v2,r,p,uid) g1 g2 ->
  v2 = v.
Proof using.
  move => H_sent H_honest v2 H_sent2.
  unfold user_sent in H_sent, H_sent2.
  destruct H_sent as [ms [H_msg [[d1 [in1 H_step]]|H_step]]];
  destruct H_sent2 as [ms2 [H_msg2 [[d2 [in2 H_step2]]|H_step2]]];
  pose proof (transition_label_unique H_step H_step2) as H;
  try (discriminate H);[injection H as -> -> ->|injection H as ->];clear H_step2;
    revert H_msg H_msg2;simpl in H_step;decompose record H_step;
    let H:=  match goal with
    | [H : _ # _ ; _ ~> _ |- _] => H
    | [H : _ # _ ~> _ |- _] => H
    end
    in clear -H;set result := (x0,ms) in H;change ms with result.2;clearbody result;revert H;
  destruct 1;simpl;clear;move/Iter.In_mem => H_msg;try (exfalso;exact H_msg);
     move/Iter.In_mem => H_msg2;simpl in H_msg, H_msg2;intuition congruence.
Qed.

(* ---------------------------------------------- *)
(* Pre- and post-conditions for user sending vote *)
(* ---------------------------------------------- *)

(* user sends softvote -> softvote_new_ok or softvote_repr_ok must have held *)
Lemma softvote_precondition g1 g2 uid v r p
  (H_sent: user_sent uid (Softvote, val v, r, p, uid) g1 g2)
  u (H_u: g1.(users).[?uid] = Some u):
  softvote_new_ok u uid v r p
   \/ softvote_repr_ok u uid v r p.
Proof using.
  clear -H_sent H_u.
  destruct H_sent as [ms [H_msg [[d1 [in1 H_step]]|H_step]]];
    simpl in H_step;decompose record H_step;clear H_step;
    move: H_msg;change ms with (x0,ms).2;
      match goal with
      | [H: _ # _ ~> _ |- _] => move: (x0,ms) H => result
      | [H: _ # _ ; _ ~> _ |- _] => move: (x0,ms) H => result
      end;subst;
  rewrite in_fnd in H_u;case:H_u => ->;clear.
  * (* no message delivery cases *)
    by destruct 1.
  * (* internal transition cases *)
    by destruct 1;try exact;rewrite mem_seq1 => /eqP [-> -> ->];[left|right].
Qed.

(* user sends certvote -> certvote_ok must have held. In case where certvote
   came from message delivery transition, need additional information about how
   the user state changes for the user who sent the certvote. *)
Lemma certvote_precondition g1 g2 uid v r p:
  user_sent uid (Certvote, val v, r, p, uid) g1 g2 ->
  forall u, g1.(users).[?uid] = Some u ->
  (exists i b,
      certvote_ok (set_softvotes u r p (i, v)) uid v b r p
      /\ g2.(users).[?uid] =
         Some (certvote_result (set_softvotes u r p (i, v)))) \/
  (exists b, certvote_ok u uid v b r p).
Proof.
  move => H_sent u H_u.
  destruct H_sent as [ms [H_msg [[d1 [in1 H_step]]|H_step]]].
  * { (* message delivery cases *)
      destruct H_step as (key_ustate & ustate_post & H_step & H_honest
                          & key_mailbox & H_msg_in_mailbox & ->).
      assert ((global_state.users UserId UState [choiceType of Msg] g1) [` key_ustate] = u).
      rewrite in_fnd in H_u; inversion H_u; trivial.
      rewrite H in H_step; clear H.
      remember (ustate_post,ms) as ustep_out in H_step.
      destruct H_step; injection Hequstep_out; clear Hequstep_out;
      intros <- <-; revert H_msg; move/Iter.In_mem => H_msg; try contradiction.
      simpl in H_msg; destruct H_msg; try contradiction; inversion H0.
      left. exists i, b; split; subst; auto.
      rewrite fnd_set eq_refl. auto.
    }
  * { (* internal transition cases *)
      destruct H_step as (key_user & ustate_post & H_honest & H_step & ->).
      remember (ustate_post,ms) as ustep_out in H_step.
      assert ((global_state.users UserId UState [choiceType of Msg] g1) [` key_user] = u).
      rewrite in_fnd in H_u; inversion H_u; trivial.
      rewrite H in H_step. clear H.
      destruct H_step; injection Hequstep_out; clear Hequstep_out;
        intros <- <-; revert H_msg; move/Iter.In_mem => H_msg; try contradiction;
      simpl in H_msg; destruct H_msg as [H_msg | H_msg]; try contradiction;
      try destruct H_msg as [H_msg | H_msg]; inversion H_msg.
      by right; exists b; subst.
    }
Qed.

(* user sent certvote -> in resulting state, the value is in the users certvals,
value corresponds to a block in user's blocks, and user is in step 4 *)
Lemma certvote_postcondition uid v r p g1 g2:
  user_sent uid (Certvote,val v,r,p,uid) g1 g2 ->
  forall u, g2.(users).[?uid] = Some u ->
  v \in certvals u r p /\
        (exists b, b \in u.(blocks) r /\ valid_block_and_hash b v)
  /\ valid_rps u r p 4.
Proof using.
  move => H_sent u H_u.
  destruct H_sent as [ms [H_msg [[d1 [in1 H_step]]|H_step]]].
  (* need to grab u *)
  * { (* message delivery cases *)
      destruct H_step as (key_ustate & ustate_post & H_step & H_honest
                          & key_mailbox & H_msg_in_mailbox & ->).
      remember (ustate_post,ms) as ustep_out in H_step.
      destruct H_step; injection Hequstep_out; clear Hequstep_out;
      intros <- <-; revert H_msg; move/Iter.In_mem => H_msg; try contradiction.
      simpl in H_msg; destruct H_msg; try contradiction.
      inversion H0;subst;clear H0.
      unfold certvote_ok in H;decompose record H;clear H.
      rewrite fnd_set eq_refl in H_u. case: H_u => {u}<-.
      unfold certvote_result.
      by (split;[|split]);
        [
        |exists b;split
        |move:H0 =>-[? [? ?]];split;[|split;[|reflexivity]]].
    }
  * { (* internal transition cases *)
      destruct H_step as (key_user & ustate_post & H_honest & H_step & ->).
      remember (ustate_post,ms) as ustep_out in H_step.
      destruct H_step; injection Hequstep_out; clear Hequstep_out;
        intros <- <-; move/Iter.In_mem in H_msg; try contradiction;
      simpl in H_msg; destruct H_msg as [H_msg | H_msg]; try contradiction;
      try destruct H_msg as [H_msg | H_msg]; inversion H_msg;subst;clear H_msg.
      rewrite fnd_set eq_refl in H_u. case:H_u => H_u.
      subst.
      unfold certvote_ok in H;decompose record H;clear H.
      by (split;[|split]);
        [|exists b;split
         |move:H0 =>-[? [? ?]]].
    }
Qed.

(* user sent nextvote open -> nextvote_open_ok must have held *)
Lemma nextvote_open_precondition g1 g2 uid r p s:
  user_sent uid (Nextvote_Open, step_val s, r, p, uid) g1 g2 ->
  forall u, g1.(users).[?uid] = Some u ->
  nextvote_open_ok u uid r p s.
Proof using.
  move => H_sent u H_u.
  destruct H_sent as [ms [H_msg [[d1 [in1 H_step]]|H_step]]].
  * { (* message delivery cases *)
      destruct H_step as (key_ustate & ustate_post & H_step & H_honest
                          & key_mailbox & H_msg_in_mailbox & ->).
      remember (ustate_post,ms) as ustep_out in H_step.
      destruct H_step; injection Hequstep_out; clear Hequstep_out;
      intros <- <-; revert H_msg; move/Iter.In_mem => H_msg; try contradiction.
      simpl in H_msg; destruct H_msg; try contradiction; inversion H0.
    }
  * { (* internal transition cases *)
      destruct H_step as (key_user & ustate_post & H_honest & H_step & ->).
      remember (ustate_post,ms) as ustep_out in H_step.
      assert ((global_state.users UserId UState [choiceType of Msg] g1) [` key_user] = u).
      rewrite in_fnd in H_u; inversion H_u; trivial.
      rewrite H in H_step. clear H.
      destruct H_step; injection Hequstep_out; clear Hequstep_out;
        intros <- <-; revert H_msg; move/Iter.In_mem => H_msg; try contradiction;
      simpl in H_msg; destruct H_msg as [H_msg | H_msg]; try contradiction;
      try destruct H_msg as [H_msg | H_msg]; inversion H_msg.
      subst; assumption.
    }
Qed.

(* user sent nextvote val -> nextvote_val_ok must have held *)
Lemma nextvote_val_precondition g1 g2 uid v r p s:
  user_sent uid (Nextvote_Val, next_val v s, r, p, uid) g1 g2 ->
  forall u, g1.(users).[?uid] = Some u ->
  (exists b, nextvote_val_ok u uid v b r p s) \/
  (nextvote_stv_ok u uid r p s /\ u.(stv) p = Some v).
Proof.
  move => H_sent u H_u.
  destruct H_sent as [ms [H_msg [[d1 [in1 H_step]]|H_step]]].
  * { (* message delivery cases *)
      destruct H_step as (key_ustate & ustate_post & H_step & H_honest
                          & key_mailbox & H_msg_in_mailbox & ->).
      remember (ustate_post,ms) as ustep_out in H_step.
      destruct H_step; injection Hequstep_out; clear Hequstep_out;
      intros <- <-; revert H_msg; move/Iter.In_mem => H_msg; try contradiction.
      simpl in H_msg; destruct H_msg; try contradiction; inversion H0.
    }
  * { (* internal transition cases *)
      destruct H_step as (key_user & ustate_post & H_honest & H_step & ->).
      remember (ustate_post,ms) as ustep_out in H_step.
      assert ((global_state.users UserId UState [choiceType of Msg] g1) [` key_user] = u).
      rewrite in_fnd in H_u; inversion H_u; trivial.
      rewrite H in H_step. clear H.
      destruct H_step; injection Hequstep_out; clear Hequstep_out;
        intros <- <-; revert H_msg; move/Iter.In_mem => H_msg; try contradiction;
      simpl in H_msg; destruct H_msg as [H_msg | H_msg]; try contradiction;
      try destruct H_msg as [H_msg | H_msg]; inversion H_msg.
      left; exists b; subst; assumption.
      right;subst;assumption.
    }
Qed.

(* -------------------------------- *)
(* Voting for one value in a period *)
(* -------------------------------- *)

(* An honest user cert-votes for at most one value in a period *)
(* In any global state, an honest user either never certvotes in a period or
   certvotes once in step 3 and never certvotes after that during that period. *)
Lemma no_two_certvotes_in_p : forall g0 trace (H_path : is_trace g0 trace) uid r p,
    forall ix1 v1, certvoted_in_path_at ix1 trace uid r p v1 ->
                   user_honest_at ix1 trace uid ->
    forall ix2 v2, certvoted_in_path_at ix2 trace uid r p v2 ->
                   user_honest_at ix2 trace uid ->
                   ix1 = ix2 /\ v1 = v2.
Proof using.
  move => g0 trace H_path uid r p.
  move => ix1 v1 H_send1 H_honest1.
  move => ix2 v2 H_send2 H_honest2.

  have: ix1 <= ix2 by
  eapply (order_sends H_path H_send1 H_send2 (step_le_refl _)).
  have: ix2 <= ix1 by
  eapply (order_sends H_path H_send2 H_send1 (step_le_refl _)).

  move => H_le1 H_le2.
  have: ix1 = ix2.
  apply/eqP. rewrite eqn_leq. apply/andP. split;assumption.
  intro;subst ix2;clear H_le1 H_le2.
  split;[reflexivity|].

  unfold certvoted_in_path_at in H_send1, H_send2.
  destruct H_send1 as [pre1 [post1 [H_step1 H_send1]]].
  destruct H_send2 as [pre2 [post2 [H_step2 H_send2]]].

  destruct (step_ix_same H_step1 H_step2) as [-> ->].
  symmetry.
  refine (vote_value_unique H_send1 _ H_send2).
  exact (at_step_onth H_honest1 (step_in_path_onth_pre H_step1)).
Qed.

(* An honest user soft-votes for at most one value in a period *)
Lemma no_two_softvotes_in_p : forall g0 trace (H_path : is_trace g0 trace) uid r p,
    forall ix1 v1, softvoted_in_path_at ix1 trace uid r p v1 ->
    forall ix2 v2, softvoted_in_path_at ix2 trace uid r p v2 ->
                   ix1 = ix2 /\ v1 = v2.
Proof using.
  clear.
  move => g0 trace H_path uid r p.
  move => ix1 v1 H_send1 ix2 v2 H_send2.

  have: ix1 <= ix2 by
  eapply (order_sends H_path H_send1 H_send2 (step_le_refl _)).
  have: ix2 <= ix1 by
  eapply (order_sends H_path H_send2 H_send1 (step_le_refl _)).

  move => H_le1 H_le2.
  have: ix1 = ix2.
  apply/eqP. rewrite eqn_leq. apply/andP. split;assumption.
  intro;subst ix2;clear H_le1 H_le2.
  split;[reflexivity|].

  unfold softvoted_in_path_at in H_send1, H_send2.
  destruct H_send1 as [pre1 [post1 [H_step1 H_send1]]].
  destruct H_send2 as [pre2 [post2 [H_step2 H_send2]]].

  destruct (step_ix_same H_step1 H_step2) as [-> ->].
  symmetry.
  refine (softvote_value_unique H_send1 _ H_send2).
  (* honesty follows from user_sent *)
  destruct H_send1 as [ms' [H_msg' [[d1' [in1' H_step']]|H_step']]].
    destruct H_step' as (key_ustate' & ustate_post' & H_step' & H_honest' & key_mailbox' & H_msg_in_mailbox' & ->).
    unfold user_honest. rewrite in_fnd. intuition.
  destruct H_step' as (key_user' & ustate_post' & H_honest' & H_step' & ->).
  unfold user_honest. rewrite in_fnd. intuition.
Qed.

(* ----------------------------------------- *)
(* Votes present in user state were received *)
(* ----------------------------------------- *)

(* vote in users softvote set -> softvote was received *)
Lemma received_softvote
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start: state_before_round r0 g0)
      ix g (H_last: onth trace ix = Some g) :
  forall uid u,
    (global_state.users UserId UState [choiceType of Msg] g).[? uid] = Some u ->
  forall voter v r p,
    (voter, v) \in u.(softvotes) r p ->
    r0 <= r ->
    exists d, msg_received uid d (Softvote, val v, r, p, voter) trace.
Proof using.
  clear -H_path H_start H_last.
  move => uid u H_u voter v r p H_softvotes H_r.

  assert (~~match g0.(users).[? uid] with
            | Some u0 => (voter,v) \in u0.(softvotes) r p
            | None => false
            end). {
    destruct (g0.(users).[?uid]) as [u0|] eqn:H_u0;[|done].
    destruct H_start as [H_users _].
    have H_key0: uid \in g0.(users) by rewrite -fndSome H_u0.
    specialize (H_users _ H_key0).
    rewrite (in_fnd H_key0) in H_u0.
    case: H_u0 H_r H_users => ->.
    clear.
    move => H_r [_] [_] [_] [H_softvotes _].
    by move: {H_softvotes}(H_softvotes _ p H_r) => /nilP ->.
  }

  assert (H_path_copy := H_path).
  apply path_gsteps_onth with
      (P := upred uid (fun u => (voter, v) \in u.(softvotes) r p))
      (ix_p:=ix) (g_p:=g)
    in H_path_copy;
    try eassumption; try (unfold upred; rewrite H_u; assumption).

  destruct H_path_copy as [n [g1 [g2 [H_step [H_pg1 H_pg2]]]]].
  unfold upred in *.
  assert (H_step_copy := H_step).
  apply transition_from_path with (g0:=g0) in H_step_copy; try assumption.
  destruct (g2.(users).[? uid]) eqn:H_u2; try (by inversion H_u2).
  destruct (g1.(users).[? uid]) eqn:H_u1.
  2: {
    apply gtrans_preserves_users in H_step_copy.
    have H_in1: (uid \in domf (g1.(users)))
      by rewrite H_step_copy; rewrite -fndSome H_u2.
    rewrite in_fnd in H_u1. inversion H_u1.
  }
  assert (exists d ms, related_by (lbl_deliver uid d (Softvote, val v, r, p, voter) ms) g1 g2).

  have H_in1: (uid \in g1.(users)) by rewrite -fndSome H_u1.
  have H_in2: (uid \in g2.(users)) by rewrite -fndSome H_u2.
  have H_in1': g1.(users)[`H_in1] = u1 by rewrite in_fnd in H_u1;case:H_u1.

  destruct H_step_copy; simpl users; autounfold with gtransition_unfold in * |-;
    try (exfalso; rewrite H_u1 in H_u2; inversion H_u2; subst;
         rewrite H_pg2 in H_pg1; inversion H_pg1).

  (* tick *)
  + {
    exfalso.
    rewrite updf_update in H_u2. inversion H_u2 as [H_adv].
    rewrite H_in1' /user_advance_timer in H_adv.
    revert H_adv.
    match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b end;
      intros; subst; rewrite H_pg2 in H_pg1; inversion H_pg1.
    assumption.
    }

  (* deliver *)
  + {
    clear H_step.
    rewrite fnd_set in H_u2. case H_eq:(uid == uid0). move/eqP in H_eq; subst uid0.
    2: {
      rewrite H_eq in H_u2.
      rewrite H_u1 in H_u2. inversion H_u2; subst.
      rewrite H_pg2 in H_pg1; inversion H_pg1.
    }
    rewrite eq_refl in H_u2. inversion H_u2.
    move:H2. rewrite ?(eq_getf _ H_in1) H_in1'.
    intro H_deliv.
    remember (pending.1,pending.2) as pending_res.
    assert (H_pending : pending = pending_res).
    destruct pending. subst pending_res. intuition.
    rewrite Heqpending_res in H_pending; clear Heqpending_res.
    remember (ustate_post,sent) as result eqn:H_result.
    destruct H_deliv eqn:H_dtrans;
    try (by case: H_result => [? ?]; destruct pre;
         subst; simpl in * |-; exfalso; rewrite H_pg2 in H_pg1; inversion H_pg1).

    (* deliver softvote *)
    * {
      case: H_result => [? ?]; destruct pre.
      exists pending.1, [::], H_in1, ustate_post.
      simpl in * |- *.
      subst pre0.
      subst ustate_post. subst u0.
      unfold set_softvotes in H_pg2.
      simpl in H_pg2.
      revert H_pg2.
      match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b eqn:Hb1 end;
        try (by intro; rewrite H_pg2 in H_pg1; inversion H_pg1).
      match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b eqn:Hb2 end;
        try (by rewrite mem_undup; intro; rewrite H_pg2 in H_pg1; inversion H_pg1).

      intro.
      rewrite in_cons mem_undup in H_pg2.
      move/orP in H_pg2.
      destruct H_pg2 as [H_eqv | H_neqv];
        try (by rewrite H_neqv in H_pg1; inversion H_pg1).

      move/eqP in H_eqv. move/eqP in Hb1.
      case: H_eqv. case: Hb1.
      move => H_r_r1 H_p_p0 H_voter_i H_v_v0.
      subst r p voter v.

      split. assumption.
      rewrite in_fnd in H_u1; inversion H_u1. subst.
      split. assumption.

      exists msg_key. rewrite <- H_pending. split. assumption.
      trivial.
      }

    (* set softvote *)
    * {
      case: H_result => [? ?]; destruct pre.
      exists pending.1, [:: (Certvote, val v0, r1, p0, uid)], H_in1, ustate_post.
      simpl in * |- *.
      subst pre0.
      subst ustate_post. subst u0.
      unfold set_softvotes in H_pg2.
      simpl in H_pg2.
      revert H_pg2.
      match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b eqn:Hb1 end;
        try (by intro; rewrite H_pg2 in H_pg1; inversion H_pg1).
      match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b eqn:Hb2 end;
        try (by rewrite mem_undup; intro; rewrite H_pg2 in H_pg1; inversion H_pg1).

      intro.
      rewrite in_cons mem_undup in H_pg2.
      move/orP in H_pg2.
      destruct H_pg2 as [H_eqv | H_neqv];
        try (by rewrite H_neqv in H_pg1; inversion H_pg1).

      move/eqP in H_eqv. move/eqP in Hb1.
      case: H_eqv. case: Hb1.
      move => H_r_r1 H_p_p0 H_voter_i H_v_v0.
      subst r p voter v.

      split. assumption.
      rewrite in_fnd in H_u1; inversion H_u1; subst.
      split. assumption.

      exists msg_key. rewrite <- H_pending. split. assumption.
      trivial.
      }

    (* deliver nonvote msg result *)
    * {
      case: H_result => [? ?]; destruct pre; subst.
      unfold deliver_nonvote_msg_result in H_pg2.
      destruct msg.1.1.1.2 in H_pg2;
        try (rewrite H_pg2 in H_pg1; inversion H_pg1);
      destruct msg.1.1.1.1 in H_pg2;
      rewrite H_pg2 in H_pg1; inversion H_pg1.
      }
    }
  (* internal *)
  + {
    clear H_step.
    rewrite fnd_set in H_u2. case H_eq:(uid == uid0). move/eqP in H_eq; subst uid0.
    2: {
      rewrite H_eq in H_u2.
      rewrite H_u1 in H_u2. inversion H_u2; subst.
      rewrite H_pg2 in H_pg1; inversion H_pg1.
    }
    rewrite eq_refl in H_u2. inversion H_u2.
    move:H1. rewrite ?(eq_getf _ H_in1) H_in1'.
    intro H_trans. remember (ustate_post,sent) as result eqn:H_result.
    destruct H_trans; case:H_result => [? ?]; subst; destruct pre;
    simpl in * |-; exfalso; rewrite H_pg2 in H_pg1; inversion H_pg1.
    }

  (* corrupt *)
  + {
    exfalso.
    rewrite fnd_set in H_u2; case H_eq:(uid == uid0).
    move/eqP in H_eq. subst uid0. rewrite eq_refl in H_u2.
    rewrite ?(eq_getf _ H_in1) H_in1' in H_u2.
    inversion H_u2; subst.
    rewrite H_pg2 in H_pg1; inversion H_pg1.

    rewrite H_eq in H_u2.
    rewrite H_u1 in H_u2. inversion H_u2; subst.
    rewrite H_pg2 in H_pg1; inversion H_pg1.
    }

  destruct H0 as [d [ms H_rel]].
  exists d. unfold msg_received.
  exists n, ms. unfold step_at. exists g1, g2.
  split; assumption.
Qed.

(* vote in users nextvote_open set -> nextvote was received *)
Lemma received_nextvote_open
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start: state_before_round r0 g0):
  forall ix g, onth trace ix = Some g ->
  forall uid u,
    (global_state.users UserId UState [choiceType of Msg] g).[? uid] = Some u ->
  forall voter r p s,
    voter \in u.(nextvotes_open) r p s ->
    r0 <= r ->
    exists d, msg_received uid d (Nextvote_Open, step_val s, r, p, voter) trace.
Proof using.
  clear -H_path H_start.
  move => ix g H_g uid u H_u voter r p s H_voter H_r.
  set P := upred uid (fun u => voter \in u.(nextvotes_open) r p s).
  assert (~~P g0). {
  move: H_start => [H_users _]. clear -H_users H_r.
  subst P. unfold upred.
  destruct (uid \in g0.(users)) eqn: H_in.
  * move/(_ _ H_in) in H_users. rewrite in_fnd.
    move: {g0 H_in}(g0.(users)[` H_in]) H_users => u H_users.
    unfold user_before_round in H_users.
    decompose record H_users.
    by move: {H4 H_r}(H4 r p s H_r) => /nilP ->.
  * by rewrite not_fnd // H_in.
  }
  assert (P g). {
    unfold P, upred.
    rewrite H_u. assumption.
  }
  have := path_gsteps_onth H_path H_g H H0.
  clear -H_path.
  move => [n [g1 [g2 [H_step [H_pre H_post]]]]].
  have H_gtrans := transition_from_path H_path H_step.
  unfold msg_received, step_at.
  suff: exists d ms, related_by (lbl_deliver uid d (Nextvote_Open, step_val s, r, p, voter) ms) g1 g2
    by move => [d [ms H_rel]];exists d, n, ms, g1, g2;split;assumption.

  move: H_gtrans H_pre H_post;unfold P, upred;clear;destruct 1;
      try solve [move => /negP H_n /H_n []].
  { (* tick *)
  move => /negP H_n H_p. exfalso. move: H_n H_p. apply contrap.
  unfold tick_update, tick_users. cbn.
  destruct (uid \in pre.(users)) eqn:H_uid.
  * rewrite updf_update // in_fnd.
    move: (pre.(users)[` H_uid]) => u.
    by unfold user_advance_timer;destruct u, corrupt;simpl.
  * apply negbT in H_uid.
    rewrite [(updf _ _ _).[? uid]] not_fnd //.
    change (?k \in ?f) with (k \in domf f).
    rewrite -updf_domf. assumption.
  }
  { (* deliver *)
    rewrite fnd_set.
    destruct (uid == uid0) eqn:H_uids;[|by move/negP => H_n /H_n []].
    move => /eqP in H_uids. subst uid0.
    rewrite in_fnd.
    destruct pending as [d pmsg]. unfold snd in H1.

    remember (pre.(users)[`key_ustate]) as ustate;
    remember (ustate_post, sent) as result;
    destruct H1 eqn:H_step;case: Heqresult => {ustate_post}<- {sent}<-;subst pre0;
                                                try by move => /negP H_n H_p;exfalso.
    *
    unfold pre'.
    move => H_n H_p.
    assert ((r,p,s) = (r0,p0,s0)). {
    apply /eqP. apply/contraNT: H_n => /negbTE H_neq.
    move: H_p. unfold set_nextvotes_open;simpl. rewrite H_neq. done.
    } case: H2 => ? ? ?;subst r0 p0 s0.
    assert (i = voter). {
      symmetry. apply /eqP. apply/contraNT: H_n => /negbTE H_neq.
    rewrite /set_nextvotes_open /= eq_refl in H_p.

    match type of H_p with context C [if ?b then _ else _] => destruct b end.
      by rewrite mem_undup in H_p.
      by rewrite in_cons H_neq mem_undup in H_p.
    } subst i.
    by finish_case.
    *
    unfold pre'.
    move => H_n H_p.
    assert ((r,p,s) = (r0,p0,s0)). {
    apply /eqP. apply/contraNT: H_n => /negbTE H_neq.
    move: H_p. unfold set_nextvotes_open;simpl. rewrite H_neq. done.
    } case: H2 => ? ? ?;subst r0 p0 s0.
    assert (i = voter). {
      symmetry. apply /eqP. apply/contraNT: H_n => /negbTE H_neq.
    rewrite /set_nextvotes_open /= eq_refl in H_p.

    match type of H_p with context C [if ?b then _ else _] => destruct b end.
      by rewrite mem_undup in H_p.
      by rewrite in_cons H_neq mem_undup in H_p.
    } subst i.
    by finish_case.
    *
    move => /negP H_n H_p; exfalso;contradict H_n.
    move: (pre.(users)[`key_ustate]) H_p => u.
    clear.
    unfold deliver_nonvote_msg_result.
    destruct msg as [[[[m v] mr] mp] mu].
    simpl.
    by destruct v;first destruct m.
  }
  { (* internal *)
  move => /negP H_n H_p. exfalso. move: H_n H_p. apply contrap.
  rewrite fnd_set.
  destruct (uid == uid0) eqn:H_uids;[|done].
  move => /eqP in H_uids. subst uid0.
  rewrite in_fnd.
  move: (pre.(users)[` ustate_key]) H0 => u H_step.
  clear -H_step.
  remember (ustate_post,sent) as result;destruct H_step;
    case: Heqresult => <- _;by destruct pre.
  }
  { (* corrupt *)
  move => /negP H_n H_p. exfalso. move: H_n H_p. apply contrap.
  rewrite fnd_set.
  destruct (uid == uid0) eqn:H_uids;[|done].
  move => /eqP in H_uids. subst uid0.
  by rewrite in_fnd.
  }
Qed.

(* vote in users nextvote_val set -> nextvote_val was received *)
Lemma received_nextvote_val
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start: state_before_round r0 g0):
  forall ix g, onth trace ix = Some g ->
  forall uid u,
    (global_state.users UserId UState [choiceType of Msg] g).[? uid] = Some u ->
  forall voter v r p s,
    (voter, v) \in u.(nextvotes_val) r p s ->
    r0 <= r ->
    exists d, msg_received uid d (Nextvote_Val, next_val v s, r, p, voter) trace.
Proof using.
  clear -H_path H_start.
  move => ix g H_g uid u H_u voter v r p s H_voter H_r.
  set P := upred uid (fun u => (voter,v) \in u.(nextvotes_val) r p s).
  assert (~~P g0). {
  move: H_start => [H_users _]. clear -H_users H_r.
  subst P. unfold upred.
  destruct (uid \in g0.(users)) eqn: H_in.
  * move/(_ _ H_in) in H_users. rewrite in_fnd.
    move: {g0 H_in}(g0.(users)[` H_in]) H_users => u H_users.
    unfold user_before_round in H_users.
    decompose record H_users.
    by move: {H6 H_r}(H6 r p s H_r) => /nilP ->.
  * by rewrite not_fnd // H_in.
  }
  assert (P g). {
    unfold P, upred.
    rewrite H_u. assumption.
  }
  have := path_gsteps_onth H_path H_g H H0.
  clear -H_path.
  move => [n [g1 [g2 [H_step [H_pre H_post]]]]].
  have H_gtrans := transition_from_path H_path H_step.
  unfold msg_received, step_at.
  suff: exists d ms, related_by (lbl_deliver uid d (Nextvote_Val, next_val v s, r, p, voter) ms) g1 g2
    by move => [d [ms H_rel]];exists d, n, ms, g1, g2;split;assumption.

  move: H_gtrans H_pre H_post;unfold P, upred;clear;destruct 1;
      try solve [move => /negP H_n /H_n []].
  { (* tick *)
  move => /negP H_n H_p. exfalso. move: H_n H_p. apply contrap.
  unfold tick_update, tick_users. cbn.
  destruct (uid \in pre.(users)) eqn:H_uid.
  * rewrite updf_update // in_fnd.
    move: (pre.(users)[` H_uid]) => u.
    by unfold user_advance_timer;destruct u, corrupt;simpl.
  * apply negbT in H_uid.
    rewrite [(updf _ _ _).[? uid]] not_fnd //.
    change (?k \in ?f) with (k \in domf f).
    rewrite -updf_domf. assumption.
  }
  { (* deliver *)
    rewrite fnd_set.
    destruct (uid == uid0) eqn:H_uids;[|by move/negP => H_n /H_n []].
    move => /eqP in H_uids. subst uid0.
    rewrite in_fnd.
    destruct pending as [d pmsg]. unfold snd in H1.

    remember (pre.(users)[`key_ustate]) as ustate;
    remember (ustate_post, sent) as result;
    destruct H1 eqn:H_step;case: Heqresult => {ustate_post}<- {sent}<-;subst pre0;
                                                try by move => /negP H_n H_p;exfalso.
    *
    unfold pre'.
    move => H_n H_p.
    assert ((r,p,s) = (r0,p0,s0)). {
    apply /eqP. apply/contraNT: H_n => /negbTE H_neq.
    move: H_p. unfold set_nextvotes_val;simpl. rewrite H_neq. done.
    } case: H2 => ? ? ?;subst r0 p0 s0.
    assert ((voter,v) = (i,v0)). {
    apply /eqP. apply/contraNT: H_n => /negbTE H_neq.
    move: H_p. unfold set_nextvotes_val;simpl. rewrite eq_refl.
    match goal with
      [|- context C[(i, v0) \in ?nvs]] => destruct ((i,v0) \in nvs) eqn:H_in
    end.
      by rewrite H_in mem_undup.
      by rewrite H_in in_cons mem_undup; move/orP; destruct 1 as [H_eq|H_in'];
        [rewrite H_neq in H_eq; discriminate|].
    } case: H2 => ? ?;subst i v0.
    by finish_case.
    *
    unfold pre'.
    move => H_n H_p.
    assert ((r,p,s) = (r0,p0,s0)). {
    apply /eqP. apply/contraNT: H_n => /negbTE H_neq.
    move: H_p. unfold set_nextvotes_val;simpl. rewrite H_neq. done.
    } case: H2 => ? ? ?;subst r0 p0 s0.
    assert ((voter,v) = (i,v0)). {
    apply /eqP. apply/contraNT: H_n => /negbTE H_neq.
    move: H_p. unfold set_nextvotes_val;simpl. rewrite eq_refl.
    match goal with
      [|- context C[(i, v0) \in ?nvs]] => destruct ((i,v0) \in nvs) eqn:H_in
    end.
      by rewrite H_in mem_undup.
      by rewrite H_in in_cons mem_undup; move/orP; destruct 1 as [H_eq|H_in'];
        [rewrite H_neq in H_eq; discriminate|].
    } case: H2 => ? ?;subst i v0.
    by finish_case.
    *
    move => /negP H_n H_p; exfalso;contradict H_n.
    move: (pre.(users)[`key_ustate]) H_p => u.
    clear.
    unfold deliver_nonvote_msg_result.
    destruct msg as [[[[m v0] mr] mp] mu].
    simpl.
    by destruct v0;first destruct m.
  }
  { (* internal *)
  move => /negP H_n H_p. exfalso. move: H_n H_p. apply contrap.
  rewrite fnd_set.
  destruct (uid == uid0) eqn:H_uids;[|done].
  move => /eqP in H_uids. subst uid0.
  rewrite in_fnd.
  move: (pre.(users)[` ustate_key]) H0 => u H_step.
  clear -H_step.
  remember (ustate_post,sent) as result;destruct H_step;
    case: Heqresult => <- _;by destruct pre.
  }
  { (* corrupt *)
  move => /negP H_n H_p. exfalso. move: H_n H_p. apply contrap.
  rewrite fnd_set.
  destruct (uid == uid0) eqn:H_uids;[|done].
  move => /eqP in H_uids. subst uid0.
  by rewrite in_fnd.
  }
Qed.

(* ------------------------------------------------------------ *)
(* Softvote in user state means voter softvoted earlier in path *)
(* ------------------------------------------------------------ *)

  (*
    Suppose (voter,v) \in u.(softvotes) r p
    => message (Softvote, val v, r, p, i) was received
    => message (Softvote, val v, r, p, i) was sent:
      either
      - user i sent (Softvote, val v, r, p, i)
        (through an internal transition only)
        => softvoting preconditions imply i was a committee member
      - or adversary (using i) forged and sent the message
        => forging does the credentials check
      - or adversary replayed the message
        => the message is in msg_history
        => user i sent it (through an internal transition only)
        => softvoting preconditions imply i was a committee member
   *)
Lemma softvotes_sent
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start: state_before_round r0 g0):
  forall ix g, onth trace ix = Some g ->
  forall uid u, g.(users).[? uid] = Some u ->
  forall r, r0 <= r -> forall voter v p,
      (voter,v) \in u.(softvotes) r p ->
      honest_during_step (r,p,2) voter trace ->
      softvoted_in_path trace voter r p v.
Proof using.
  clear -H_path H_start.
  move => ix g H_onth uid u H_u r H_r voter v p H_voter H_honest.
  generalize dependent g. generalize dependent ix. generalize dependent voter.

  induction trace using last_ind;[discriminate|].

  move: (H_path).
  rename H_path into H_path_trans.
  destruct (rcons trace x) eqn:H_rcons.
  inversion H_path_trans.
  destruct H_path_trans as [H_g0 H_path_add]; subst g.
  rewrite <- H_rcons.

  move => H_path voter H_voter H_honest ix g H_onth H_u.
  destruct (ix == (size trace)) eqn:H_add.
  * { (* ix = size trace *)
  move/eqP in H_add. subst.
  have H_onth_copy := H_onth.
  unfold onth in H_onth_copy.
  rewrite drop_rcons // drop_size in H_onth_copy.
  case:H_onth_copy => H_x. subst x.

  have H_path_copy := H_path.
  eapply received_softvote in H_path;[|eassumption..].

  destruct H_path as [d H_msg_rec].

  apply received_was_sent with (r0:=r0)
                               (u:=uid) (d:=d)
                               (msg:=(Softvote, val v, r, p, voter))
    in H_path_copy;[|assumption..].
  apply H_path_copy in H_r;[|assumption].
  destruct H_r as [ix0 [g1 [g2 [H_s_at H_sent]]]].
  exists ix0, g1, g2;split;assumption.
  }
  *
  move /eqP in H_add.
  have H_onth' := onth_size H_onth.
  rewrite size_rcons in H_onth'.
  assert (H_ix : ix < size trace) by (ppsimpl; lia; done).
  clear H_onth' H_add.

  assert (H_onth_trace : (onth trace ix) = Some g). {
  unfold onth; unfold onth in H_onth; rewrite drop_rcons in H_onth.
  apply drop_nth with (x0:=g0) in H_ix; rewrite H_ix in H_onth.
  rewrite H_ix. trivial.
  ppsimpl; lia.
  }

  assert (H_trace: is_trace g0 trace).
  destruct trace;[by inversion H_onth_trace|].
  inversion H_rcons; subst.
  unfold is_trace.
  split;[done|].
    by rewrite rcons_path in H_path_add; move/andP: H_path_add; intuition.

  eapply IHtrace in H_trace; try eassumption.
  destruct H_trace as [ix0 [g1 [g2 [H_s_at H_sent]]]].
  unfold softvoted_in_path, softvoted_in_path_at.
  exists ix0, g1, g2;split;[|assumption].
  by apply step_in_path_prefix with (size trace);rewrite take_rcons.
  by move: H_honest;rewrite /honest_during_step all_rcons => /andP [] _.
Qed.

(* ------------------------------------------------------------ *)
(* Sender/forger of a message has sufficiently small credential *)
(* ------------------------------------------------------------ *)

Lemma user_sent_credential uid msg g1 g2:
  user_sent uid msg g1 g2 ->
  let:(r,p,s) := msg_step msg in uid \in committee r p s.
Proof using.
  move => [ms [H_in [[d [pending H_rel]]|H_rel]]];move: H_in;
            simpl in H_rel;decompose record H_rel.
  * { (* utransition deliver *)
    move: H. clear. move: {g1 x}(g1.(users)[`x]) => u.
    remember (x0,ms) as result.
    destruct 1;case:Heqresult => ? ?;subst x0 ms;move/Iter.In_mem => /= H_in;intuition;
    subst msg;simpl;
    apply/imfsetP;exists uid;[|reflexivity];apply/asboolP.
    unfold certvote_ok in H;decompose record H;assumption.
    }
  * { (* utransition internal *)
    move: H0. clear. move: {g1 x}(g1.(users)[`x]) => u.
    remember (x0,ms) as result.
    destruct 1;case:Heqresult => ? ?;subst x0 ms;move/Iter.In_mem => /= H_in;intuition;
    (subst msg;simpl;
     apply/imfsetP;exists uid;[|reflexivity];apply/asboolP);
    autounfold with utransition_unfold in * |-;
    match goal with [H:context C [comm_cred_step] |- _] => decompose record  H;assumption end.
    }
Qed.

Lemma user_forged_credential msg g1 g2:
  user_forged msg g1 g2 ->
  let:(r,p,s) := msg_step msg in msg_sender msg \in committee r p s.
Proof using.
  move: msg => [[[[mty v] r] p] sender] H_forged.
  simpl in H_forged;decompose record H_forged;clear H_forged;subst g2.
  move: (g1.(users)[`x]) H1 H0 => u. clear.
  destruct mty, v;simpl;(try solve[destruct 1]) => {x0}-> H_cred;
  (apply/imfsetP;exists sender;[|reflexivity];apply/asboolP;assumption).
Qed.

(* -------------------- *)
(* Checking credentials *)
(* -------------------- *)

(* all softvoters in a round/period are in the committee for step 2 *)
Lemma softvote_credentials_checked
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start: state_before_round r0 g0):
  forall ix g, onth trace ix = Some g ->
  forall uid u, g.(users).[? uid] = Some u ->
  forall r, r0 <= r -> forall v p,
    softvoters_for v u r p `<=` committee r p 2.
Proof.
  (* cleanup needed *)
  clear -H_path H_start.
  intros ix g H_onth uid u H_lookup r H_r v p.
  apply/fsubsetP => voter H_softvoters.

  have H_softvote : (voter,v) \in u.(softvotes) r p
    by move: H_softvoters;clear;move => /imfsetP [] [xu xv] /= /andP [H_in /eqP] -> ->.

  apply onth_take_some in H_onth.
  assert (H_ix : ix.+1 > 0) by intuition.
  have [d [n [ms H_deliver]]] :=
    received_softvote
      (is_trace_prefix H_path H_ix) H_start
      H_onth H_lookup
      H_softvote H_r.

  set msg := (Softvote,val v,r,p,voter).
  assert
    (exists send_ix g1 g2, step_in_path_at g1 g2 send_ix trace
                           /\ (user_sent voter msg g1 g2 \/ user_forged msg g1 g2))
    as H_source. {
    rewrite /step_at /= in H_deliver;decompose record H_deliver.
    assert (onth trace n = Some x)
      by (refine (onth_from_prefix (step_in_path_onth_pre _));eassumption).
    eapply pending_sent_or_forged;try eassumption.
  }

  destruct H_source as (send_ix & g1 & g2 & H_step & [H_send | H_forge]).
  apply user_sent_credential in H_send. assumption.
  apply user_forged_credential in H_forge. assumption.
Qed.

(* all nextvoters for bot in a round/period/step are in the committee *)
Lemma nextvote_open_credentials_checked
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start: state_before_round r0 g0):
  forall ix g, onth trace ix = Some g ->
  forall uid u, g.(users).[? uid] = Some u ->
  forall r, r0 <= r -> forall p s,
      nextvoters_open_for u r p s `<=` committee r p s.
Proof.
  clear -H_path H_start.
  intros ix g H_onth uid u H_lookup r H_r p s.
  apply/fsubsetP => voter H_nextvoters.

  have H_nextvote : voter \in u.(nextvotes_open) r p s
    by revert H_nextvoters; rewrite in_fset;
    change (in_mem voter _) with (voter \in u.(nextvotes_open) r p s).

  apply onth_take_some in H_onth.
  assert (H_ix : ix.+1 > 0) by intuition.
  have [d [n [ms H_deliver]]] :=
    received_nextvote_open
      (is_trace_prefix H_path H_ix) H_start
      H_onth H_lookup
      H_nextvote H_r.

  set msg := (Nextvote_Open,step_val s,r,p,voter).
  assert
    (exists send_ix g1 g2, step_in_path_at g1 g2 send_ix trace
                           /\ (user_sent voter msg g1 g2 \/ user_forged msg g1 g2))
    as H_source. {
    rewrite /step_at /= in H_deliver;decompose record H_deliver.
    assert (onth trace n = Some x)
      by (refine (onth_from_prefix (step_in_path_onth_pre _));eassumption).
    eapply pending_sent_or_forged;try eassumption.
  }

  destruct H_source as (send_ix & g1 & g2 & H_step & [H_send | H_forge]).
  apply user_sent_credential in H_send. assumption.
  apply user_forged_credential in H_forge. assumption.
Qed.

(* all nextvoters for bota val in a round/period/step are in the committee *)
Lemma nextvote_val_credentials_checked
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start: state_before_round r0 g0):
  forall ix g, onth trace ix = Some g ->
  forall uid u, g.(users).[? uid] = Some u ->
  forall r, r0 <= r -> forall v p s,
      nextvoters_val_for v u r p s `<=` committee r p s.
Proof.
  clear -H_path H_start.
  intros ix g H_onth uid u H_lookup r H_r v p s.
  apply/fsubsetP => voter H_nextvoters.

  have H_nextvote : (voter,v) \in u.(nextvotes_val) r p s
    by move: H_nextvoters;clear;move => /imfsetP [] [xu xv] /= /andP [H_in /eqP] -> ->.

  apply onth_take_some in H_onth.
  assert (H_ix : ix.+1 > 0) by intuition.
  have [d [n [ms H_deliver]]] :=
    received_nextvote_val
      (is_trace_prefix H_path H_ix) H_start
      H_onth H_lookup
      H_nextvote H_r.

  set msg := (Nextvote_Val,next_val v s,r,p,voter).
  assert
    (exists send_ix g1 g2, step_in_path_at g1 g2 send_ix trace
                           /\ (user_sent voter msg g1 g2 \/ user_forged msg g1 g2))
    as H_source. {
    rewrite /step_at /= in H_deliver;decompose record H_deliver.
    assert (onth trace n = Some x)
      by (refine (onth_from_prefix (step_in_path_onth_pre _));eassumption).
    eapply pending_sent_or_forged;try eassumption.
  }

  destruct H_source as (send_ix & g1 & g2 & H_step & [H_send | H_forge]).
  apply user_sent_credential in H_send. assumption.
  apply user_forged_credential in H_forge. assumption.
Qed.

(* ---------------- *)
(* Advancing period *)
(* ---------------- *)

(* period advances to p, step of ustate changes to (r,p,1) with round the same,
   original ustate must have had smaller period *)
Definition period_advances uid r p (users1 users2: {fmap UserId -> UState}) : Prop :=
  {ukey_1: uid \in users1 &
  {ukey_2: uid \in users2 &
  let ustate1 := users1.[ukey_1] in
  let ustate2 := users2.[ukey_2] in
  ustate1.(round) = ustate2.(round)
  /\ step_lt (step_of_ustate ustate1) (r,p,0)
  /\ step_of_ustate ustate2 = (r,p,1)}}.

(* period advances from g1 to g2 at given index in path *)
Definition period_advance_at n path uid r p g1 g2 : Prop :=
  step_in_path_at g1 g2 n path /\ period_advances uid r p (g1.(users)) (g2.(users)).

(* period advances to r.p from ge1 to ge2, and there is a message sent from gs1
   to gs2 in the path at r.p along with a step in the path from gs1 to gs2, then
   gs1 is reachable from ge2 *)
Lemma post_enter_reaches_sent
      g0 trace (H_path:is_trace g0 trace)
      ix_e uid r p ge1 ge2 (H_enter: period_advance_at ix_e trace uid r p ge1 ge2)
      ix_s gs1 gs2 (H_step: step_in_path_at gs1 gs2 ix_s trace)
      msg (H_send: user_sent uid msg gs1 gs2)
      (H_r_msg: msg_round msg = r)
      (H_p_msg: msg_period msg = p):
  greachable ge2 gs1.
 Proof using.
  move: H_enter => [H_step_enter [ukey_ge1 [ukey_ge2 [H_adv [H_ge1_step_lt H_ge2_step_eq]]]]].
  set ukey_gs1 := user_sent_in_pre H_send.

  assert (ix_e < ix_s) as H_order.
  {
    have: step_lt (step_of_ustate (ge1.(users)[` ukey_ge1]))
                  (step_of_ustate (gs1.(users)[` ukey_gs1])).
    apply/(step_lt_le_trans H_ge1_step_lt)/step_leP.
      by rewrite (utransition_label_start H_send (in_fnd ukey_gs1)) /= H_r_msg H_p_msg !ltnn !eq_refl leq0n.
    eapply (order_ix_from_steps H_path
              (step_in_path_onth_pre H_step_enter)
              (step_in_path_onth_pre H_step)).
  }

  exact
     (at_greachable H_path (ix1:=ix_e.+1) (ix2:=ix_s) H_order
                       (step_in_path_onth_post H_step_enter)
                       (step_in_path_onth_pre H_step)).
Qed.

(* a node enters period p > 0 only if it received t_H next-votes for the same
   value from some step s of period p-1 *)
Lemma period_advance_only_by_next_votes
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start: state_before_round r0 g0):
    forall n uid r p,
      r0 <= r ->
    forall g1 g2, period_advance_at n trace uid r p g1 g2 ->
      exists (s:nat) (v:option Value) (next_voters:{fset UserId}),
        next_voters `<=` committee r p.-1 s
        /\ (if v then tau_v else tau_b) <= #|` next_voters |
        /\ (exists u, g2.(users).[?uid] = Some u /\ u.(stv) p = v)
        /\ forall voter, voter \in next_voters ->
           received_next_vote uid voter r p.-1 s v trace.
Proof using.
  clear -H_path H_start.
  intros n uid r p H_r g1 g2 H_adv.
  destruct H_adv as [H_step [H_g1 [H_g2 [H_round [H_lt H_rps]]]]].
  assert (H_gtrans : g1 ~~> g2) by (eapply transition_from_path; eassumption).

  assert (H_lt_0 := H_lt).
  eapply step_lt_le_trans with (c:=(r,p,1)) in H_lt.
  2: { simpl; intuition. }

  destruct H_gtrans.

  (* tick *)
  exfalso.
  pose proof (tick_users_upd increment H_g1) as H_tick.
  rewrite in_fnd in H_tick.

  assert (H_tick_adv :
            (tick_users increment pre) [` H_g2] =
            user_advance_timer
              increment
              ((global_state.users UserId UState [choiceType of Msg] pre) [` H_g1])).
    by inversion H_tick; simpl; assumption.

  clear H_tick.
  unfold tick_update in H_rps.
  cbn -[in_mem mem] in H_rps.

  rewrite H_tick_adv in H_rps.
  unfold user_advance_timer in H_rps.
  destruct (local_state.corrupt UserId Value PropRecord Vote
                                ((global_state.users UserId UState [choiceType of Msg] pre)
                                   [` H_g1]));
    rewrite <- H_rps in H_lt; apply step_lt_irrefl in H_lt; assumption.

  { (* message delivery cases *)
    unfold delivery_result in H_rps.
    rewrite setfNK in H_rps.
    destruct (uid == uid0) eqn:H_uid.
    move/eqP in H_uid. subst.
    simpl in H_rps.
    assert (H_g1_key_ustate_opt :
              Some (pre.(users)[`H_g1]) = Some (pre.(users)[`key_ustate])).
      by repeat rewrite -in_fnd.

    inversion H_g1_key_ustate_opt as [H_g1_key_ustate]. clear H_g1_key_ustate_opt.
    rewrite H_g1_key_ustate in H_lt; rewrite <- H_rps in H_lt.
    rewrite H_g1_key_ustate in H_round.
    unfold step_of_ustate in H_lt.

    remember (ustate_post,sent) as ustep_out in H1.
    remember (pre.(users)[` key_ustate]) as u in H1.

    destruct H1; injection Hequstep_out; clear Hequstep_out; intros <- <-;
      try (inversion H_rps; exfalso; subst; subst pre';
           apply step_lt_irrefl in H_lt; contradiction).

    (* positive case: nextvote open *)
    {
      destruct H1 as [H_valid_rps H_quorum_size].
      rewrite H_g1_key_ustate in H_lt_0.
      clear H_g1_key_ustate H_g1.
      rename pre0 into u.
      rewrite -Hequ in H0 H_lt_0 H_lt H_round.
      cbn -[step_le step_lt] in * |-.

      destruct H_valid_rps as [H_r1 [H_p0 H_s]].
      case:H_rps => H_r' H_p.
      rewrite -H_p H_p0 -H_r' H_r1.

      assert (H_n : n.+2 > 0) by intuition.
      apply step_in_path_onth_post in H_step.
      match goal with [H : onth trace n.+1 = Some ?x |- _] => rename H into H_onth;remember x as dr end.
      (*
      assert (H_onth : onth (take n.+2 trace) n.+1 = Some dr).
        subst pref.
        destruct (n.+2 < size trace) eqn:H_n2.
        apply onth_take_some in H_step. rewrite size_take in H_step.
        rewrite H_n2 in H_step. by intuition; eassumption.
        assert (size trace <= n.+2). by clear -H_n2; ppsimpl; lia.
        rewrite take_oversize; assumption.
      *)

      assert (H_addsub : (p0 + 1)%Nrec.-1 = p0). by clear; ppsimpl; lia.
      rewrite H_addsub.
      assert (H_r0r1 : r0 <= r1).
        by simpl in H_r1; rewrite H_r1 in H_r'; subst r; eassumption.

      exists s, None, (nextvoters_open_for pre' r1 p0 s); repeat split.
      eapply nextvote_open_credentials_checked with
          (uid:=uid) (u:=(adv_period_open_result pre'));
        try eassumption;
        try (subst dr; rewrite fnd_set; by rewrite eq_refl).

      simpl.
      unfold nextvoters_open_for.
      move: H_quorum_size.
      by rewrite card_fseq -finseq_size.

      exists (adv_period_open_result pre').
      split.
        by rewrite Heqdr fnd_set eq_refl.
      simpl.
      by rewrite H_p0 -/addn addn1 eq_refl.

      intro voter.
      rewrite in_fset.
      change (in_mem voter _) with (voter \in pre'.(nextvotes_open) r1 p0 s).

      intro H_voter.
      eapply received_nextvote_open with (u:=(adv_period_open_result pre'));
        try eassumption;
        try (subst dr; rewrite fnd_set; by rewrite eq_refl).
    }

    (* positive case: nextvote val *)
    {
      destruct H1 as [H_valid_rps H_quorum_size].
      rewrite H_g1_key_ustate in H_lt_0.
      clear H_g1_key_ustate H_g1.
      rename pre0 into u.
      rewrite -Hequ in H0 H_lt_0 H_lt H_round.

      destruct H_valid_rps as [H_r1 [H_p0 H_s]].
      case:H_rps => H_r' H_p.
      rewrite -H_p H_p0 -H_r' H_r1.

      apply step_in_path_onth_post in H_step.
      match goal with [H : onth trace n.+1 = Some ?x |- _] => rename H into H_onth;remember x as dr end.

      assert (H_addsub : (p0 + 1)%Nrec.-1 = p0). by clear; ppsimpl; lia.
      rewrite H_addsub.
      assert (H_r0r1 : r0 <= r1).
        by simpl in H_r1; rewrite H_r1 in H_r'; subst r; eassumption.

      exists s, (Some v), (nextvoters_val_for v pre' r1 p0 s); repeat split.
      eapply nextvote_val_credentials_checked with
          (uid:=uid) (u:=(adv_period_val_result pre' v));
        try eassumption;
        try (subst dr; rewrite fnd_set; by rewrite eq_refl).

      simpl.
      move: H_quorum_size.
      unfold nextvote_value_quorum.
      rewrite finseq_size -card_fseq.
      match goal with |[|- is_true (tau_v <= ?A) -> is_true (tau_v <= ?B)]
                       => suff ->: A = B by[] end.
      by apply/imfset_filter_size_lem.

      exists (adv_period_val_result pre' v).
      split.
        by rewrite Heqdr fnd_set eq_refl.
        by rewrite /= H_p0 -/addn addn1 eq_refl.

      intros voter H_voter.
      have H_nextvote : (voter,v) \in pre'.(nextvotes_val) r1 p0 s
        by move: H_voter;move=>/imfsetP [] [xu xv] /= /andP [H_in /eqP];intros->->.

      eapply received_nextvote_val with (u:=(adv_period_val_result pre' v));
        try eassumption;
        try (subst dr; rewrite fnd_set; by rewrite eq_refl).
    }

    exfalso.
    rewrite setfNK in H_round.
    assert (H_uid : (uid == uid) = true). apply/eqP; trivial.
    rewrite H_uid in H_round.

    subst pre0.
    inversion H_rps as [H_r0].
    cbn -[step_lt addn] in H_lt. rewrite H_r0 in H_lt.
    destruct H1 as [H_adv _]. unfold advancing_rp in H_adv.
    rewrite H_round in H_adv. clear -H_adv.
    by simpl in H_adv; ppsimpl; lia.

    exfalso. subst.
    unfold deliver_nonvote_msg_result in *.
    destruct pre.
    clear -H_rps H_lt.
    cbn -[step_lt] in * |- *.
    destruct msg.1.1.1.2; destruct msg.1.1.1.1;cbn -[step_lt] in H_lt;
    case:H_rps H_lt => -> -> ->;apply step_lt_irrefl.

    exfalso. rewrite <- H_rps in H_lt; apply step_lt_irrefl in H_lt; contradiction.
  }

  { (* internal step case *)
    exfalso.
    unfold step_result in H_rps.
    rewrite setfNK in H_rps.
    destruct (uid == uid0) eqn:Huid.
    move/eqP in Huid. subst.
    simpl in H_rps.
    assert (H_g1_key_ustate_opt :
              Some (pre.(users)[`H_g1]) = Some (pre.(users)[`ustate_key])).
      by repeat rewrite -in_fnd.

    inversion H_g1_key_ustate_opt as [H_g1_key_ustate]. clear H_g1_key_ustate_opt.
    rewrite H_g1_key_ustate in H_lt; rewrite <- H_rps in H_lt.
    unfold step_of_ustate in H_lt.

    remember (ustate_post,sent) as ustep_out in H0.
    remember (pre.(users)[`ustate_key]) as u in H0.

    destruct H0; injection Hequstep_out; clear Hequstep_out; intros <- <-; inversion H_rps;
      try (destruct H0 as [H_lam [H_vrps [H_ccs [H_s [H_rest]]]]];
           clear -H4 H_s; by ppsimpl; lia).

    subst; try apply step_lt_irrefl in H_lt; try contradiction.

    destruct H0 as [H_nv_stv H_stv].
    destruct H_nv_stv as [H_lam [H_vrps [H_ccs [H_s [H_rest]]]]].
    clear -H4 H_s. by ppsimpl; lia.

    (* no nextvote ok - need s > 3 assumption? *)
    move:H_lt_0;rewrite H_g1_key_ustate -Hequ /step_of_ustate H2 H3.
    clear;move: (pre0.(step)) => s /step_ltP /=.
    by rewrite !eq_refl !ltnn ltn0.

    subst. simpl in H_lt.
    simpl in H_rps;inversion H_rps.
    rewrite H2 H3 H4 !ltnn in H_lt.
    clear -H_lt. intuition.
    (*
    unfold certvote_timeout_ok in H0.
    inversion H0; subst.
    clear -H4 H1. rewrite H1 in H4. inversion H4.

    rewrite <- H_rps in H_lt; apply step_lt_irrefl in H_lt; contradiction.
    *)
  }

  (* recover from partition *)
  exfalso.
  simpl in H_g2.
  assert (H_g1_g2_opt : Some (pre.(users)[`H_g1]) = Some (pre.(users)[`H_g2])).
    by repeat rewrite -in_fnd.

  inversion H_g1_g2_opt as [H_g1_g2]; clear H_g1_g2_opt.
  rewrite H_g1_g2 in H_lt.
  rewrite <- H_rps in H_lt; apply step_lt_irrefl in H_lt; assumption.

  (* enter partition *)
  exfalso.
  simpl in H_g2.
  assert (H_g1_g2_opt : Some (pre.(users)[`H_g1]) = Some (pre.(users)[`H_g2])).
    by repeat rewrite -in_fnd.

  inversion H_g1_g2_opt as [H_g1_g2]; clear H_g1_g2_opt.
  rewrite H_g1_g2 in H_lt.
  rewrite <- H_rps in H_lt; apply step_lt_irrefl in H_lt; assumption.

  (* corrupt user *)
  exfalso.

  rewrite setfNK in H_rps.
  destruct (uid == uid0) eqn:Huid.
  move/eqP in Huid. subst.
  simpl in H_rps.
  assert (H_g1_ustate_key_opt : 
            Some (pre.(users)[`H_g1]) = Some (pre.(users)[`ustate_key])).
    by repeat rewrite -in_fnd.

  inversion H_g1_ustate_key_opt as [H_g1_ustate_key]; clear H_g1_ustate_key_opt.
  rewrite H_g1_ustate_key in H_lt.
  rewrite <- H_rps in H_lt; apply step_lt_irrefl in H_lt; assumption.

  rewrite <- H_rps in H_lt; apply step_lt_irrefl in H_lt; assumption.

  (* replay message *)
  exfalso.
  simpl in H_g2.
  assert (H_g1_g2_opt : Some (pre.(users)[`H_g1]) = Some (pre.(users)[`H_g2])).
    by repeat rewrite -in_fnd.
  inversion H_g1_g2_opt as [H_g1_g2]; clear H_g1_g2_opt.
  rewrite H_g1_g2 in H_lt.
  rewrite <- H_rps in H_lt; apply step_lt_irrefl in H_lt; assumption.

  (* forge message *)
  exfalso.
  simpl in H_g2.
  assert (H_g1_g2_opt : Some (pre.(users)[`H_g1]) = Some (pre.(users)[`H_g2])).
    by repeat rewrite -in_fnd.
  inversion H_g1_g2_opt as [H_g1_g2]; clear H_g1_g2_opt.
  rewrite H_g1_g2 in H_lt.
  rewrite <- H_rps in H_lt; apply step_lt_irrefl in H_lt; assumption.
Qed.

(* a user honest at r.p must have advanced to period p *)
Lemma honest_in_period_entered
      g0 trace (H_path : is_trace g0 trace)
      r (H_start: state_before_round r g0):
  forall p, 1 < p ->
  forall uid, honest_in_period r p uid trace ->
  exists n g1 g2, period_advance_at n trace uid r p g1 g2.
Proof using.
  clear -H_path H_start.
  move => p H_p_gt uid [ix H_in_period].
  destruct (onth trace ix) as [g|] eqn:H_g;rewrite H_g in H_in_period;
    [|exfalso;assumption].
  destruct (g.(users).[?uid]) as [u|] eqn:H_u;[|exfalso;assumption].
  move: H_in_period => [H_honest [H_r H_p]].
  set P := upred uid (fun u => (u.(round) == r) && (u.(period) == p)).
  have H_Pg : P g by rewrite /P /upred H_u H_r H_p !eq_refl.
  have H_NPg0  : ~~ P g0.
  {
  rewrite /P /upred.
  destruct (g0.(users).[?uid]) as [u0|] eqn:H_u0;[|exact].
  apply/negP => /andP [/eqP H_r0 /eqP H_p0].
  move: H_start => [H_users_before _].
  unfold users_before_round in H_users_before.
  have H_in_u0: uid \in g0.(users) by rewrite -fndSome H_u0.
  specialize (H_users_before _ H_in_u0).
  rewrite in_fnd in H_u0. case: H_u0 H_users_before => -> [H_u0_step _].
  case: H_u0_step => [| [] _ [] _ [] H_p' _];[by rewrite H_r0 ltnn|].
  by move: H_p_gt;rewrite -H_p0 H_p' ltnn.
  }
  have {H_Pg H_NPg0}[n [g1 [g2 [H_step H_change]]]]
    := path_gsteps_onth H_path H_g H_NPg0 H_Pg.
  exists n,g1,g2;split;[assumption|].

  apply (transition_from_path H_path) in H_step.
  have H_in2 : uid \in g2.(users)
    by move: H_change => [] _;unfold P, upred;
       destruct g2.(users).[?uid] eqn:H_u2 => H_P2;[rewrite -fndSome H_u2|].
  have H_in1 : uid \in g1.(users)
    by rewrite /in_mem /= /pred_of_finmap (gtrans_preserves_users H_step).
  clear -H_step H_change H_in1 H_in2 H_p_gt.
  destruct (H_step);try by exfalso;move: H_change => [] /negP.
  * (* tick *)
    exfalso. move: H_change => [] /negP.
    autounfold with gtransition_unfold;unfold P, upred.
    rewrite updf_update // (in_fnd H_in1).
    move:(pre.(users)[`H_in1]) => u;destruct u,corrupt;exact.
  * (* deliver *)
    {
    move: H_change => [] /negP.
    rewrite {1}/delivery_result /P /upred fnd_set.
    destruct (uid == uid0) eqn:H_eq;
      [move/eqP in H_eq;subst uid0
      |by move => A {A}/A].
    rewrite (in_fnd key_ustate).
    remember (pre.(users)[` key_ustate] : UState) as u.
    move => H_pre /andP [/eqP H_r /eqP H_p].
    exists key_ustate, H_in2.
    symmetry in Hequ; rewrite Hequ.
    intros ustate1 ustate2; subst ustate1 ustate2.
    rewrite getf_set.

    assert (step_lt (step_of_ustate u) (r,p,0)) as H_step_lt.
    {
      have {H_step}H_after : ustate_after u ustate_post by
        apply (gtr_rps_non_decreasing H_step (uid:=uid));
      [symmetry in Hequ;rewrite Hequ;apply in_fnd
      |rewrite fnd_set eq_refl].
      apply ustate_after_iff_step_le in H_after.
      case:H_after =>[|[a b]];[by rewrite H_r;left|].
      right;split;[by rewrite a|left].
      case:b=>[|[b _]];[by rewrite H_p|exfalso].
      apply H_pre;rewrite a b H_r H_p !eq_refl;done.
    }
    suff: u.(round)=ustate_post.(round) /\ step_of_ustate ustate_post = (r,p,1) by tauto.
    unfold step_of_ustate.
    remember (ustate_post,sent) as result;destruct H1;
      case:Heqresult => ? ?;subst ustate_post sent;
        try (destruct H_pre;by rewrite H_r H_p !eq_refl).
    + (* adv_period_open_result *)
      by move: H_p H_r;simpl => -> ->;clear;split;reflexivity.
    + (* adv_period_val_result *)
      by move: H_p H_r;simpl => -> ->;clear;split;reflexivity.
    + (* certify result *)
      by rewrite -H_p ltnn in H_p_gt.
    + {
        destruct H_pre;rewrite -H_r -H_p /deliver_nonvote_msg_result.
        clear.
        by repeat match goal with
                |[|- context X [match ?x with _ => _ end]] => destruct x
               end;rewrite !eq_refl.
      }
    }
  * (* internal *)
    {
      move: H_change => [] /negP.
      rewrite {1}/step_result /P /upred fnd_set.
      destruct (uid == uid0) eqn:H_eq;
        [move/eqP in H_eq;subst uid0
        |by move => A {A}/A].
      rewrite (in_fnd ustate_key).
      remember (pre.(users)[` ustate_key] : UState) as u.
      move => H_pre /andP [/eqP H_r /eqP H_p].
      exists ustate_key, H_in2.
      symmetry in Hequ; rewrite Hequ.
      intros ustate1 ustate2; subst ustate1 ustate2.
      rewrite getf_set.

      assert (step_lt (step_of_ustate u) (r,p,0)) as H_step_lt.
      {
        have {H_step}H_after : ustate_after u ustate_post by
        apply (gtr_rps_non_decreasing H_step (uid:=uid));
          [symmetry in Hequ;rewrite Hequ;apply in_fnd
          |rewrite fnd_set eq_refl].
        apply ustate_after_iff_step_le in H_after.
        case:H_after =>[|[a b]];[by rewrite H_r;left|].
        right;split;[by rewrite a|left].
        case:b=>[|[b _]];[by rewrite H_p|exfalso].
        apply H_pre;rewrite a b H_r H_p !eq_refl;done.
      }
      suff: u.(round)=ustate_post.(round) /\ step_of_ustate ustate_post = (r,p,1) by tauto.
      remember (ustate_post,sent) as result;destruct H0;
      case:Heqresult => ? ?;subst ustate_post sent;
           try (destruct H_pre;by rewrite H_r H_p !eq_refl).
    }
  * (* corrupt *)
    exfalso. move: H_change => [] /negP.
    unfold corrupt_user_result, P, upred.
    rewrite fnd_set.
    destruct (uid==uid0) eqn:H_eq;[|by apply].
    move /eqP in H_eq;subst uid0.
    by rewrite (in_fnd ustate_key).
Qed.


(* An honest node can enter period p'>1 only if at least one honest node
   participated in period p'-1 *)
(* Note that we freeze the state of corrupt users, so any user whose period
   actually advanced must have been honest at the time *)
Lemma adv_period_from_honest_in_prev g0 trace (H_path: is_trace g0 trace)
  r0 (H_start: state_before_round r0 g0):
  forall n uid r p,
    p > 0 ->
    r0 <= r ->
    (exists g1 g2, period_advance_at n trace uid r p g1 g2) ->
    exists uid', honest_in_period r (p.-1) uid' trace.
Proof.
  intros n uid r p.
  intros H_p H_r [g1 [g2 H_adv]].
  eapply period_advance_only_by_next_votes in H_adv;[|eassumption..].
  destruct H_adv as (s & v & next_voters & H_voters_cred & H_voters_size & _ & ?).
  clear g1 g2.
  assert (H_n : n.+2 > 0) by intuition.
  assert (exists honest_voter, honest_voter \in next_voters /\ honest_during_step (r,p.-1,s) honest_voter trace) as (uid_honest & H_honest_voter & H_honest)
    by (destruct v;simpl in H_voters_size;[eapply quorum_v_has_honest|eapply quorum_b_has_honest];eassumption).
  clear H_voters_size.
  exists uid_honest.
  specialize (H uid_honest H_honest_voter).
  unfold received_next_vote in H.
  set msg_bit:= (match v with | Some v => (Nextvote_Val, next_val v s)
               | None => (Nextvote_Open, step_val s)
       end) in H.
  destruct H as [d H].
  pose proof (received_was_sent H_path H_start H) as H1.
  rewrite {1}[msg_bit]surjective_pairing in H1.
  specialize (H1 H_r).
  cbn -[user_sent step_in_path_at msg_step] in H1.
  lapply H1;[clear H1|destruct v;assumption].
  intros (ix & g1 & g2 & H_step & H_sent).
  unfold honest_in_period;exists ix.
  have H_onth:= step_in_path_onth_pre H_step.
  rewrite H_onth.
  have H_user_in := user_sent_in_pre H_sent.
  rewrite (in_fnd H_user_in).
  have H_start_label := utransition_label_start H_sent (in_fnd H_user_in).

  split.
  { (* Honest at ix *)
  suff: (user_honest uid_honest g1)
      by unfold user_honest;rewrite in_fnd;move/negP.
  apply (user_honest_from_during H_path H_onth (H_in:=H_user_in)).
  rewrite H_start_label.
  revert H_honest.
  apply honest_during_le .
  destruct v;apply step_le_refl.
  }
  {
    move: (g1.(users)[`H_user_in]) H_start_label => u. clear.
    by destruct u, v;case.
  }
Qed.

(* ------------------------------------------------- *)
(* Users cannot nextvote for both a value and bottom *)
(* ------------------------------------------------- *)

(* definition that states that if there is a quorum of voters for the value v,
   then there cannot be a quorum of voters for bottom *)
Definition period_nextvoted_exclusively_for (v:Value) (r p:nat) (trace: seq GState) : Prop :=
  (forall s (voters: {fset UserId}),
     voters `<=` committee r p s ->
    tau_v <= #|` voters | ->
    forall v',
   (forall u, u \in voters ->
      honest_during_step (r,p,s) u trace ->
      nextvoted_val_in_path trace u r p s v')
   -> v' = v)
  /\
  (forall s (voters: {fset UserId}),
     voters `<=` committee r p s ->
    tau_b <= #|` voters | ->
   ~(forall u, u \in voters ->
      honest_during_step (r,p,s) u trace ->
      nextvoted_bot_in_path trace u r p s)).

(* if all users nextvte for v and all users did not nextvote for bottom, then
   the above definition holds *)
Lemma period_nextvoted_exclusively_from_nextvotes
      g0 trace (H_path: is_trace g0 trace)
      r (H_start: state_before_round r g0)
      p (H_p_gt: 1 < p)
      v
  (H_nextvote_val : forall (uid : UserId) (s : nat) (v' : Value),
                            nextvoted_val_in_path trace uid r p s v' -> v' = v)
  (H_no_nextvotes_open : forall (uid : UserId) (s : nat),
                        honest_during_step (r, p, s) uid trace ->
                        ~ nextvoted_bot_in_path trace uid r p s):
  period_nextvoted_exclusively_for v r p trace.
Proof.
  split => s voters H_creds H_size.
  * { (* nextvote_val quorums all voted for v *)
      have [honest_voter [H_hv_in H_hv_honest]]:= quorum_v_has_honest trace H_creds H_size.
      move => v' /(_ _ H_hv_in H_hv_honest).
      by apply/H_nextvote_val.
    }
  * { (* no nextvote_open quorums *)
      have [honest_voter [H_hv_in H_hv_honest]]:= quorum_b_has_honest trace H_creds H_size.
      move/(_ _ H_hv_in H_hv_honest).
      by apply/H_no_nextvotes_open: H_hv_honest.
    }
Qed.

(* period_nextvoted_exclusively_for disallows nextvote_bottom_quorum *)
Lemma no_bottom_quorums_during_from_nextvoted_excl
  g0 trace (H_path: is_trace g0 trace)
  r (H_start: state_before_round r g0)
  p v (H_excl: period_nextvoted_exclusively_for v r p trace)
  ix g (H_g: onth trace ix = Some g)
  uid u (H_u: g.(users).[?uid] = Some u)
  (H_r: u.(round) = r)
  (H_p: u.(period) = p.+1):
  forall s : nat, ~ nextvote_bottom_quorum u r p s.
 Proof using.
   unfold nextvote_bottom_quorum => s H_bot_quorum.
   move:H_excl => [_ /(_ s (nextvoters_open_for u r p s)) H_no_bot_votes].
   specialize (H_no_bot_votes (nextvote_open_credentials_checked H_path H_start H_g H_u (leqnn _) p s)).
   apply H_no_bot_votes.
   by move: H_bot_quorum;rewrite /nextvoters_open_for card_fseq finseq_size.

   move=>bot_voter;rewrite /nextvoters_open_for inE /= => H_bv_in.
   have[d H_recv]:= received_nextvote_open H_path H_start H_g H_u H_bv_in (leqnn _).
   by apply/(received_was_sent H_path H_start H_recv).
Qed.

(* ---------------------------------------------- *)
(* Lemmas for entering period with starting value *)
(* ---------------------------------------------- *)

(* users enter exclusively for v and u advances to p+1 implies u's starting
   value at p+1 is v *)
Lemma stv_at_entry_from_excl
      g0 trace (H_path:is_trace g0 trace)
      r (H_start: state_before_round r g0)
      p v (H_excl: period_nextvoted_exclusively_for v r p trace)
      ix uid g1 g2 (H_adv: period_advance_at ix trace uid r p.+1 g1 g2)
      u (H_u: g2.(users).[?uid] = Some u):
      u.(stv) p.+1 = Some v.
Proof using.
  clear -H_path H_start H_excl H_adv H_u.
  move: (period_advance_only_by_next_votes H_path H_start (leqnn r) H_adv).
  move => [nv_step [v0 [voters [H_creds [H_size [H_stv H_voters_voted]]]]]].
  move: H_stv => [u' [H_u' H_u'_stv]].
  move: H_u';rewrite H_u;case => ?;subst u'.
  rewrite H_u'_stv.

  destruct v0 as [v0|].
  * (* nextvote_val case *)
    apply f_equal.
    apply (proj1 H_excl nv_step voters H_creds H_size v0).
    move => voter H_voter_in H_voter_honest.
    move: (H_voters_voted _ H_voter_in) => [d H_recv].
    exact (received_was_sent H_path H_start H_recv (leqnn _) H_voter_honest).
  * (* nextvote_open case *)
    exfalso.
    apply ((proj2 H_excl) nv_step voters H_creds H_size).
    move => voter H_voter_in H_voter_honest.
    move: (H_voters_voted _ H_voter_in) => [d H_recv].
    exact (received_was_sent H_path H_start H_recv (leqnn _) H_voter_honest).
Qed.

(* users enters exclusively for v in r.p-1 and u sends a message at r.p, then
   u's starting value at p is v. *)
Lemma stv_at_send_from_excl
      g0 trace (H_path:is_trace g0 trace)
      r (H_start: state_before_round r g0)
      p (H_p_gt: 1 < p)
      v (H_excl: period_nextvoted_exclusively_for v r p.-1 trace)
      ix g1 g2 (H_step: step_in_path_at g1 g2 ix trace)
      uid msg (H_send : user_sent uid msg g1 g2)
      (H_r_msg: msg_round msg = r)
      (H_p_msg: msg_period msg = p)
      u (H_u: g1.(users).[?uid] = Some u)
      : u.(stv) p = Some v.
Proof using.
  have H_sent_at: user_sent_at ix trace uid msg by exists g1, g2;split;assumption.
  have H_honest_in := user_honest_in_from_send H_sent_at.
    rewrite H_r_msg H_p_msg in H_honest_in.

  move:(honest_in_period_entered H_path H_start H_p_gt H_honest_in) => [ix_entry [ge1 [ge2 H_entry]]].
  move:(H_entry) => [_ [_ [ukey2 [_ [_ H_ue_step]]]]].

  have H_ue := in_fnd ukey2.
  set ue:UState := ge2.(users) [`ukey2] in H_ue H_ue_step.
  move: H_ue_step => [H_r_ue H_p_ue _].
  have H_stv_entry: ue.(stv) p = Some v.
  {
    rewrite -[p](ltn_predK H_p_gt).
    refine (stv_at_entry_from_excl H_path H_start H_excl _ (in_fnd ukey2)).
    rewrite (ltn_predK H_p_gt).
    eassumption.
  }

  have H_reach: greachable ge2 g1 by eapply post_enter_reaches_sent;eassumption.
  have[H_r_u H_p_u _] := utransition_label_start H_send H_u.

  symmetry;rewrite -H_stv_entry.
  by apply (stv_forward H_reach H_ue H_u);congruence.
Qed.

(* ----------------------------------------------------------- *)
(* Vote uniqueness based on value nextvoted in previous period *)
(* ----------------------------------------------------------- *)

(* if all honest nodes that entered a period p-1 >= 2 did so exclusively for
   value v, then an honest node cannot cert-vote for any value other than v in step
   2 of period p. *)
Lemma prev_period_nextvotes_limits_honest_soft_vote
  g0 trace (H_path: is_trace g0 trace)
  r (H_start: state_before_round r g0)
  p (H_p_gt: 1 < p)
  v (H_excl: period_nextvoted_exclusively_for v r p.-1 trace):
  forall uid, honest_during_step (r,p,2) uid trace ->
  forall v', softvoted_in_path trace uid r p v' -> v' = v.
Proof.
  move => uid H_honest v' [ix H_voted].

  move: H_voted => [g1 [g2 [H_step H_send]]].
  have H_u := in_fnd (user_sent_in_pre H_send).
  set u: UState := g1.(users)[` user_sent_in_pre H_send] in H_u.

  have stv_fwd : u.(stv) p = Some v
    := stv_at_send_from_excl H_path H_start H_p_gt H_excl H_step H_send erefl erefl H_u.

  have H_g1 := step_in_path_onth_pre H_step.

  have:=utransition_label_start H_send H_u.
  unfold msg_step, msg_round, msg_period => -/= [H_r_u H_p_u _].

  have no_bot_quroums: forall s, ~nextvote_bottom_quorum u r p.-1 s. {
    rewrite -[p](ltn_predK H_p_gt) in H_p_u.
    eapply no_bottom_quorums_during_from_nextvoted_excl;eassumption.
  }

  case:(softvote_precondition H_send H_u).
  * { (* softvote_new *)
      unfold softvote_new_ok => -[_] [_] [_] [[]].
        by rewrite /cert_may_exist H_r_u H_p_u subn1.
    }
  * { (* softvote_repr *)
      unfold softvote_repr_ok => -[_] [_] [_] [_] [[H_cert _]|[_ H_stv']].
      by case:H_cert;rewrite /cert_may_exist H_r_u H_p_u subn1.
      by move:H_stv';rewrite stv_fwd => -[<-].
    }
Qed.

(* if all honest nodes that entered a period p >= 2 did so exclusively for
   value v, then an honest node cannot cert-vote for any value other than v in step
   3 of period p'. *)
Lemma prev_period_nextvotes_limits_cert_vote :
  forall g0 trace (H_path: is_trace g0 trace),
  forall r (H_start: state_before_round r g0) ,
  forall p, 1 < p ->
  forall v, period_nextvoted_exclusively_for v r p.-1 trace ->
  forall uid v',
    honest_during_step (r,p,3) uid trace ->
    certvoted_in_path trace uid r p v' -> v' = v.
Proof.
  clear.
  move => g0 trace H_path r H_start p H_p v H_excl uid v' H_honest H_vote.
  destruct H_vote as [ix_cert H_vote].

  have H_honest_in:= user_honest_in_from_send H_vote.

  unfold certvoted_in_path_at in H_vote.
  destruct H_vote as (g1_v & g2_v & H_vote_step & H_vote_send).

  have H_g2 := step_in_path_onth_post H_vote_step.
  set H_in: uid \in g2_v.(users) := user_sent_in_post H_vote_send.
  have H_u := in_fnd H_in.
  set u: UState := (g2_v.(users)[` H_in]) in H_u.


  have H_softvotes_for_v := prev_period_nextvotes_limits_honest_soft_vote H_path H_start H_p H_excl.

  have [H_in_certvals _]:= certvote_postcondition H_vote_send H_u.
  unfold certvals in H_in_certvals.

  have H_creds := softvote_credentials_checked H_path H_start H_g2 H_u (leqnn _) v' p.
  move: H_in_certvals;rewrite mem_filter /soft_weight => /andP [H_size _].
  have [uid_sv [H_in_sv H_sv_honest]] := quorum_s_has_honest trace H_creds H_size.

  apply (H_softvotes_for_v _ H_sv_honest).

  have [d H_recv]: exists d : R, msg_received uid d (Softvote, val v', r, p, uid_sv) trace.
  {
    move: H_in_sv => /imfsetP /= [[x_uid x_v] /andP [H_in_x /eqP ? /= ?]];subst x_uid x_v.
    exact (received_softvote H_path H_start H_g2 H_u H_in_x (leqnn r)).
  }

  apply (received_was_sent H_path H_start H_recv (leqnn r) H_sv_honest).
Qed.

(* --------------------------------------------------------------- *)
(* Lemmas for propagating value nextvoted for from previous period *)
(* --------------------------------------------------------------- *)

(* in p-1, all nextvotes were for v, and at step 2 in p, all softvotes were for
   v, then at all steps in p, all nextvotes were for v *)
Lemma nextvotes_val_follow_softvotes
      g0 trace (H_path: is_trace g0 trace)
      r (H_start: state_before_round r g0)
      p (H_p_gt: 1 < p)
      v (H_excl: period_nextvoted_exclusively_for v r p.-1 trace):
  (forall uid_sv : UserId,
      honest_during_step (r,p,2) uid_sv trace ->
      forall v', softvoted_in_path trace uid_sv r p v' -> v' = v) ->
  (forall uid_nv s,
      honest_during_step (r,p,s) uid_nv trace ->
      forall v', nextvoted_val_in_path trace uid_nv r p s v' -> v' = v).
Proof.
  move => H_softvotes uid_nv s H_honest_nv v' [ix_nv H_nextvoted].
  move: (H_nextvoted) => [g1 [g2 [H_step_nv H_send_nv]]].
  set H_in1 := user_sent_in_pre H_send_nv.
  set H_u1 := in_fnd H_in1.
  set u1 : UState := g1.(users)[`H_in1] in H_u1.
  change (user_sent_at ix_nv trace uid_nv (Nextvote_Val, next_val v' s, r, p, uid_nv))
       in H_nextvoted.

  case:(nextvote_val_precondition H_send_nv H_u1).
  *
    move => [_] [_] [_] [_] [_] [_] [_].
    have H_softvotes_for_v := prev_period_nextvotes_limits_honest_soft_vote H_path H_start H_p_gt H_excl.

    have H_g1 := step_in_path_onth_pre H_step_nv.
    have H_creds := softvote_credentials_checked H_path H_start H_g1 H_u1 (leqnn _) v' p.
    rewrite /certvals mem_filter /soft_weight => /andP [H_size _].
    have [uid_sv [H_in_sv H_sv_honest]] := quorum_s_has_honest trace H_creds H_size.
    apply (H_softvotes_for_v _ H_sv_honest).

    apply/(softvotes_sent H_path H_start H_g1 H_u1 (leqnn r)): H_sv_honest.
    move:H_in_sv => /imfsetP /= [] x /andP [H_x_in].
    unfold matchValue. destruct x. move => /eqP ? /= ?;subst.
    assumption.

  *
    move => [_].
    rewrite (stv_at_send_from_excl H_path H_start H_p_gt H_excl H_step_nv H_send_nv erefl erefl H_u1).
    by case => ->.
Qed.

(* users enter exclusively for v in p-1 implies users enter exclusively for v in p *)
Lemma excl_enter_excl_next:
  forall g0 trace (H_path: is_trace g0 trace),
  forall r (H_start: state_before_round r g0),
  forall (p : nat) (v : Value),
    1 < p ->
    period_nextvoted_exclusively_for v r p.-1 trace ->
    period_nextvoted_exclusively_for v r p trace.
Proof.
  move => g0 trace H_path r H_start p v H_p_gt H_prev_excl.
  simpl in H_prev_excl.

  have H_honest_softvotes: forall uid, honest_during_step (r,p,2) uid trace ->
                            forall v', softvoted_in_path trace uid r p v' ->
                                       v' = v
   := prev_period_nextvotes_limits_honest_soft_vote H_path H_start H_p_gt H_prev_excl.

  have H_nextvote_val_respects: forall uid s v', nextvoted_val_in_path trace uid r p s v' -> v' = v.
  {
    have:= (nextvotes_val_follow_softvotes H_path H_start H_p_gt H_prev_excl H_honest_softvotes).
    clear -H_path.
    move => H uid s v' H_voted.
    apply/H: (H_voted).
    move: H_voted => [ix H_voted].
    exact (honest_during_from_sent H_path H_voted).
  }

  have H_no_nextvotes_open: forall uid s, honest_during_step (r,p,s) uid trace -> ~nextvoted_bot_in_path trace uid r p s.
  {
    move => uid s H_honest [ix [g1 [g2 [H_step H_vote]]]].
    set H_u := in_fnd (user_sent_in_pre H_vote).
    set H_g1 := step_in_path_onth_pre H_step.
    have := nextvote_open_precondition H_vote H_u.
    move => [_] [_] [_] [_] [_] /(_ H_p_gt).
    have:=utransition_label_start H_vote H_u.
    unfold msg_step, msg_round, msg_period => -/=[H_r_u H_p_u H_s_u].
    rewrite subn1.
    apply (no_bottom_quorums_during_from_nextvoted_excl H_path H_start H_prev_excl H_g1 H_u H_r_u).
    by rewrite (ltn_predK H_p_gt).
  }

  by apply/(period_nextvoted_exclusively_from_nextvotes H_path).
Qed.

(* ----------------------------------------- *)
(* Propagate certificate information forward *)
(* ----------------------------------------- *)

(* cert info from saw_v at r.p remains true at g1 *)
Lemma certinfo_forward
  g0 trace (H_path: is_trace g0 trace)
  r (H_start: state_before_round r g0)
  p v uid (H_saw: saw_v trace r p v uid)
  ix g1 g2 (H_step: step_in_path_at g1 g2 ix trace)
  u (H_u: g1.(users).[? uid] = Some u)
  msg (H_send: user_sent uid msg g1 g2)
  (H_u_step: step_le (r,p,4) (msg_step msg)):
  v \in certvals u r p
  /\ exists b, b \in blocks u r /\ valid_block_and_hash b v.
Proof using.
  move: H_saw => /(@hasP _ _ trace)=> -[g_mid H_g_mid].
  case:fndP => // key_mid.
  set u_mid: UState := g_mid.(users)[`key_mid].
  move => /andP[H_v_certval_mid /andP[H_blocks_mid] /step_leP H_mid_step_le].
  set H_g1 := step_in_path_onth_pre H_step.
  set key1 := user_sent_in_pre H_send.
  rewrite (in_fnd key1) in H_u.
  case: H_u => ?;subst u.
  set u := g1.(users)[`key1].

  assert (greachable g_mid g1) as H_reach.
  {
    assert (index g_mid trace <= ix). {
      rewrite -ltnS.
      pose proof (order_ix_from_steps H_path (onth_index H_g_mid) (step_in_path_onth_post H_step)).
      apply (H _ key_mid (user_sent_in_post H_send)).

      apply (step_le_lt_trans H_mid_step_le).
      have:= (utransition_label_end H_send (in_fnd (user_sent_in_post H_send))).
      apply/step_le_lt_trans.
      assumption.
    }
    exact (at_greachable H_path H (onth_index H_g_mid) (step_in_path_onth_pre H_step)).
  }
  have H_softvotes_advance := softvotes_monotone H_reach (in_fnd key_mid) (in_fnd key1) r p.

  assert (v \in certvals u r p).
  {
    move: H_v_certval_mid.
    rewrite !mem_filter => /andP [H_size_mid H_votes_mid].
    apply/andP.
    split.
    *
      apply (leq_trans H_size_mid).
      apply fsubset_leq_card.
      apply subset_imfset.
      move => x /andP [x_mem x_prop].
      apply/andP;split;[|exact x_prop].
      move: H_softvotes_advance x_mem => /subsetP/(_ x).
        by apply.
    *
      move: H_votes_mid.
      rewrite !mem_undup.
      move/mapP => -[x H_x_in H_x2].
      apply/mapP;exists x;[|assumption].
      move: H_softvotes_advance H_x_in => /subsetP.
        by apply.
  }

  move: H_blocks_mid => /hasP [b' H_b' /asboolP H_b'_valid].
  assert (b' \in u.(blocks) r).
  {
    move: {H_b'_valid}b' H_b'.
    apply/subsetP.
    exact (blocks_monotone H_reach (in_fnd key_mid) (in_fnd key1) r).
  }

  by split;[|exists b';split].
Qed.

(* ----------------------------------- *)
(* Entering period for certified value *)
(* ----------------------------------- *)

(* v certified in p means users enter p nextvoting for v *)
Lemma certificate_is_start_of_next_period
  g0 trace (H_path: is_trace g0 trace)
  r (H_start: state_before_round r g0)
  p v (H_cert: certified_in_period trace r p v):
    period_nextvoted_exclusively_for v r p trace.
Proof.
  clear -H_path H_start H_cert.
  destruct H_cert as [certvote_quorum [H_comm [H_q_size H_vote]]].

  destruct (quorum_c_has_honest trace H_comm H_q_size) as [certvoter [H_inq H_cv_honest]].

  move:(H_vote certvoter H_inq) => [ix_cv [g1_cv [g2_cv [H_step_cv H_sent_cv]]]].

  have H_g2 := step_in_path_onth_post H_step_cv.
  have key2 := user_sent_in_post H_sent_cv.
  have H_u2 := in_fnd key2.
  set u2: UState := g2_cv.(users)[`key2] in H_u2.

  move:(certvote_postcondition H_sent_cv H_u2) => [H_certvals [[b [H_blocks H_block_valid]] H_g2_step]].

  have H_certvoters_saw_v:
    forall uid : UserId, uid \in certvote_quorum -> honest_during_step (r, p, 3) uid trace -> saw_v trace r p v uid.
  {
    move => cv2 H_in2 H_hon2.
    move: (H_vote _ H_in2) => [ix2 [g1' [g2' [H_step' H_send']]]].
    move:(certvote_postcondition H_send' (in_fnd (user_sent_in_post H_send'))) =>
    [H_certvals' [[b' [H_blocks' H_block_valid']] H_g2'_step]].
    unfold saw_v.
    apply/(@hasP GState_eqType _ trace).
    exists g2'.
    pose proof (step_in_path_onth_post H_step').
    eapply onth_in; eassumption.
    rewrite (in_fnd (user_sent_in_post H_send')).
    apply/andP;split;[|apply/andP;split].
    assumption.
      by apply/hasP;exists b';[|apply/asboolP].
    unfold step_of_ustate;move: H_g2'_step => [-> [-> ->]].
    apply/step_leP/step_le_refl.
  }

  have H_softvote_quorums_only_for_v :
    forall quorum2,
      quorum2 `<=` committee r p 2 ->
      tau_s <= #|` quorum2| ->
    forall v',
    (forall voter, voter \in quorum2 ->
                   honest_during_step (r,p,2) voter trace ->
                   softvoted_in_path trace voter r p v') ->
      v' = v.
  {
    move => q2 H_certs_q2 H_size_q2 v' H_voters_q2.
    assert (tau_s <= soft_weight v u2 r p) as H_v
        by (move: H_certvals;rewrite mem_filter => /andP [] //).
    have H_votes_checked :=
      softvote_credentials_checked H_path H_start (step_in_path_onth_post H_step_cv) H_u2 (leqnn r).
    move:(quorums_s_honest_overlap trace (H_votes_checked v p) H_v H_certs_q2 H_size_q2)
    => [common_voter [H_voter_in_q1 [H_voter_in_q2 H_voter_honest]]].

    move/(_ _ H_voter_in_q2 H_voter_honest):H_voters_q2 => {H_voter_in_q2}[ix_sv' H_voted_v'].

    move: H_voter_in_q1 => /imfsetP [[x_1 x_2]] /= /andP [H] /eqP H1 H2.
    move:H1 H2 H => {x_1}<- {x_2}<- => H_in_softvotes.

    move:(softvotes_sent H_path H_start H_g2 H_u2 (leqnn r) H_in_softvotes H_voter_honest) => [ix_sv].
    by apply (no_two_softvotes_in_p H_path H_voted_v').
  }

  have H_interquorum_v := interquorum_c_v_certinfo H_comm H_q_size H_certvoters_saw_v.
  have H_interquorum_b := interquorum_c_b_certinfo H_comm H_q_size H_certvoters_saw_v.

  split.
  (* For value votes:
     By interquorum assumptions, any nextvote quorum contains an honest voter
     which (would have) certvoted for v in step 3.
       Having seen a quorum of softvotes rules out an stv-based nextvote.
       A quorum of softvotes for the v' they voted for
       would have honest overlap with the softvote v quorum
       so by no_two_softvotes_in_p we have v = v'.
   *)
  {
  move => s nextvoters H_nv_creds H_nv_size v' H_nv_voted.
  move: H_interquorum_v => /(_ r p s _ H_nv_creds H_nv_size)
    => -[uid_nv [H_in_nv [H_saw_v H_honest]]].
  move:H_nv_voted =>/(_ _ H_in_nv H_honest){H_in_nv} [ix_nv [g1_nv [g2_nv [H_step_nv H_send_nv]]]].

  set key1_nv := user_sent_in_pre H_send_nv.
  set u1_nv := g1_nv.(users)[` key1_nv].

  case:(nextvote_val_precondition H_send_nv (in_fnd key1_nv)) => [[b0]|].
  * (* nextvote_val_ok *)
    unfold nextvote_val_ok => -[_] [_] [_] [_] [_] [_].
    unfold certvals.
    rewrite !mem_filter => /andP [H_sv_size H_sv_votes].
    have H_sv_creds := (softvote_credentials_checked H_path H_start
         (step_in_path_onth_pre H_step_nv) (in_fnd key1_nv) (leqnn r) v' p).

    apply (H_softvote_quorums_only_for_v _ H_sv_creds H_sv_size).

    have:= softvotes_sent H_path H_start (step_in_path_onth_pre H_step_nv) (in_fnd key1_nv) (leqnn r).
    clear.
    move=> H_sv_sent voter H_in.
    apply H_sv_sent.
      by move: H_in => /imfsetP [[x0 x1] /andP [H_in /eqP ->] /= ->].
  * (* nextvote_stv_ok *)
    unfold nextvote_stv_ok => -[] [_] [_] [_] [H_s] [/(_ v)H_no_good_certvals _] _.
    have H_good_certval := certinfo_forward H_path H_start H_saw_v H_step_nv (in_fnd key1_nv) H_send_nv.
    unfold msg_step, msg_round, msg_period in H_good_certval;cbn -[step_le] in H_good_certval.
    have: step_le (r,p,4) (r,p,s) by apply/step_leP;rewrite /= !ltnn !eq_refl H_s /=.
    move/H_good_certval => [H_v_certval [b0 [H_b0_blocks H_b0_valid]]].
    exfalso.
    exact (H_no_good_certvals H_v_certval _ H_b0_blocks H_b0_valid).
  }

  (* For no bottom votes:
     By interquorum assumption, any nextvote quorum contains an honest voter
     which (would have) certvoted for v in step 3.
       Having seen enough softvotes violates the precondition for voting for bottom.
   *)
  {

  move => s bot_voters H_bot_creds H_bot_size H_bot_voted.
  move: H_interquorum_b
    => /(_ r p s _ H_bot_creds H_bot_size){H_bot_creds H_bot_size}
    => -[honest_bot_voter [H_honest_in [H_honest_saw H_honest_honest]]].
  move: H_bot_voted => /(_ _ H_honest_in H_honest_honest){H_honest_in}
                       [ix_nv [g1_nv [g2_nv [H_step_nv H_send_nv]]]].


  set key1_nv := user_sent_in_pre H_send_nv.
  set u1_nv := g1_nv.(users)[` key1_nv].

  have := nextvote_open_precondition H_send_nv (in_fnd key1_nv).
  move => -[_] [_] [_] [H_s] [/(_ v)H_no_good_certvals _].

  have H_good_certval := certinfo_forward H_path H_start H_honest_saw H_step_nv (in_fnd key1_nv) H_send_nv.
  unfold msg_step, msg_round, msg_period in H_good_certval;cbn -[step_le] in H_good_certval.
  have: step_le (r,p,4) (r,p,s) by apply/step_leP;rewrite /= !ltnn !eq_refl H_s /=.
  move/H_good_certval => [H_v_certval [b0 [H_b0_blocks H_b0_valid]]].
  exfalso.
  exact (H_no_good_certvals H_v_certval _ H_b0_blocks H_b0_valid).
  }
Qed.

(* v certified in r.p means users enter all p' >= p nextvoting for v *)
Lemma certificate_is_start_of_later_periods
  trace g0  (H_path: is_trace g0 trace)
  r (H_start: state_before_round r g0):
  forall p,  1 <= p ->
  forall v,
    certified_in_period trace r p v ->
  forall p', p <= p' ->
    period_nextvoted_exclusively_for v r p' trace.
Proof.
  move => p H_p v H_cert p' H_p_lt.
  have: p' = (p + (p' - p))%nat by symmetry;apply subnKC.
  move: (p' - p)%nat => n {p' H_p_lt}->.
  elim:n.
  (* Next step after certification *)
  by rewrite addn0;apply/(certificate_is_start_of_next_period H_path).
  (* Later steps *)
  move => n;rewrite addnS.
  apply (excl_enter_excl_next H_path H_start (p:=(p+n).+1)).
  by rewrite ltnS addn_gt0 H_p.
Qed.

(* -------------------------- *)
(* One certificate per period *)
(* -------------------------- *)

(* only one value can be certified in a given r.p pair *)
Lemma one_certificate_per_period: forall g0 trace r p,
    state_before_round r g0 ->
    is_trace g0 trace ->
    forall v1, certified_in_period trace r p v1 ->
    forall v2, certified_in_period trace r p v2 ->
    v1 = v2.
Proof.
  clear.
  intros g0 trace r p H_start H_path v1 H_cert1 v2 H_cert2.
  destruct H_cert1 as (quorum1 & H_q1 & H_size1 & H_cert1).
  destruct H_cert2 as (quorum2 & H_q2 & H_size2 & H_cert2).
  pose proof (quorums_c_honest_overlap trace H_q1 H_size1 H_q2 H_size2).
  destruct H as (voter & H_common1 & H_common2 & H_honest).
  specialize (H_cert1 _ H_common1).
  specialize (H_cert2 _ H_common2).
  destruct H_cert1 as [ix1 H_cert1].
  destruct H_cert2 as [ix2 H_cert2].

  assert (user_honest_at ix1 trace voter) as H_honest1. {
  move: H_cert1.
  unfold certvoted_in_path_at. move => [g1 [g2 [H_step H_vote]]].

  pose proof (in_fnd (user_sent_in_pre H_vote)) as H0.
  set ustate := g1.(users)[`user_sent_in_pre H_vote] in H0.
  clearbody ustate.
  have H1: (step_of_ustate ustate) = (r,p,3) := utransition_label_start H_vote H0.

  pose proof (honest_at_from_during H_honest H_path) as H.
  specialize (H _ _ (step_in_path_onth_pre H_step)).
  specialize (H _ H0).
  apply H.
  rewrite H1.
  apply step_le_refl.
  }

  assert (user_honest_at ix2 trace voter) as H_honest2. {
  move: H_cert2.
  unfold certvoted_in_path_at. move => [g1 [g2 [H_step H_vote]]].
  pose proof (honest_at_from_during H_honest H_path) as H.
  specialize (H _ _ (step_in_path_onth_pre H_step)).
  pose proof (in_fnd (user_sent_in_pre H_vote)).
  set ustate := g1.(users)[`user_sent_in_pre H_vote] in H0.
  clearbody ustate.
  specialize (H _ H0).
  apply H.
  rewrite (utransition_label_start H_vote H0);apply step_le_refl.
  }

  by destruct (no_two_certvotes_in_p H_path H_cert1 H_honest1 H_cert2 H_honest2).
Qed.

(* ------ *)
(* SAFETY *)
(* ------ *)

(* The safety theorem: only one value can be certified in each round. This means
   that at most one block is approved in a given round. *)
Theorem safety : forall (g0 : GState) (trace : seq GState) (r : nat),
  state_before_round r g0 ->
  is_trace g0 trace ->
  forall (p1 : nat) (v1 : Value), certified_in_period trace r p1 v1 ->
  forall (p2 : nat) (v2 : Value), certified_in_period trace r p2 v2 ->
  v1 = v2.
Proof.
  intros g0 trace r H_start H_path p1 v1 H_cert1 p2 v2 H_cert2.
  wlog: p1 v1 H_cert1 p2 v2 H_cert2 / (p1 <= p2).
  { (* showing this suffices *)
  intros H_narrowed.
  destruct (p1 <= p2) eqn:H_test;[|symmetry];eapply H_narrowed;try eassumption.
  apply ltnW. rewrite ltnNge. rewrite H_test. done.
  }
  (* Continuing proof *)
  intro H_le.
  destruct (eqVneq p1 p2).
  * (* Two blocks certified in same period. *)
  subst p2; clear H_le.
  eapply one_certificate_per_period;eassumption.
  *
  (* Second certificate produced in a later period *)
  assert (p1 < p2) as Hlt by (rewrite ltn_neqAle;apply /andP;split;assumption).
  clear H_le i.
  assert (1 <= p1) as H_p1.
  {
    move: H_cert1 => [quorum_p1 [H_creds [H_size _]]].
    move: (quorum_c_has_honest trace H_creds H_size) => [voter1 [H_in _]].
    move: H_creds => /fsubsetP /(_ _ H_in) /imfsetP [x H H_x].
    move: H_x H => {x}<- /asboolP.
    apply credentials_valid_period.
  }
  have H_p2: p1 <= p2.-1 by rewrite -ltnS (ltn_predK Hlt).

  destruct (nosimpl H_cert2) as (q2 & H_q2 & H_size2 & H_cert2_voted).
  destruct (quorum_c_has_honest trace H_q2 H_size2)
     as (honest_voter & H_honest_q & H_honest_in).

  specialize (H_cert2_voted honest_voter H_honest_q).
  destruct (nosimpl H_cert2_voted) as (ix & ga1 & ga2 & [H_step2 H_send_vote2]).
  assert (honest_in_period r p2 honest_voter trace)
   by (eapply honest_in_from_during_and_send;[eassumption..|apply step_le_refl]).

  symmetry.
  have H_p2': 1 < p2 by apply (leq_trans (n:=p1.+1));[rewrite ltnS|].
  have H_excl := certificate_is_start_of_later_periods H_path H_start H_p1 H_cert1 H_p2.
  exact (prev_period_nextvotes_limits_cert_vote H_path H_start H_p2' H_excl H_honest_in H_cert2_voted).
Qed.
