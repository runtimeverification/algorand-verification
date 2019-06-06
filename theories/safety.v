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
Require Import algorand_model safety_helpers quorums.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section AlgoSafety.

(* internal transition does not change corrupt flag *)
Lemma utransition_internal_preserves_corrupt uid pre post sent:
  uid # pre ~> (post,sent) -> pre.(corrupt) = post.(corrupt).
Proof using.
  set result:=(post,sent). change post with (result.1). clearbody result.
  destruct 1;reflexivity.
Qed.

(* message transition does not change corrupt flag *)
Lemma utransition_msg_preserves_corrupt uid msg pre post sent:
  uid # pre ; msg ~> (post,sent) -> pre.(corrupt) = post.(corrupt).
Proof using.
  set result:=(post,sent). change post with (result.1). clearbody result.
  destruct 1;try reflexivity.
  + unfold deliver_nonvote_msg_result;simpl.
    destruct msg as [[[[? ?] ?] ?] ?];simpl.
    destruct e;[destruct m|..];reflexivity.
Qed.

Definition step_at path ix lbl :=
  exists g1 g2,
    step_in_path_at g1 g2 ix path
    /\ related_by lbl g1 g2.

Definition msg_received uid msg_deadline msg path : Prop :=
  exists n ms, step_at path n
   (lbl_deliver uid msg_deadline msg ms).

Definition received_next_vote u voter round period step value path : Prop :=
  exists d, msg_received u d ((match value with
                               | Some v => (Nextvote_Val,next_val v step)
                               | None => (Nextvote_Open,step_val step)
                               end),round,period,voter) path.

Ltac unfold_step_result :=
  unfold tick_update, tick_users.

Lemma corrupt_preserved_ustep_msg : forall uid upre msg upost,
    uid # upre ; msg ~> upost ->
    upre.(corrupt) -> upost.1.(corrupt).
Proof using.
  destruct 1;simpl;try done.
  * (* Only one case remains *)
  unfold deliver_nonvote_msg_result;simpl.
  destruct msg as [[[[? ?] ?] ?] ?];simpl.
  destruct e;[destruct m|..];unfold set_blocks,set_proposals;simpl;done.
Qed.

Lemma corrupt_preserved_ustep_internal : forall uid upre upost,
    uid # upre ~> upost ->
    upre.(corrupt) -> upost.1.(corrupt).
Proof using.
  by destruct 1.
Qed.

Lemma honest_backwards_gstep : forall (g1 g2 : GState),
    GTransition g1 g2 ->
    forall uid, user_honest uid g2 ->
                user_honest uid g1.
Proof using.
  move => g1 g2 Hstep uid.
  destruct Hstep;unfold user_honest;destruct pre;
    unfold_step_result;simpl global_state.users in * |- *;try done.
  + (* step_tick *)
    destruct (fndP users uid).
    by rewrite updf_update //;destruct (users.[kf]), corrupt.
    by rewrite not_fnd // -[uid \in _]/(uid \in domf _) -updf_domf.
  + (* step_deliver_msg UTransitionMsg *)
  rewrite fnd_set.
  destruct (@eqP (Finite.choiceType UserId) uid uid0);[|done].
  subst uid0;rewrite (in_fnd key_ustate).
  by move/negP: H0.
  + (* step_internal UTransitionInternal *)
  rewrite fnd_set.
  destruct (@eqP (Finite.choiceType UserId) uid uid0);[|done].
  subst uid0;rewrite (in_fnd ustate_key).
  apply/contraNN => H1. by apply corrupt_preserved_ustep_internal in H0.
  + (* step_corrupt_user *)
  rewrite fnd_set.
  by destruct (@eqP (Finite.choiceType UserId) uid uid0).
Qed.

Lemma honest_last_all uid g0 p (H_path : is_trace g0 p):
    user_honest uid (last g0 p) ->
    all (user_honest uid) (g0::p).
Proof using.
  move => H_honest.
  destruct p. inversion H_path.
  destruct H_path as [H_g0 H_path]; subst.
  revert H_honest.
  elim/last_ind: p H_path => [|s x IH] /=; first by move=> _ ->.
  rewrite rcons_path last_rcons all_rcons.
  move/andP => [Hpath Hstep] Hx.
  specialize (IH Hpath).
  rewrite Hx.
  apply IH. by apply/honest_backwards_gstep /asboolP: Hx.
Qed.
Arguments honest_last_all uid [g0] [p].

Lemma honest_monotone uid g1 g2:
  greachable g1 g2 ->
  user_honest uid g2 ->
  user_honest uid g1.
Proof.
  move => [p H_path H_last] H_honest2.
  subst g2.
  pose proof (honest_last_all uid H_path H_honest2).
  by move: H => /andP [].
Qed.

Lemma path_steps : forall {T} (R : rel T) x0 p,
    path R x0 p ->
    forall (P : pred T),
    ~~ P x0 -> P (last x0 p) ->
    exists n,
      match drop n (x0 :: p) with
      | x1 :: x2 :: _ => ~~ P x1 && P x2
      | _ => false
      end.
Proof using.
  clear.
  intros T R x0 p H_path P H_x0.
  revert p H_path. induction p using last_ind.
  * simpl. intros _ H_b. exfalso. revert H_b. apply /negP. assumption.
  * rewrite last_rcons. rewrite rcons_path.
    move => /andP [H_path H_step] H_x.
    destruct (P (last x0 p)) eqn:H_last.
  + destruct IHp as [n' Hind];[done..|]. exists n'.
    destruct n';simpl in Hind |- *. destruct p;[by exfalso|assumption].
    destruct (ltnP n' (size p));[|by (rewrite drop_oversize in Hind)].
    rewrite drop_rcons;[destruct (drop n' p) as [|? [|]];[done..|tauto]|].
    apply ltnW;assumption.
  + clear IHp. exists (size p).
    destruct (size p) eqn:H_size. simpl.
    rewrite (size0nil H_size) in H_last |- *. simpl. by apply/andP.
    simpl.
    rewrite (drop_nth x0).
    rewrite <- cats1, <- H_size.
    rewrite drop_size_cat;[|reflexivity].
    rewrite nth_cat.
    rewrite H_size ltnSn.
    change n with (n.+1.-1).
    rewrite <- H_size, nth_last, H_last.
    simpl. assumption.
    rewrite size_rcons H_size.
    rewrite ltnS. apply leqnSn.
Qed.

Lemma path_prefix : forall T R p (x:T) n,
    path R x p -> path R x (take n p).
Proof using.
  induction p;[done|].
  move => /= x n /andP [Hr Hpath].
  destruct n. done.
  simpl;apply /andP;by auto.
Qed.

Lemma is_trace_prefix : forall trace g0 n,
    is_trace g0 trace -> n > 0 -> is_trace g0 (take n trace).
Proof.
  clear.
  induction trace;[done|].
  destruct n. done.
  simpl.
  unfold is_trace.
  move => [H_g0 H_path] _.
  split;[done|by apply path_prefix].
Qed.

Lemma is_trace_drop g0 g0' trace trace' (H_trace: is_trace g0 trace) n:
  drop n trace = g0' :: trace' -> is_trace g0' (g0' :: trace').
Proof using.
  move => H_drop.
  destruct trace. inversion H_trace.
  destruct H_trace as [H_g0 H_trace]; subst.
  eapply path_drop' with (n:=n) in H_trace.
  unfold is_trace.
  destruct n.
    by rewrite drop0 in H_trace; rewrite drop0 in H_drop; inversion H_drop; subst.
    by rewrite H_drop in H_trace.
Qed.

Lemma path_gsteps_onth
      g0 trace (H_path : is_trace g0 trace)
      ix_p g_p (H_g_p : onth trace ix_p = Some g_p):
    forall (P : pred GState),
    ~~ P g0 -> P g_p ->
    (* exists n g1 g2, step_in_path_at g1 g2 n (g0::trace) /\ ~~ P g1 /\ P g2. *)
    exists n g1 g2, step_in_path_at g1 g2 n trace /\ ~~ P g1 /\ P g2.
Proof using.
  destruct trace;[by contradict H_path|].
  move: H_path => [H_g0 H_path];subst g.
  move=> P H_NPg0 H_Pg.
  have H_path' := path_prefix ix_p H_path.
  destruct ix_p as [|ix_p];
    first by exfalso;move:H_g_p H_NPg0;case => ->;rewrite H_Pg.
  change (onth trace ix_p = Some g_p) in H_g_p.

  pose proof (path_steps H_path' H_NPg0).
  have H_size_trace := onth_size H_g_p.
  rewrite -nth_last nth_take size_takel // (onth_nth H_g_p) in H.
  specialize (H H_Pg).
  move:H;clear -H_NPg0;move => [n H].

  exists n.
  unfold step_in_path_at.
  destruct (drop n (g0 :: take ix_p.+1 trace)) as [|x l] eqn: H_eq;[|destruct l];[done..|].
  rewrite -[g0::trace](cat_take_drop ix_p.+2).
  move/andP in H;exists x, g;split;[|assumption].
  rewrite drop_cat.
  case:ifP;[rewrite H_eq;done|].
  move => /negP /negP /=;rewrite ltnS -ltnNge => H_oversize.
  by rewrite drop_oversize // in H_eq.
Qed.

(* To show there is not a fork in a particular round,
   we will take a history that extends before any honest
   node has made a transition in that round *)
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

Definition opred (T : Type) (P : pred T) : pred (option T) :=
  fun o => match o with
           | None => false
           | Some v => P v
           end.

Definition is_pending (target:UserId) (msg_body:Msg) : pred GState :=
  fun g => opred (fun (ms:{mset R * Msg}) => has (fun p => p.2 == msg_body) ms)
                 (g.(msg_in_transit).[?target]).

(*
(* possible lemmas for pending_honest_sent *)
Lemma new_msg_from_send_or_replay g1 g2 (H_step: g1 ~~> g2):
    forall target (key_msg2 : target \in g2.(msg_in_transit)) d pending_msg,
      (d,pending_msg) \in g2.(msg_in_transit).[key_msg2] ->
    (forall (key_msg1 : target \in g1.(msg_in_transit)),
      (d,pending_msg) \notin g1.(msg_in_transit).[key_msg1]) ->
    let sender := msg_sender pending_msg in
    user_honest sender g1 ->
    user_sent sender pending_msg g1 g2
    \/ pending_msg \in g1.(msg_history).
Proof using.
Abort.

Definition pending_in_history_after (r:nat)
           (msg_in_transit:{fmap UserId -> {mset R * Msg}}) (msg_history:{mset Msg}) : Prop :=
  forall uid (key : uid \in msg_in_transit) d pending_msg,
    (d,pending_msg) \in msg_in_transit.[key] ->
  r <= msg_round pending_msg ->
  pending_msg \in msg_history.

Lemma pending_in_history_after_invariant g1 g2 (H_step: g1 ~~> g2):
  forall r, pending_in_history_after r (g1.(msg_in_transit)) (g1.(msg_history))
         -> pending_in_history_after r (g2.(msg_in_transit)) (g2.(msg_history)).
Proof using.
  clear -H_step.
  destruct H_step;try exact (fun r H => H);autounfold with gtransition_unfold;destruct pre;simpl in * |- *.
  * move => r H_pending.
    unfold pending_in_history_after.
    move => uid0 key d pending_msg H_msg H_r.

    assert (uid0 \in domf msg_in_transit).
    move:(key). rewrite -!fsub1set => key'. refine (fsubset_trans key' _).
    apply send_broadcasts_domf. admit.
    rewrite dom_setf mem_fset1U //.
  (*  SearchAbout domf setf.
    apply send_i
    specialize (H_pending uid0). *)
Abort.

Lemma pending_in_history g0 trace (H_path: path gtransition g0 trace)
    r (H_start:state_before_round r g0):
    forall g ix,
      onth trace ix = Some g ->
    forall uid (key : uid \in g.(msg_in_transit)) d pending_msg,
      (d,pending_msg) \in g.(msg_in_transit).[key] ->
    r <= msg_round pending_msg ->
    pending_msg \in g.(msg_history).
Proof.
  move => g ix H_g uid key d pending_msg H_pending H_r.
  have H_path' := path_prefix ix.+1 H_path.
  have H_last := onth_take_last H_g g0.
Abort.
*)

Lemma utransition_msg_sender_good uid u msg result:
  uid # u ; msg ~> result ->
  forall m, m \in result.2 -> uid = msg_sender m.
Proof using.
  clear.
  by destruct 1 => /= m /Iter.In_mem /=;intuition;subst m.
Qed.

Lemma utransition_internal_sender_good uid u result:
  uid # u ~> result ->
  forall m, m \in result.2 -> uid = msg_sender m.
Proof using.
  clear.
  by destruct 1 => /= m /Iter.In_mem /=;intuition;subst m.
Qed.

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

Definition user_forged (msg:Msg) (g1 g2: GState) :=
  let: (mty,v,r,p,sender) := msg in
  related_by (lbl_forge_msg sender r p mty v) g1 g2.

Lemma broadcasts_prop
  uid (msg:Msg) (l:seq Msg)
  time (targets : {fset UserId}) (mailboxes' mailboxes : {fmap UserId -> {mset R * Msg}}):
  (odflt mset0 mailboxes'.[? uid] `<=` odflt mset0 mailboxes.[? uid])%mset ->
  match (send_broadcasts time targets mailboxes' l).[? uid] with
  | Some msg_mset => has (fun p : R * Msg => p.2 == msg) msg_mset
  | None => false
  end ->
  ~~
  match mailboxes.[? uid] with
  | Some msg_mset => has (fun p : R * Msg => p.2 == msg) msg_mset
  | None => false
  end -> msg \in l.
Proof using.
  clear.
  move => H_sub H_pre H_post.
  have{H_post}H_post: ~~has (fun p: R * Msg => p.2 == msg) (odflt mset0 mailboxes.[?uid])
    by case:fndP H_post;[|rewrite enum_mset0].

  rewrite send_broadcastsE in H_pre.
  case:mailboxes'.[?uid]/fndP => H_mb';
   [|by move:H_pre;rewrite not_fnd //;
     congr (uid \notin _): H_mb';apply updf_domf].

  have{H_post}H_post: ~~has (fun p: R * Msg => p.2 == msg) (mailboxes'.[H_mb'])
    by apply/contraNN:H_post => /hasP /= [x H_in H_x];
       apply/hasP;exists x;[apply (msubset_subset H_sub);rewrite in_fnd|].

  move: {mailboxes H_sub}H_pre.

  case:(uid \in targets)/boolP=>H_tgt;
    [|by apply contraTT;rewrite updf_update'].

  rewrite updf_update {targets H_tgt}// => /hasP /=[[d msg'] H_in /eqP /=H_msg].
  move:H_msg H_in=> {msg'}-> /in_merge_msgs [//|H_in].

  move/negP in H_post;contradict H_post.
  by apply /hasP;exists (d,msg).
Qed.

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

(* A message from an honest user was actually sent in the trace *)
(* Use this to relate an honest user having received a quorum of messages
   to some honest user having sent those messages *)
(* Hopefully the statement can be cleaned up *)
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

(*
   This lemma connects message receipt to the sending of a message,
   used to reach back to an earlier honest transition.
 *)
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

Definition ustate_after us1 us2 : Prop :=
  us1.(round) < us2.(round)
  \/ (us1.(round) = us2.(round) /\ us1.(period) < us2.(period))
  \/ (us1.(round) = us2.(round) /\ us1.(period) = us2.(period) /\ us1.(step) <= us2.(step)).

Lemma ustate_after_iff_step_le u1 u2:
  step_le (step_of_ustate u1) (step_of_ustate u2)
  <-> ustate_after u1 u2.
Proof using.
  unfold ustate_after;destruct u1, u2;simpl.
  clear;tauto.
Qed.

Lemma utransition_label_start uid msg g1 g2 :
    user_sent uid msg g1 g2 ->
    forall u, g1.(users).[? uid] = Some u ->
    (step_of_ustate u) = (msg_step msg).
Proof using.
  unfold user_sent.
  move => [sent [msg_in H_trans]] u H_u.
  destruct msg as [[[[mtype v] r] p] uid_m].
  case: H_trans => [[d [body H_recv]]|H_step].
  * { (* message delivery cases *)
  destruct H_recv as (key_ustate & ustate_post & H_step & H_honest
                     & key_mailbox & H_msg_in_mailbox & ->).
  destruct g1;simpl in * |- *.
  unfold step_of_ustate.
  rewrite in_fnd in H_u. injection H_u;clear H_u. intros <-.

  remember (ustate_post,sent) as ustep_out in H_step.
  destruct H_step;injection Hequstep_out;clear Hequstep_out;intros <- <-;
    try (exfalso;exact (notF msg_in)).

  (* Only one delivery transition actually sends a message *)
  move/Iter.In_mem in msg_in;case: msg_in => [[*]|[]];subst.
  unfold certvote_ok in H;decompose record H;clear H.
  revert H0.
  clear;unfold pre',valid_rps;autounfold with utransition_unfold;simpl;clear.
  move => [-> [->  ->]];reflexivity.
  }
  * { (* internal transition cases *)
    destruct H_step as (key_user & ustate_post & H_honest & H_step & ->).
    destruct g1;simpl in * |- *.
    rewrite in_fnd in H_u;injection H_u;clear H_u.
    intro H. rewrite -> H in * |- *. clear key_user users H.
    move/Iter.In_mem in msg_in.
    clear -msg_in H_step.

    unfold step_of_ustate.
    remember (ustate_post,sent) as ustep_out in H_step;
      destruct H_step;
    injection Hequstep_out;clear Hequstep_out;intros <- <-;
    let rec use_mem H :=
      first [exfalso;exact H

      |destruct H as [H|H];[injection H as <- <- <- <- <-|use_mem H]]
    in use_mem msg_in;
    autounfold with utransition_unfold in H;
      decompose record H;clear H;
    match goal with
    | [H:valid_rps _ _ _ _ |- _] => unfold valid_rps in H;move: H
    | [H:advancing_rp _ _ _ |- _] => unfold advancing_rp in H;move :H
    end;clear;simpl;move=> [-> [-> ->]];reflexivity.
  }
Qed.

Lemma utransition_label_end : forall uid msg g1 g2,
    user_sent uid msg g1 g2 ->
    forall u, g2.(users).[? uid] = Some u ->
    step_lt (msg_step msg) (step_of_ustate u).
Proof using.
  move => uid msg g1 g2.
  unfold user_sent.
  move => [sent [msg_in H_trans]] u H_u.
  destruct msg as [[[[mtype v] r] p] uid_m].
  case: H_trans => [[d [body H_recv]]|H_step].
  * { (* message delivery cases *)
  destruct H_recv as (key_ustate & ustate_post & H_step & H_honest
                     & key_mailbox & H_msg_in_mailbox & ->).
  revert H_u. rewrite fnd_set eq_refl. case => {u}<-.

  destruct g1;cbn -[in_mem mem eq_op] in * |- *.
  remember (ustate_post,sent) as ustep_out in H_step.
  destruct H_step;injection Hequstep_out;clear Hequstep_out;intros <- <-;
  try (exfalso;exact (notF msg_in));
  match type of msg_in with
  | is_true (_ \in [:: _]) =>
    unfold in_mem in msg_in; simpl in msg_in;
      rewrite Bool.orb_false_r in msg_in;
      apply (elimT eqP) in msg_in;
      injection msg_in;clear msg_in;
      intros -> -> -> -> ->
  end.

  autounfold with utransition_unfold in H. decompose record H.
  revert H0;subst pre';clear;unfold valid_rps;destruct pre;simpl.
    by intuition.
  }
  * { (* internal transition cases *)
  destruct H_step as (key_user & ustate_post & H_honest & H_step & ->).
  revert H_u. rewrite fnd_set eq_refl. case => {u}<-.

  destruct g1;cbn -[in_mem mem eq_op] in * |- *.
  move/Iter.In_mem in msg_in.

  clear -msg_in H_step.
  remember (ustate_post,sent) as ustep_out in H_step.
  destruct H_step;
  injection Hequstep_out;clear Hequstep_out;intros <- <-;
   let rec use_mem H :=
       first [exfalso;exact H
      |destruct H as [H|H];[injection H as <- <- <- <- <-|use_mem H]]
  in use_mem msg_in;
    autounfold with utransition_unfold in H;
    decompose record H;clear H;
    match goal with
    | [H:valid_rps _ _ _ _ |- _] => move: H; unfold valid_rps
    | [H:advancing_rp _ _ _ |- _] => move: H; unfold advancing_rp
    end;clear;destruct pre;simpl;clear;move=> [-> [-> H_step_val]];
    repeat (split || right);
      by rewrite addn1 ltnSn.
  }
Qed.

Lemma utransition_label_correctly : forall uid msg g1 g2,
    user_sent uid msg g1 g2 ->
    forall u, g1.(users).[? uid] = Some u ->
    match msg with
    | (Certvote,_,r_m,p_m,uid_m) =>
      ((r_m > u.(round)) \/ (r_m = u.(round) /\ p_m >= u.(period)))
        /\ uid_m = uid
    | (_,v,r_m,p_m,uid_m) =>
      r_m = u.(round) /\ p_m = u.(period) /\  uid_m = uid
      /\ match v with
         | val _ => True
         | step_val s_m => s_m = u.(step)
         | repr_val _ _ p_m => p_m = u.(period)
         | next_val _ s_m => s_m = u.(step)
         end
    end.
Proof using.
  move=> uid msg g1 g2.
  rewrite /user_sent.
  move => [sent [msg_in H_trans]] u H_u.
  change (msg \in sent:Prop) in msg_in.
  destruct msg as [[[[mtype v] r] p] uid_m].
  case: H_trans => [[d [body H_recv]]|H_step].
  * { (* message delivery cases *)
  destruct H_recv as (key_ustate & ustate_post & H_step & H_honest
                     & key_mailbox & H_msg_in_mailbox & ->).
  destruct g1;simpl in * |- *.
  rewrite in_fnd in H_u. injection H_u;clear H_u. intros <-.

  remember (ustate_post,sent) as ustep_out in H_step.
  destruct H_step;injection Hequstep_out;clear Hequstep_out;intros <- <-;
  try (exfalso;exact (notF msg_in));
  match type of msg_in with
  | is_true (_ \in [:: _]) =>
    unfold in_mem in msg_in; simpl in msg_in;
      rewrite Bool.orb_false_r in msg_in;
      apply (elimT eqP) in msg_in;
      injection msg_in;clear msg_in;
      intros -> -> -> -> ->
  end;
  match goal with [x : algorand_model.UState |- _] =>
  match goal with [x' := context C [?f x] |- _] =>
  match goal with [H : context C [?g x'] |- _] =>
     destruct x;subst x';unfold f,g in H;simpl in H;
     decompose record H;clear H
  end
  end
  end;simpl;
  match goal with
  | [H : valid_rps _ _ _ _ |- _] => move:H;unfold valid_rps;
      simpl;clear;
    by intuition;subst;intuition
  | _ => idtac
  end.
  }
  * { (* internal transition cases *)
    destruct H_step as (key_user & ustate_post & H_honest & H_step & ->).
    destruct g1;simpl in * |- *.
    rewrite in_fnd in H_u;injection H_u;clear H_u. intros <-.
    move/Iter.In_mem in msg_in.
    clear -msg_in H_step.

    remember (ustate_post,sent) as ustep_out in H_step;
    destruct H_step;
    injection Hequstep_out;clear Hequstep_out;intros <- <-;
    let rec use_mem H :=
      first [exfalso;exact H

      |destruct H as [H|H];[injection H as <- <- <- <- <-|use_mem H]]
    in use_mem msg_in;
    match goal with
    | [pre : algorand_model.UState |- _] =>
      is_var pre;
        match goal with
        |[H : context C [?f pre] |- _] =>
         unfold f in H;decompose record H;
           match goal with
           | [H:valid_rps _ _ _ _ |- _] => unfold valid_rps in H;clear -H pre
           | [H:advancing_rp _ _ _ |- _] => unfold advancing_rp in H;clear -H pre
           end;
           destruct pre;simpl in * |- *
        end
    end;by intuition;subst;intuition.
    }
Qed.

(** Now we have lemmas showing that transitions preserve various invariants *)

Definition user_timers_valid : pred UState :=
  fun u =>
    (Rleb 0 u.(p_start) &&
     Rleb u.(timer) u.(deadline) ).

(* Sensible states *)
(* This notion specifies what states can be considered valid states. The idea
   is that we only consider execution traces that begin at sensible states,
   since sensibility is preserved by the transition system (to be shown), the
   set of reachable states will also be sensible (to be shown). This means that
   it is not important which specific state is assumed as the initial state as
   long as the state is sensible.
   Note: the traditional operational notion of an initial state is a now a
   special case of sensibility *)
Definition sensible_ustate (us : UState) : Prop :=
  (us.(p_start) >= 0)%R /\
  (0 <= us.(timer) <= us.(deadline))%R .

Definition sensible_gstate (gs : GState) : Prop :=
  (gs.(now) >= 0)%R /\
  ~ gs.(users) = [fmap] /\
  domf gs.(msg_in_transit) `<=` domf gs.(users) /\ (* needed? *)
  forall uid (k:uid \in gs.(users)), sensible_ustate gs.(users).[k].
  (* more constraints if we add corrupt users map and total message history *)

Lemma step_later_deadlines : forall s,
    s > 3 -> next_deadline s = (lambda + big_lambda + (INR s - 3) * L)%R.
Proof using.
  intros s H_s; clear -H_s.
  unfold next_deadline.
  do 3 (destruct s;[exfalso;apply not_false_is_true;assumption|]).
  reflexivity.
Qed.

(* The user transition relation preserves sensibility of user states *)
Lemma utr_msg_preserves_sensibility : forall uid us us' m ms,
  sensible_ustate us -> uid # us ; m ~> (us', ms) ->
  sensible_ustate us'.
Proof.
  intros uid us us' m ms H_sensible Hstep;
  remember (us',ms) as ustep_output eqn:H_output;
  destruct Hstep; injection H_output; intros; subst;
  match goal with
  | [H_sensible : sensible_ustate ?s |- _] => is_var s;
     destruct s;unfold sensible_ustate in * |- *;
     decompose record H_sensible;clear H_sensible;simpl in * |- *
  end;
  autounfold with utransition_unfold in * |- *;
  match goal with
  | [H : context C [valid_rps] |- _] => unfold valid_rps in H;simpl in H;decompose record H
  | _ => idtac
  end;
  try by intuition lra.
  (* deliver nonvote msg needs some custom steps *)
  clear H_output.
  destruct msg as [[[[mtype ex_val] ?] ?] ?];
    destruct ex_val;simpl;[destruct mtype;simpl|..];intuition lra.
Qed.

(* SAFETY *)

(* An honest user may cert-vote only at step 3 of a period *)
(* Certvoting is enabled only at step 3 *)
Lemma certvote_only_in_step3 : forall us uid v b r p,
  certvote_ok us uid v b r p -> us.(step) = 3.
Proof using.
move => us uid v b r p Hc.
elim: Hc => tH [vH oH].
elim: vH => rH [pH sH].
by [].
Qed.

(* An honest user may soft-vote only at step 2 of a period *)
(* Softvoting is enabled only at step 2 *)
Lemma softvote_only_in_step2 : forall us v b r p,
  softvote_new_ok us v b r p -> us.(step) = 2 /\
  softvote_repr_ok us v b r p -> us.(step) = 2 .
Proof using.
move => us v b r p Hc.
elim: Hc => tH [vH oH].
elim: vH => rH [pH sH].
by [].
Qed.

(* State us2 is no earlier than state us1 in terms of round-period-step ordering *)

(* A one-step user-level transition never decreases round-period-step *)
Lemma utr_rps_non_decreasing_msg : forall uid m us1 us2 ms,
  uid # us1 ; m ~> (us2, ms) -> ustate_after us1 us2.
Proof using.
move => uid m us1 us2 ms utrH.
inversion_clear utrH.
- rewrite /pre'.
  unfold ustate_after => /=.
  do 2! [right]. by do 2! [split; auto].
- case: H => tH [vH oH].
  case: vH => rH [pH sH].
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
- rewrite /pre'.
  unfold ustate_after => /=.
  do 2! [right]. by do 2! [split; auto].
- rewrite /pre'.
  unfold ustate_after => /=.
  right. left. split ; first by [].
  rewrite addn1. by [].
- rewrite /pre'.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
- case: H => vH oH.
  case: vH => rH [pH sH].
  unfold ustate_after => /=.
  right. left. split ; first by [].
  rewrite addn1. by [].
- rewrite /pre'.
  unfold ustate_after => /=.
  do 2! [right]. by do 2! [split; auto].
- unfold ustate_after => /=.
  left. unfold certify_ok in H. decompose record H;clear H.
  revert H0;unfold pre';clear.
  destruct us1;simpl. rewrite addn1 ltnS.
  unfold advancing_rp. simpl.
  by move => [|[->] _];[apply ltnW|apply leqnn].
- destruct m.1.1.1.2 eqn:E.
  destruct m.1.1.1.1 eqn:E'.
  unfold deliver_nonvote_msg_result. rewrite E. rewrite E'.  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  unfold deliver_nonvote_msg_result. rewrite E. rewrite E'.  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  unfold deliver_nonvote_msg_result. rewrite E. rewrite E'.  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  unfold deliver_nonvote_msg_result. rewrite E. rewrite E'.  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  unfold deliver_nonvote_msg_result. rewrite E. rewrite E'.  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  unfold deliver_nonvote_msg_result. rewrite E. rewrite E'.  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  unfold deliver_nonvote_msg_result. rewrite E. rewrite E'.  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  unfold deliver_nonvote_msg_result. rewrite E. unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  unfold deliver_nonvote_msg_result. rewrite E. unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  unfold deliver_nonvote_msg_result. rewrite E. unfold ustate_after => /=.
  do 2! [right]. by do 2! [split; auto].
Qed.

(* A one-step user-level transition never decreases round-period-step *)
Lemma utr_rps_non_decreasing_internal : forall uid us1 us2 ms,
  uid # us1 ~> (us2, ms) -> ustate_after us1 us2.
Proof using.
move => uid us1 us2 ms utrH.
inversion_clear utrH.
- case: H => tH [vH oH].
  case: vH => rH [pH sH].
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
- case: H => tH [vH oH].
  case: vH => rH [pH sH].
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
- case: H => tH [vH oH].
  case: vH => rH [pH sH].
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
- case: H => tH [vH oH].
  case: vH => rH [pH sH].
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
- case: H  => tH [vH oH].
  case: vH => rH [pH sH].
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
- case: H => tH [vH oH].
  case: vH => rH [pH sH].
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
- case: H => tH [vH oH].
  case: vH => rH [pH sH].
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
- case: H => tH [vH oH].
  case: vH => rH [pH sH].
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
- elim: H => tH [vH [vbH [svH oH]]].
  elim: vH => rH [pH sH].
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  rewrite addn1. by subst.
- case: H => tH [vH [vbH [svH oH]]].
  case: vH => rH [pH sH].
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  rewrite addn1. by subst.
- case: H => H v'H.
  case: H => tH [vH [vbH [svH oH]]].
  case: vH => rH [pH sH].
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  rewrite addn1. by subst.
- case: H => H [vH cH].
  case: vH => rH [pH sH].
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  rewrite addn1. by subst.
- case: H => tH [vH oH].
  case: vH => rH [pH sH].
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
Qed.

(* A one-step global transition never decreases round-period-step of any user *)
Lemma gtr_rps_non_decreasing : forall g1 g2 uid us1 us2,
  g1 ~~> g2 ->
  g1.(users).[? uid] = Some us1 -> g2.(users).[? uid] = Some us2 ->
  ustate_after us1 us2.
Proof using.
move => g1 g2 uid us1 us2.
elim => //.
- move => increment pre Htick.
  set users : GState -> _ := global_state.users _ _ _.
  move => Hu.
  case Hd: (uid \in domf (users pre)); last first.
    by move/negP/negP: Hd => Hd; move: Hu; rewrite not_fnd.
  rewrite tick_users_upd //.
  case =><-; move: Hu.
  rewrite in_fnd; case =>->.
  rewrite /user_advance_timer /= /ustate_after /=.
  by case: ifP => //=; right; right.
- set GS := global_state.GState UserId UState [choiceType of Msg].
  move => pre uid0.
  set users : GS -> _ := global_state.users _ _ _.
  move => msg_key [r m] Hpend key_ustate ustate_post sent Hloc.
  move/utr_rps_non_decreasing_msg => Hst.
  case Huid_eq: (uid == uid0).
    move/eqP: Huid_eq =>->.
    rewrite in_fnd //; case =><-.
    rewrite fnd_set /=.
    have ->: (uid0 == uid0) by apply/eqP.
    by case =><-.
  move => Hus.
  rewrite fnd_set /= Huid_eq Hus.
  by case =>->; right; right.
- set GS := global_state.GState UserId UState [choiceType of Msg].
  move => pre uid0.
  set users : GS -> _ := global_state.users _ _ _.
  move => ustate_key Hloc ustate_post sent.
  move/utr_rps_non_decreasing_internal => Hst.
  case Huid_eq: (uid == uid0).
    move/eqP: Huid_eq =>->.
    rewrite in_fnd //; case =><-; rewrite fnd_set /=.
    have ->: (uid0 == uid0) by apply/eqP.
    by case =><-.
  move => Hus.
  rewrite fnd_set /= Huid_eq Hus.
  by case =>->; right; right.
- set GS := global_state.GState UserId UState [choiceType of Msg].
  move => pre Hpre.
  set users : GS -> _ := global_state.users _ _ _.
  rewrite /= -/users => Hus1.
  by rewrite Hus1; case =>->; right; right.
- set GS := global_state.GState UserId UState [choiceType of Msg].
  move => pre Hpre.
  set users : GS -> _ := global_state.users _ _ _.
  rewrite /= -/users => Hus1.
  by rewrite Hus1; case =>->; right; right.
- set GS := global_state.GState UserId UState [choiceType of Msg].
  move => pre uid0 ustate_key.
  set users : GS -> _ := global_state.users _ _ _.
  move => Hcorrupt Hst; move: Hst Hcorrupt.
  case Huid_eq: (uid == uid0).
    move/eqP: Huid_eq =>->.
    rewrite in_fnd //.
    rewrite fnd_set /=.
    have ->: (uid0 == uid0) by apply/eqP.
    rewrite -/(users pre).
    by case =>-> => Hcorrupt; case =><-; right; right.
  rewrite fnd_set /= Huid_eq -/(users pre).
  by move =>-> => Hcorrupt; case =>->; right; right.
- set GS := global_state.GState UserId UState [choiceType of Msg].
  move => pre uid0.
  set users : GS -> _ := global_state.users _ _ _.
  move => ustate_key m Hc Hm.
  rewrite /= =>->; case =>->.
  by right; right.
- set GS := global_state.GState UserId UState [choiceType of Msg].
  move => pre sender.
  set users : GS -> _ := global_state.users _ _ _.
  move => sender_key r p s mtype mval Hhave Hcomm Hmatch.
  rewrite /= =>->; case =>->.
  by right; right.
Qed.

Lemma gtr_users_non_decreasing g1 g2 (H_step: GTransition g1 g2):
  forall uid, uid \in g1.(users) -> uid \in g2.(users).
Proof using.
  intro uid.
  repeat match goal with | [|- context C [uid \in ?f]] => change (uid \in f) with (uid \in domf f) end.
  destruct H_step;destruct pre;autounfold with gtransition_unfold;cbn;
    [rewrite -updf_domf| try (rewrite dom_setf;apply fset1Ur)..];done.
Qed.

Lemma ustate_after_transitive :
  forall us1 us2 us3,
    ustate_after us1 us2 ->
    ustate_after us2 us3 ->
    ustate_after us1 us3.
Proof using.
move => us1 us2 us3.
rewrite -!ustate_after_iff_step_le.
apply step_le_trans.
Qed.

Lemma gtrans_preserves_users: forall gs1 gs2,
  gs1 ~~> gs2 -> domf gs1.(users) = domf gs2.(users).
Proof using.
move => gs1 gs2.
elim => //.
- move => increment pre Htick.
  by rewrite -tick_users_domf.
- move => pre uid msg_key pending Hpending key_ustate ustate_post sent Hcorrupt Huser /=.
  by rewrite mem_fset1U //.
- move => pre uid ustate_key Hcorrupt ustate_post sent Huser /=.
  by rewrite mem_fset1U //.
- move => pre uid ustate_key Hcorrupt /=.
  by rewrite mem_fset1U //.
Qed.

Lemma gtrans_domf_users: forall gs1 gs2,
  gs1 ~~> gs2 -> domf gs1.(users) `<=` domf gs2.(users).
Proof using.
move => gs1 gs2.
elim => //.
- move => increment pre Htick.
  apply/fsubsetP => x Hd.
  by rewrite -tick_users_domf.
- move => pre uid msg_key pending Hpending key_ustate ustate_post sent Hcorrupt Huser /=.
  by apply/fsubsetP => x Hd; apply: fset1Ur.
- move => pre uid ustate_key Hcorrupt ustate_post sent Huser /=.
  by apply/fsubsetP => x Hd; apply: fset1Ur.
- move => pre uid ustate_key Hcorrupt /=.
  by apply/fsubsetP => x Hd; apply: fset1Ur.
Qed.

(* is_trace assumption breaks this, but this is not used anywhere *)
Lemma greachable_domf_users: forall g1 g2,
    greachable g1 g2 -> domf g1.(users) `<=` domf g2.(users).
Proof using.
  move => g1 g2 [trace H_path H_last].
  destruct trace. inversion H_path.
  destruct H_path as [H_g0 H_path]. subst g.
  revert trace g1 H_path H_last.
  elim => //=.
  - by move => _ _ <-.
  - move => a l IH g1 /andP [/asboolP H_step H_path] H_last.
    apply gtrans_domf_users in H_step.
    apply /(fsubset_trans H_step){H_step}.
    by apply IH.
Qed.

(* Generalization of non-decreasing round-period-step results to paths *)
Lemma greachable_rps_non_decreasing : forall g1 g2 uid us1 us2,
  greachable g1 g2 ->
  g1.(users).[? uid] = Some us1 -> g2.(users).[? uid] = Some us2 ->
  ustate_after us1 us2.
Proof using.
move => g1 g2 uid us1 us2.
case => gtrace Hpath Hlast.
destruct gtrace. inversion Hpath.
destruct Hpath as [H_g0 Hpath]; subst g.
set GS := global_state.GState UserId UState [choiceType of Msg].
set users : GS -> _ := global_state.users _ _ _.
elim: gtrace g1 g2 uid us1 us2 Hpath Hlast => //=.
  move => g1 g2 uid us1 us2 Htr ->->; case =>->.
  by right; right.
move => g gtrace IH.
move => g1 g2 uid us1 us2.
move/andP => [Htrans Hpath] Hlast Hg1 Hg2.
move/asboolP: Htrans => Htrans.
case Hg: (users g).[? uid] => [u|].
  have IH' := IH _ _ _ _ _ Hpath Hlast Hg Hg2.
  have Haft := gtr_rps_non_decreasing Htrans Hg1 Hg.
  move: Haft IH'.
  exact: ustate_after_transitive.
move/gtrans_domf_users: Htrans => Hdomf.
case Hd: (uid \in domf (users g1)); last first.
  by move/negP/negP: Hd => Hd; move: Hg1; rewrite not_fnd.
move/idP: Hd => Hd.
move: Hdomf.
move/fsubsetP => Hsub.
move: Hd; move/Hsub => Hdom.
move: Hg.
by rewrite in_fnd.
Qed.

(* A user has certvoted a value for a given period along a given path *)
Definition certvoted_in_path_at ix path uid r p v : Prop :=
  user_sent_at ix path uid (Certvote,val v,r,p,uid).

Definition certvoted_in_path path uid r p v : Prop :=
  exists ix, certvoted_in_path_at ix path uid r p v.

Definition certified_in_period trace r p v :=
  exists (certvote_quorum:{fset UserId}),
     certvote_quorum `<=` committee r p 3
  /\ #|` certvote_quorum | >= tau_c
  /\ forall (voter:UserId), voter \in certvote_quorum ->
       certvoted_in_path trace voter r p v.

Definition softvoted_in_path_at ix path uid r p v : Prop :=
  exists g1 g2, step_in_path_at g1 g2 ix path
   /\ user_sent uid (Softvote,val v,r,p,uid) g1 g2.

Definition softvoted_in_path path uid r p v : Prop :=
  exists ix, softvoted_in_path_at ix path uid r p v.

Definition enough_softvotes_in_period trace r p v :=
  exists (softvote_quorum:{fset UserId}),
     softvote_quorum `<=` committee r p 2
  /\ #|` softvote_quorum | >= tau_s
  /\ forall (voter:UserId), voter \in softvote_quorum ->
       softvoted_in_path trace voter r p v.

Definition nextvoted_bot_in_path_at ix path uid (r p s:nat) : Prop :=
  exists g1 g2, step_in_path_at g1 g2 ix path
   /\ user_sent uid (Nextvote_Open, step_val s,r,p,uid) g1 g2.

Definition nextvoted_bot_in_path path uid r p s : Prop :=
  exists ix, nextvoted_bot_in_path_at ix path uid r p s.

Definition enough_nextvotes_bot_in_step trace r p s :=
  exists (nextvote_quorum:{fset UserId}),
     nextvote_quorum `<=` committee r p s
  /\ #|` nextvote_quorum | >= tau_b
  /\ forall (voter:UserId), voter \in nextvote_quorum ->
       nextvoted_bot_in_path trace voter r p s.

Definition nextvoted_val_in_path_at ix path uid r p s v : Prop :=
  exists g1 g2, step_in_path_at g1 g2 ix path
   /\ user_sent uid (Nextvote_Val,next_val v s,r,p,uid) g1 g2.

Definition nextvoted_val_in_path path uid r p s v : Prop :=
  exists ix, nextvoted_val_in_path_at ix path uid r p s v.

Definition enough_nextvotes_val_in_step trace r p s v :=
  exists (nextvote_quorum:{fset UserId}),
     nextvote_quorum `<=` committee r p s
  /\ #|` nextvote_quorum | >= tau_v
  /\ forall (voter:UserId), voter \in nextvote_quorum ->
       nextvoted_val_in_path trace voter r p s v.

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

Lemma step_at_nth_pre pre post ix path:
  step_in_path_at pre post ix path ->
  forall x0, nth x0 path ix = pre.
Proof using.
  clear.
  unfold step_in_path_at.
  elim: ix path => [|n IHn] [] //= a [];tauto.
Qed.

Lemma step_at_nth_post pre post ix path:
  step_in_path_at pre post ix path ->
  forall x0, nth x0 path (ix.+1) = post.
Proof using.
  clear.
  unfold step_in_path_at.
  elim: ix path => [|n IHn] [] //= a [];tauto.
Qed.

Lemma at_greachable
      g0 states (H_path: is_trace g0 states)
      ix1 ix2 (H_le : ix1 <= ix2)
      g1 (H_g1 : onth states ix1 = Some g1)
      g2 (H_g2 : onth states ix2 = Some g2):
  greachable g1 g2.
Proof using.
  clear -H_path H_le H_g1 H_g2.
  assert (ix2 < size states) by
  (rewrite -subn_gt0 -size_drop;
   move: H_g2;clear;unfold onth;
   by destruct (drop ix2 states)).

  exists (g1 :: (drop ix1.+1 (take ix2.+1 states))).
  {
    eapply is_trace_prefix with (n:=ix2.+1) in H_path; try (by intuition).
    eapply is_trace_drop with (g0':=g1) (n:=ix1) in H_path; try eassumption.
    rewrite {1}(drop_nth g2).
    rewrite nth_take //.
    rewrite (onth_nth H_g1) //.
    rewrite size_take.
    destruct (ix2.+1 < size states); by ppsimpl; lia.
  }
  {
    simpl.
    rewrite (last_nth g1) size_drop size_takel //.
    move:(H_le). rewrite leq_eqVlt.
    move/orP => [H_eq | H_lt].
    by move/eqP in H_eq;subst;rewrite subnn;simpl;congruence.
    by rewrite subSn //= nth_drop subnKC // nth_take ?ltnS // (onth_nth H_g2).
  }
Qed.

Lemma order_ix_from_steps g0 trace (H_path: is_trace g0 trace):
  forall ix1 g1, onth trace ix1 = Some g1 ->
  forall ix2 g2, onth trace ix2 = Some g2 ->
  forall uid (key1: uid \in g1.(users)) (key2: uid \in g2.(users)),
    step_lt (step_of_ustate (g1.(users)[`key1])) (step_of_ustate (g2.(users)[`key2])) ->
    ix1 < ix2.
Proof using.
  move => ix1 g1 H_g1 ix2 g2 H_g2 uid key1 key2 H_step_lt.
  rewrite ltnNge. apply /negP => H_ix_le.

  suff: ustate_after (g2.(users)[`key2]) (g1.(users)[`key1])
    by move/ustate_after_iff_step_le /(step_lt_le_trans H_step_lt);apply step_lt_irrefl.

  have H_reach: greachable g2 g1 by eapply at_greachable;eassumption.
  exact (greachable_rps_non_decreasing H_reach (in_fnd _) (in_fnd _)).
Qed.

Lemma steps_greachable
      g0 path (H_path : is_trace g0 path)
      ix ix2 (H_lt : ix < ix2)
      pre post (H_step : step_in_path_at pre post ix path)
      pre2 post2 (H_step2 : step_in_path_at pre2 post2 ix2 path):
  greachable post pre2.
Proof using.
  apply step_in_path_onth_post in H_step.
  apply step_in_path_onth_pre in H_step2.
  eapply at_greachable;eassumption.
Qed.

Lemma order_state_from_step g0 states (H_path: is_trace g0 states) uid
  ix1 g1 (H_g1: onth states ix1 = Some g1)
      u1 (H_u1: g1.(users).[? uid] = Some u1)
  ix2 g2 (H_g2: onth states ix2 = Some g2)
      u2 (H_u2: g2.(users).[? uid] = Some u2):
  step_lt (step_of_ustate u1) (step_of_ustate u2) ->
  ix1 < ix2.
Proof using.
  move => H_step_lt.
  rewrite ltnNge. apply /negP => H_le.

  have H_greach: greachable g2 g1 by (eapply at_greachable;eassumption).
  have := greachable_rps_non_decreasing H_greach H_u2 H_u1.

  rewrite -ustate_after_iff_step_le.
  move: (step_of_ustate u1) (step_of_ustate u2) H_step_lt => [[r1 p1] s1] [[r2 p2] s2].
  clear.
  move => H_lt H_le.

  exact (step_lt_irrefl (step_lt_le_trans H_lt H_le)).
Qed.

Lemma order_sends g0 trace (H_path: is_trace g0 trace) uid
      ix1 msg1 (H_send1: user_sent_at ix1 trace uid msg1)
      ix2 msg2 (H_send2: user_sent_at ix2 trace uid msg2):
  step_le (msg_step msg1) (msg_step msg2) ->
  ix1 <= ix2.
Proof.
  move => H_step_le.
  move: H_send1 => [pre1 [post1 [H_step1 H_send1]]].
  move: H_send2 => [pre2 [post2 [H_step2 H_send2]]].

  rewrite leqNgt. apply /negP => H_lt.
  have H_reach: greachable post2 pre1.
  eapply (at_greachable H_path H_lt);eauto using step_in_path_onth_pre, step_in_path_onth_post.
  have := greachable_rps_non_decreasing H_reach
                                        (in_fnd (user_sent_in_post H_send2))
                                        (in_fnd (user_sent_in_pre H_send1)).
  move/ustate_after_iff_step_le.
  have:= utransition_label_end H_send2 (in_fnd (user_sent_in_post H_send2)).
  have -> := utransition_label_start H_send1 (in_fnd (user_sent_in_pre H_send1)).
  move => H_step_lt H_step_le1.
  have {H_step_le1}H_step_lt1 := step_lt_le_trans H_step_lt H_step_le1.
  have:= step_le_lt_trans H_step_le H_step_lt1.
  clear.
  move: (msg_step msg1) => [[r p] s].
  by apply step_lt_irrefl.
Qed.

Lemma step_ix_same trace ix g1 g2:
    step_in_path_at g1 g2 ix trace ->
    forall g3 g4,
    step_in_path_at g3 g4 ix trace ->
      g3 = g1 /\ g4 = g2.
Proof using.
  clear.
  unfold step_in_path_at.
  destruct (drop ix trace) as [|? [|]];(tauto || intuition congruence).
Qed.

(* basic lemma for propagating honest backwards *)
Lemma user_honest_from_during g0 trace (H_path: is_trace g0 trace):
  forall ix g1,
    onth trace ix = Some g1 ->
  forall uid (H_in : uid \in g1.(users)),
    honest_during_step (step_of_ustate (g1.(users)[`H_in])) uid trace ->
  user_honest uid g1.
Proof using.
  move => ix g1 H_onth uid H_in /all_nthP.
  move/(_ g1 ix (onth_size H_onth)).
  rewrite (onth_nth H_onth g1) /user_honest /upred' (in_fnd H_in).
  move/implyP;apply.
  by apply /step_leP /step_le_refl.
Qed.

(* L1: An honest user cert-votes for at most one value in a period *)
(* :: In any global state, an honest user either never certvotes in a period or certvotes once in step 3 and never certvotes after that during that period
   :: If an honest user certvotes in a period (step 3) then he will never certvote again in that period *)
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

(* A user has softvoted for one value exactly once for a given period along a given path *)
Definition softvoted_once_in_path path r p uid : Prop :=
  exists ix v, softvoted_in_path_at ix path uid r p v
  /\ forall ix' v',
     softvoted_in_path_at ix' path uid r p v' -> ix = ix' /\ v = v'.

Lemma take_rcons T : forall (s : seq T) (x : T), take (size s) (rcons s x) = s.
Proof using. elim => //=; last by move => a l IH x; rewrite IH. Qed.

(* 'user_sent uid (Softvote, val v1, r, p, uid) pre post' implies the
   round-period-step of user state at pre is exactly r, p, 2 *)
(* not really needed *)
Lemma step_of_softvote_sent uid r p: forall v pre post,
  user_sent uid (Softvote, val v, r, p, uid) pre post ->
  forall ustate, pre.(users).[? uid] = Some ustate ->
  (step_of_ustate ustate) = (r, p, 2).
Proof.
  intros v pre post H_sent ustate H_ustate.
  destruct H_sent as [ms [H_msg [[d1 [in1 H_step]]|H_step]]].
  destruct H_step as (key_ustate & ustate_post & H_step & H_honest & key_mailbox & H_msg_in_mailbox & ->).
  remember (ustate_post,ms) as ustep_out in H_step.
  destruct H_step; injection Hequstep_out; clear Hequstep_out;intros <- <-; revert H_msg; move/Iter.In_mem => H_msg; try contradiction.
  simpl in H_msg; destruct H_msg; try contradiction.
  inversion H0;subst;clear H0.
  destruct H_step as (key_user & ustate_post & H_honest & H_step & ->).
  assert (pre.(users)[` key_user] = ustate)
    by (rewrite in_fnd in H_ustate;injection H_ustate;trivial).
  unfold step_of_ustate.
  rewrite -> H in * |- *.
  inversion H_step;clear H_step;move: H;subst;move => H;
  move: H_msg => /Iter.In_mem /=;intuition;try discriminate.

  unfold softvote_new_ok in H3;decompose record H3;clear H3.
  move: H4 => [-> [-> ->]]. congruence.
  unfold softvote_repr_ok in H3;decompose record H3;clear H3.
  move: H4 => [-> [-> ->]]. congruence.
Qed.

(* Priority:HIGH
   Proof should be very similar to no_two_certvotes_in_p *)
(* L2: An honest user soft-votes for at most one value in a period *)
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


(* A user has nextvoted bottom for a given period along a given path *)
Definition nextvoted_open_in_path_at ix path uid r p s : Prop :=
  user_sent_at ix path uid (Nextvote_Open, step_val s,r,p,uid).

Definition nextvoted_open_in_path path r p s uid : Prop :=
  exists ix, nextvoted_open_in_path_at ix path uid r p s.

(* A user has nextvoted a value for a given period along a given path *)
Definition nextvoted_value_in_path path r p s uid v : Prop :=
  exists ix, user_sent_at ix path uid (Nextvote_Val, next_val v s, r, p, uid).


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

(* Several lemmas here showing that some of the
   sets in the UState may only increase over time,
   or within a round *)
Lemma softvotes_utransition_internal:
  forall uid pre post msgs, uid # pre ~> (post, msgs) ->
  forall r p, pre.(softvotes) r p \subset post.(softvotes) r p.
Proof using.
  move => uid pre post msgs step r p.
  remember (post,msgs) as result eqn:H_result;
  destruct step;case:H_result => [? ?];subst;done.
Qed.

Lemma softvotes_utransition_deliver:
  forall uid pre post m msgs, uid # pre ; m ~> (post, msgs) ->
  forall r p,
    pre.(softvotes) r p \subset post.(softvotes) r p.
Proof using.
  move => uid pre post m msgs step r p;
  remember (post,msgs) as result eqn:H_result;
    destruct step;case:H_result => [? ?];subst;
  destruct pre;simpl;autounfold with utransition_unfold;
    repeat match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b end;
  try (by apply subxx_hint);
  by apply/subsetP => x H_x;rewrite ?in_cons mem_undup H_x ?orbT.
Qed.

Lemma softvotes_gtransition g1 g2 (H_step:g1 ~~> g2) uid:
  forall u1, g1.(users).[?uid] = Some u1 ->
  exists u2, g2.(users).[?uid] = Some u2
             /\ forall r p, u1.(softvotes) r p \subset u2.(softvotes)  r p.
Proof using.
  clear -H_step => u1 H_u1.
  have H_in1: (uid \in g1.(users)) by rewrite -fndSome H_u1.
  have H_in1': g1.(users)[`H_in1] = u1 by rewrite in_fnd in H_u1;case:H_u1.
  destruct H_step;simpl users;autounfold with gtransition_unfold;
    try (rewrite fnd_set;case H_eq:(uid == uid0);
      [move/eqP in H_eq;subst uid0|]);
    try (eexists;split;[eassumption|done]);
    first rewrite updf_update //;
    (eexists;split;[reflexivity|]).
  * (* tick *)
    rewrite H_in1' /user_advance_timer.
    by match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b end.
  * (* deliver *)
    move:H1. rewrite ?(eq_getf _ H_in1) H_in1'. apply softvotes_utransition_deliver.
  * (* internal *)
    move:H0. rewrite ?(eq_getf _ H_in1) H_in1'. apply softvotes_utransition_internal.
  * (* corrupt *)
    rewrite ?(eq_getf _ H_in1) H_in1'. done.
Qed.

Lemma softvotes_monotone g1 g2 (H_reach:greachable g1 g2) uid:
  forall u1, g1.(users).[?uid] = Some u1 ->
  forall u2, g2.(users).[?uid] = Some u2 ->
  forall r p,
    u1.(softvotes) r p \subset u2.(softvotes)  r p.
Proof using.
  clear -H_reach.
  move => u1 H_u1 u2 H_u2.
  destruct H_reach as [trace H_path H_last].
  destruct trace. inversion H_path.
  destruct H_path as [H_g0 H_path]. subst g.
  move: g1 H_path H_last u1 H_u1.
  induction trace.
  * simpl. by move => g1 _ <- u1;rewrite H_u2{H_u2};case => ->.
  * cbn [path last] => g1 /andP [/asboolP H_step H_path] H_last u1 H_u1 r p.
    specialize (IHtrace a H_path H_last).
    have [umid [H_umid H_sub]] := softvotes_gtransition H_step H_u1.
    specialize (H_sub r p).
    specialize (IHtrace umid H_umid r p).
    refine (subset_trans H_sub IHtrace).
Qed.

Lemma soft_weight_monotone g1 g2 (H_reach:greachable g1 g2) uid:
  forall u1, g1.(users).[?uid] = Some u1 ->
  forall u2, g2.(users).[?uid] = Some u2 ->
  forall v r p,
    soft_weight v u1 r p <= soft_weight v u2 r p.
Proof using.
  move => u1 H_u1 u2 H_u2 v r p.
  have H_mono := softvotes_monotone H_reach H_u1 H_u2 r p.
  apply fsubset_leq_card.
  unfold softvoters_for.
  move: (u1.(softvotes)) (u2.(softvotes)) H_mono;clear => s1 s2 /subsetP H_mono.
  apply subset_imfset.
  simpl.
  move => x /andP [H_x_s1 H_val].
  by apply/andP;split;[apply/H_mono|].
Qed.

Lemma blocks_utransition_internal:
  forall uid pre post msgs, uid # pre ~> (post, msgs) ->
  forall r, pre.(blocks) r \subset post.(blocks) r.
Proof using.
  move => uid pre post msgs step r.
  remember (post,msgs) as result eqn:H_result;
  destruct step;case:H_result => [? ?];subst;done.
Qed.

Lemma blocks_utransition_deliver:
  forall uid pre post m msgs, uid # pre ; m ~> (post, msgs) ->
  forall r,
    pre.(blocks) r \subset post.(blocks) r.
Proof using.
  move => uid pre post m msgs step r;
  remember (post,msgs) as result eqn:H_result;
    destruct step;case:H_result => [? ?];subst;
  destruct pre;simpl;autounfold with utransition_unfold;
    repeat match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b
           | _ => progress simpl end;
  try (by apply subxx_hint);
  by apply/subsetP => x H_x;rewrite ?in_cons mem_undup H_x ?orbT.
Qed.

Lemma blocks_gtransition g1 g2 (H_step:g1 ~~> g2) uid:
  forall u1, g1.(users).[?uid] = Some u1 ->
  exists u2, g2.(users).[?uid] = Some u2
             /\ forall r, u1.(blocks) r \subset u2.(blocks) r.
Proof using.
  clear -H_step => u1 H_u1.
  have H_in1: (uid \in g1.(users)) by rewrite -fndSome H_u1.
  have H_in1': g1.(users)[`H_in1] = u1 by rewrite in_fnd in H_u1;case:H_u1.
  destruct H_step;simpl users;autounfold with gtransition_unfold;
    try (rewrite fnd_set;case H_eq:(uid == uid0);
      [move/eqP in H_eq;subst uid0|]);
    try (eexists;split;[eassumption|done]);
    first rewrite updf_update //;
    (eexists;split;[reflexivity|]).
  * (* tick *)
    rewrite H_in1' /user_advance_timer.
    by match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b end.
  * (* deliver *)
    move:H1. rewrite ?(eq_getf _ H_in1) H_in1'. apply blocks_utransition_deliver.
  * (* internal *)
    move:H0. rewrite ?(eq_getf _ H_in1) H_in1'. apply blocks_utransition_internal.
  * (* corrupt *)
    rewrite ?(eq_getf _ H_in1) H_in1'. done.
Qed.

Lemma blocks_monotone g1 g2 (H_reach: greachable g1 g2) uid:
  forall u1, g1.(users).[? uid] = Some u1 ->
  forall u2, g2.(users).[? uid] = Some u2 ->
  forall r, u1.(blocks) r \subset u2.(blocks) r.
Proof using.
  clear -H_reach.
  move => u1 H_u1 u2 H_u2.
  destruct H_reach as [trace H_path H_last].
  destruct trace. inversion H_path.
  destruct H_path as [H_g0 H_path]. subst g.
  move: g1 H_path H_last u1 H_u1.
  induction trace.
  * simpl. by move => g1 _ <- u1;rewrite H_u2{H_u2};case => ->.
  * cbn [path last] => g1 /andP [/asboolP H_step H_path] H_last u1 H_u1 r.
    specialize (IHtrace a H_path H_last).
    have [umid [H_umid H_sub]] := blocks_gtransition H_step H_u1.
    specialize (H_sub r).
    specialize (IHtrace umid H_umid r).
    refine (subset_trans H_sub IHtrace).
Qed.

(* L3: If an honest user cert-votes for a value in step 3, the user will NOT next-vote bottom in the same period
*)
Lemma certvote_excludes_nextvote_open_in_p g0 trace (H_path: is_trace g0 trace) uid r p s v:
  honest_during_step (r,p,s) uid trace ->
  certvoted_in_path trace uid r p v -> ~ nextvoted_open_in_path trace r p s uid .
Proof using.
  clear -H_path.
  move => H_honest [ix_cv H_cv] [ix_nv H_nv].
  move: (H_cv) => [g1_cv [g2_cv [H_step_cv H_vote_cv]]].
  move: (H_nv) => [g1_nv [g2_nv [H_step_nv H_vote_nv]]].

  have H_key1_nv := user_sent_in_pre H_vote_nv.
  set ustate_nv : UState := g1_nv.(users)[`H_key1_nv].
  have H_lookup_nv : _ = Some ustate_nv := in_fnd H_key1_nv.
  have H_nv_precond := nextvote_open_precondition H_vote_nv H_lookup_nv.

  have H_key2_cv := user_sent_in_post H_vote_cv.
  set ustate_cv : UState := g2_cv.(users)[`H_key2_cv].
  have H_lookup_cv : _ = Some ustate_cv := in_fnd H_key2_cv.
  have H_softvotes := certvote_postcondition H_vote_cv H_lookup_cv.

  assert (ix_cv < ix_nv) as H_lt.
  {
  apply (order_ix_from_steps H_path (step_in_path_onth_pre H_step_cv) (step_in_path_onth_pre H_step_nv)
                             (key1:=user_sent_in_pre H_vote_cv) (key2:=user_sent_in_pre H_vote_nv)).
  rewrite (utransition_label_start H_vote_cv);[|by apply in_fnd].
  rewrite (utransition_label_start H_vote_nv);[|by apply in_fnd].
  move:H_nv_precond;clear;simpl;unfold nextvote_open_ok;tauto.
  }

  have H_reach: greachable g2_cv g1_nv := steps_greachable H_path H_lt H_step_cv H_step_nv.

  move: H_nv_precond. unfold nextvote_open_ok.
  move => [] _ [] _ [] _ [] _ [] H_no_softvotes _.

  clear -H_reach H_softvotes H_lookup_cv H_lookup_nv H_no_softvotes.
  specialize (H_no_softvotes v).
  have: v \in certvals ustate_nv r p.
  {
    move: H_softvotes => [H] _. move: H.
    rewrite !mem_filter.
    move/andP => [H_tau H_votes]. apply/andP.
    split.
      by apply/(leq_trans H_tau) /(soft_weight_monotone H_reach H_lookup_cv H_lookup_nv).
      have H_subset := softvotes_monotone H_reach H_lookup_cv H_lookup_nv r p.
      move: H_subset H_votes.
      unfold vote_values.
      destruct ustate_cv, ustate_nv;simpl; clear.
      move => H_subset.
      rewrite !mem_undup.
      move/mapP => [x H_in H_v].
      apply/mapP. exists x;[|assumption].
      move: {H_v}x H_in.
      apply/subsetP.
      by assumption.
  }
  move => H_certval_nv.
  move: H_softvotes =>  [_ [[b [H_b H_valid]] _]].

  refine (H_no_softvotes H_certval_nv b _ H_valid).
  apply/subsetP: {H_valid}b H_b.
  by apply (blocks_monotone H_reach H_lookup_cv H_lookup_nv).
Qed.

Lemma users_not_added g1 g2 (H_step:g1 ~~> g2) uid:
  g1.(users).[?uid] = None ->
  g2.(users).[?uid] = None.
Proof using.
  clear -H_step => H_u1.
  have H_notin1: (uid \notin g1.(users)) by rewrite -fndSome H_u1.
  destruct H_step;simpl users;
    try assumption;
    try (by rewrite fnd_set; case H_eq:(uid == uid0);
         [move/eqP in H_eq; subst; rewrite key_ustate in H_notin1; inversion H_notin1|]);
    try (by rewrite fnd_set; case H_eq:(uid == uid0);
         [move/eqP in H_eq; subst; rewrite ustate_key in H_notin1; inversion H_notin1|]).
  (* tick *)
  apply tick_users_notin; assumption.
Qed.

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
    eapply users_not_added in H_u1; try eassumption.
    rewrite H_u1 in H_u2; inversion H_u2.
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

(* Priority:HIGH
   Top-level result,
   much of proof shared with certvote_excludes_nextvote_open_in_p
 *)
(* L3’: If an honest user cert-votes for a value in step 3, the user can only next-vote that value in the same period *)
Lemma certvote_nextvote_value_in_p
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start : state_before_round r0 g0) uid r p s v v':
  honest_during_step (r,p,s) uid trace ->
  r0 <= r ->
  certvoted_in_path trace uid r p v ->
  nextvoted_value_in_path trace r p s uid v' ->
  v = v'.
Proof.
  clear -H_path H_start.
  move => H_honest H_r [ix_cv H_cv] [ix_nv H_nv].
  move: (H_cv) => [g1_cv [g2_cv [H_step_cv H_vote_cv]]].
  move: (H_nv) => [g1_nv [g2_nv [H_step_nv H_vote_nv]]].

  have H_g1_nv := step_in_path_onth_pre H_step_nv.
  have H_key1_nv := user_sent_in_pre H_vote_nv.
  set ustate_nv : UState := g1_nv.(users)[`H_key1_nv].
  have H_lookup_nv : _ = Some ustate_nv := in_fnd H_key1_nv.
  have H_nv_precond := nextvote_val_precondition H_vote_nv H_lookup_nv.

  have H_g2_cv := step_in_path_onth_post H_step_cv.
  have H_key2_cv := user_sent_in_post H_vote_cv.
  set ustate_cv : UState := g2_cv.(users)[`H_key2_cv].
  have H_lookup_cv : _ = Some ustate_cv := in_fnd H_key2_cv.
  have H_cv_cond := certvote_postcondition H_vote_cv H_lookup_cv.

  assert (ix_cv < ix_nv).
  {
  apply (order_ix_from_steps H_path (step_in_path_onth_pre H_step_cv) H_g1_nv
                             (key1:=user_sent_in_pre H_vote_cv) (key2:=user_sent_in_pre H_vote_nv)).
  rewrite (utransition_label_start H_vote_cv);[|by apply in_fnd].
  rewrite (utransition_label_start H_vote_nv);[|by apply in_fnd].

  destruct H_nv_precond as [H_nv_precond | H_nv_precond].
  move:H_nv_precond =>[b];clear;simpl;unfold nextvote_val_ok;tauto.
  (* stv case of nextvote_val_precondition *)
  right;split;[reflexivity|];right;split;[reflexivity|].
  case: H_nv_precond.
  clear.
  unfold nextvote_stv_ok.
  tauto.
  }

  have H_reach : greachable g2_cv g1_nv
    := steps_greachable H_path H H_step_cv H_step_nv.

  destruct H_cv_cond as [H_certval_cv [[b' [H_blocks H_valid]] _]].

  assert (v \in certvals ustate_nv r p) as H_certval_v.
  {
    move: H_certval_cv.
    have H_weight_le := soft_weight_monotone H_reach H_lookup_cv H_lookup_nv v r p.
    have H_softvotes_le := softvotes_monotone H_reach H_lookup_cv H_lookup_nv r p.
    clear -H_weight_le H_softvotes_le.
    rewrite /certvals !mem_filter => /andP [H_weight H_votes].
    apply/andP. split. by apply (leq_trans H_weight).
    move:H_votes. rewrite /vote_values !mem_undup. move/mapP => [] x H_x ->.
    apply map_f. move: H_x.
    by apply/subsetP.
  }

  assert (tau_s <= soft_weight v ustate_nv r p) as H_v
      by (move:H_certval_v;rewrite mem_filter => /andP [] //).

  destruct H_nv_precond as [H_nv_precond_val | H_nv_precond_stv].

  * (* from nextvote val *)
  {
  have {H_nv_precond_val}H_certval_v' : v' \in certvals ustate_nv r p
    by move: H_nv_precond_val => [] b;unfold nextvote_val_ok;tauto.

  assert (tau_s <= soft_weight v' ustate_nv r p) as H_v'
      by (move: H_certval_v';rewrite mem_filter => /andP [] //).


  have H_votes_checked :=
    softvote_credentials_checked H_path H_start H_g1_nv H_lookup_nv H_r.

  have Hq := quorums_s_honest_overlap trace.
  specialize (Hq r p 2 _ _ (H_votes_checked _ _) H_v (H_votes_checked _ _) H_v').

  move: Hq => [softvoter [H_voted_v [H_voted_v' H_softvoter_honest]]].
  assert (softvoted_in_path trace softvoter r p v) as H_sent_v. {
  apply (softvotes_sent H_path H_start H_g1_nv H_lookup_nv H_r).
  move:H_voted_v => /imfsetP /= [] x /andP [H_x_in].
  unfold matchValue. destruct x. move => /eqP ? /= ?;subst.
  assumption.
  assumption.
  }
  assert (softvoted_in_path trace softvoter r p v') as H_sent_v'. {
  apply (softvotes_sent H_path H_start H_g1_nv H_lookup_nv H_r).
  move:H_voted_v' => /imfsetP /= [] x /andP [H_x_in].
  unfold matchValue. destruct x. move => /eqP ? /= ?;subst.
  assumption.
  assumption.
  }
  move: H_sent_v => [ix_v H_sent_v].
  move: H_sent_v' => [ix_v' H_sent_v'].

  by case:(no_two_softvotes_in_p H_path H_sent_v H_sent_v').
  }

  * {
  exfalso.
  (* stv case of nextvote_val_precondition *)
  destruct H_nv_precond_stv as [H_nv_stv _].
  destruct H_nv_stv as [H_time [H_rps [H_ccs [H_nv_step [H_not_valid [H_p H_no_quorum]]]]]].

  apply (H_not_valid _ H_certval_v b');[|assumption].
  by move: (blocks_monotone H_reach H_lookup_cv H_lookup_nv r) (b') H_blocks => /subsetP.
  }
Qed.

Definition period_advances uid r p (users1 users2: {fmap UserId -> UState}) : Prop :=
  {ukey_1: uid \in users1 &
  {ukey_2: uid \in users2 &
  let ustate1 := users1.[ukey_1] in
  let ustate2 := users2.[ukey_2] in
  ustate1.(round) = ustate2.(round)
  /\ step_lt (step_of_ustate ustate1) (r,p,0)
  /\ step_of_ustate ustate2 = (r,p,1)}}.

(* L5.0 A node enters period p > 0 only if it received t_H next-votes for
   the same value from some step s of period p-1 *)
Definition period_advance_at n path uid r p g1 g2 : Prop :=
  step_in_path_at g1 g2 n path /\ period_advances uid r p (g1.(users)) (g2.(users)).

Lemma set_nil : forall (T : finType), [set x in [::]] = @set0 T.
Proof. by move => T. Qed.

Lemma finseq_size : forall (T : finType) (s: seq T), #|s| = size (undup s).
Proof.
move=> T s.
rewrite -cardsE.
elim: s => //=; first by rewrite set_nil cards0.
move => x s IH.
rewrite set_cons /=.
case: ifP => //=.
  move => xs.
  suff Hsuff: x |: [set x0 in s] = [set x in s] by rewrite Hsuff.
  apply/setP => y.
  rewrite in_setU1.
  case Hxy: (y == x) => //.
  rewrite /= inE.
  by move/eqP: Hxy=>->.
move/negP/negP => Hx.
by rewrite cardsU1 /= inE Hx /= add1n IH.
Qed.


Lemma imfset_filter_size_lem (A B : choiceType) (f : A -> B) (sq : seq A) (P : A -> bool):
  #|` [fset x | x in [seq f x | x <- sq & P x]]| = #|` [fset f x | x in sq & P x]|.
Proof.
  clear -f sq P.
  rewrite Imfset.imfsetE !size_seq_fset.
  apply perm_eq_size, uniq_perm_eq;[apply undup_uniq..|].

  intro fx. rewrite !mem_undup map_id /= filter_undup mem_undup.
  apply Bool.eq_true_iff_eq;rewrite -!/(is_true _).
  by split;move/mapP => [x H_x ->];apply map_f;move:H_x;rewrite mem_undup.
Qed.

(* some collection of votes recorded in nv_open/val field *)
(* where certs check out and tau_b many of them *)
(* statement uses received_next_vote pred *)
(* only end up with vote recorded in your set if you actually receive it/it is sent *)
(* stop at in a nextvote collection *)

(* Priority:MED
   Structural lemma about advancement
 *)
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

(* L5.1 Any set of tau_b committee  members must include at least one honest node,
        defined earlier as quorum_b_has_honest *)
Definition honest_in_period (r p:nat) uid path :=
  exists n,
    match @onth GState path n with
    | None => False
    | Some gstate =>
      match gstate.(users).[? uid] with
      | None => False
      | Some ustate =>
        ~ustate.(corrupt) /\ ustate.(round) = r /\ ustate.(period) = p
      end
    end.

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


(* L5 An honest node can enter period p'>1 only if at least one
      honest node participated in period p'-1 *)
(* Note that we freeze the state of corrupt users,
   so any user whose period actually advanced must have been
   honest at the time *)
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

Definition users_at ix path : {fmap UserId -> UState} :=
  match drop ix path with
  | g1 :: _ => g1.(users)
  | _ => [fmap]
  end.

Definition user_stv_val (uid:UserId) (g:GState) (p:nat) (stv':option Value) : bool :=
  if g.(users).[? uid] is Some ustate then ustate.(stv) p == stv' else false.

Definition user_stv_val_at ix path uid p stv : bool :=
  match drop ix path with
  | g1 :: _ => user_stv_val uid g1 p stv
  | _ => false
  end.

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

Lemma period_nextvoted_exclusively_from_nextvotes
      g0 trace (H_path: is_trace g0 trace)
      r (H_start: state_before_round r g0)
      p (H_p_gt: 1 < p)
      v
  (H_nextvote_val : forall (uid : UserId) (s : nat) (v' : Value),
                            nextvoted_val_in_path trace uid r p s v' -> v' = v)
  (H_no_nextvotes_open : forall (uid : UserId) (s : nat),
                        honest_during_step (r, p, s) uid trace ->
                        ~ nextvoted_open_in_path trace r p s uid):
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

(* D1: an honest node enters a period exclusively for value v *)
(* if it enters the period with starting value $v$ *)
 (* and has not observed t_H next-votes for $\bot$ from any single step of the previous period *)
(*
Definition enters_exclusively_for_value (uid : UserId) (r p : nat) (v : Value) path :=
  exists g1 g2 n, period_advance_at n path uid r p g1 g2 /\
  exists ustate, g2.(users).[? uid] = Some ustate /\
  ~ ustate.(corrupt) /\ ustate.(stv) p = Some v /\
  forall s, ~nextvote_bottom_quorum ustate r p.-1 s.
 *)

Lemma stv_utransition_internal:
  forall uid pre post msgs, uid # pre ~> (post, msgs) ->
  pre.(round) = post.(round) ->
  pre.(period) = post.(period) ->
  forall p, pre.(stv) p = post.(stv) p.
Proof using.
  move => uid pre post msgs step.
  remember (post,msgs) as result eqn:H_result;
  destruct step;case:H_result => [? ?];subst;done.
Qed.

Lemma stv_utransition_deliver:
  forall uid pre post m msgs, uid # pre ; m ~> (post, msgs) ->
  pre.(round) = post.(round) ->
  pre.(period) = post.(period) ->
  forall p, pre.(stv) p = post.(stv) p.
Proof using.
  move => uid pre post m msgs step H_round H_period.
  remember (post,msgs) as result eqn:H_result;
  destruct step;case:H_result => [? ?];subst;
    try by (destruct pre;simpl;autounfold with utransition_unfold;done).
  * {
      exfalso;move: H_period;clear;destruct pre;simpl;clear.
      rewrite -[period in period = _]addn0. move/addnI. done.
    }
  * {
      exfalso;move: H_period;clear;destruct pre;simpl;clear.
      rewrite -[period in period = _]addn0. move/addnI. done.
    }
  * { exfalso;unfold certify_ok in H;decompose record H;clear H.
      move:H0. rewrite /advancing_rp H_round;clear;simpl.
      by case =>[|[]];[rewrite ltnNge leq_addr
                      |rewrite -[r in _ = r]addn0;move/addnI].
    }
  * { clear.
      unfold deliver_nonvote_msg_result.
      destruct msg as [[[[]]]]. simpl.
      by destruct e;[destruct m|..].
    }
Qed.

Lemma stv_gtransition g1 g2 (H_step:g1 ~~> g2) uid:
  forall u1, g1.(users).[?uid] = Some u1 ->
  exists u2, g2.(users).[?uid] = Some u2
  /\  (u1.(round)  = u2.(round)  ->
       u1.(period) = u2.(period) ->
       forall p, u1.(stv) p = u2.(stv) p).
Proof using.
  clear -H_step => u1 H_u1.
  have H_in1: (uid \in g1.(users)) by rewrite -fndSome H_u1.
  have H_in1': g1.(users)[`H_in1] = u1 by rewrite in_fnd in H_u1;case:H_u1.
  destruct H_step;simpl users;autounfold with gtransition_unfold;
    try (rewrite fnd_set;case H_eq:(uid == uid0);
      [move/eqP in H_eq;subst uid0|]);
    try (eexists;split;[eassumption|done]);
    first rewrite updf_update //;
    (eexists;split;[reflexivity|]).
  * (* tick *)
    rewrite H_in1' /user_advance_timer.
    by match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b end.
  * (* deliver *)
    move:H1. rewrite ?(eq_getf _ H_in1) H_in1'. apply stv_utransition_deliver.
  * (* internal *)
    move:H0. rewrite ?(eq_getf _ H_in1) H_in1'. apply stv_utransition_internal.
  * (* corrupt *)
    rewrite ?(eq_getf _ H_in1) H_in1'. done.
Qed.

Lemma stv_forward
      g1 g2 (H_reach : greachable g1 g2)
      uid u1 u2:
  g1.(users).[?uid] = Some u1 ->
  g2.(users).[?uid] = Some u2 ->
  u1.(round) = u2.(round) ->
  u1.(period) = u2.(period) ->
  forall p, u1.(stv) p = u2.(stv) p.
Proof using.
  clear -H_reach.
  move => H_u1 H_u2 H_r H_p.
  destruct H_reach as [trace H_path H_last].

  destruct trace. inversion H_path.
  destruct H_path as [H_g0 H_path]. subst g.

  move: g1 H_path H_last u1 H_u1 H_r H_p.
  induction trace.
  * simpl. by move => g1 _ <- u1;rewrite H_u2{H_u2};case => ->.
  * cbn [path last] => g1 /andP [/asboolP H_step H_path] H_last u1 H_u1 H_r H_p p.

    assert (H_reach : greachable a g2).
      by eapply ex_intro2 with (a::trace); unfold is_trace.

    specialize (IHtrace a H_path H_last).
    have [umid [H_umid H_sub]] := stv_gtransition H_step H_u1.
    specialize (IHtrace umid H_umid).
    have H_le_u1_umid := gtr_rps_non_decreasing H_step H_u1 H_umid.
    have H_le_umid_u2 := greachable_rps_non_decreasing H_reach H_umid H_u2.
    have H_r': u1.(round) = umid.(round). {
      move: H_r H_p H_le_u1_umid H_le_umid_u2.
      unfold ustate_after. destruct u1,umid,u2;simpl;clear;intros;subst.
      intuition. have := ltn_trans H H0. by rewrite ltnn.
    }
    have H_p': u1.(period) = umid.(period). {
      move: H_r H_p H_le_u1_umid H_le_umid_u2.
      unfold ustate_after. destruct u1,umid,u2;simpl;clear;intros;subst.
      intuition. have := ltn_trans H H0. by rewrite ltnn.
      subst. by rewrite ltnn in H.
      subst. by rewrite ltnn in H0.
      have := ltn_trans H2 H3. by rewrite ltnn.
    }
    specialize (H_sub H_r' H_p').
    rewrite H_sub. clear H_sub.
    apply IHtrace;congruence.
Qed.

Definition round_advance_at n path uid r g1 g2 : Prop :=
  step_in_path_at g1 g2 n path /\
  {ukey_1: uid \in g1.(users) &
  {ukey_2: uid \in g2.(users) &
  let ustate1 := g1.(users).[ukey_1] in
  let ustate2 := g2.(users).[ukey_2] in
  step_lt (step_of_ustate ustate1) (r,1,1)
  /\ step_of_ustate ustate2 = (r,1,1)}}.

Lemma honest_softvote_respects_excl_stv:
  forall p, 1 < p ->
  forall u r,
    (forall s, ~nextvote_bottom_quorum u r p.-1 s) ->
  forall g1 uid,
    g1.(users).[?uid] = Some u ->
  forall v,
    u.(stv) p = Some v ->
  forall v' g2,
    user_sent uid (Softvote, val v', r, p, uid) g1 g2 ->
  v' = v.
Proof.
  move => p H_p u r H_excl g1 uid H_u v H_stv v' g2 H_sent.
  move: H_sent => [ms [H_msg [[d [pending H_deliver]]|H_internal]]].
  *
    move: H_deliver => [key1 [upost]] /=.
    have H_u_key: (g1.(users))[`key1] = u by rewrite in_fnd in H_u;case:H_u.
    rewrite !H_u_key.
    move => [H_step [H_honest _]].
    contradict H_msg => /Iter.In_mem.
    move: H_step;clear.
    by inversion 1;simpl;intuition.
  *
    move: H_internal => [key1 [upost]] /=.
    have H_u_key: (g1.(users))[`key1] = u by rewrite in_fnd in H_u;case:H_u.
    rewrite !H_u_key.
    move => [H_honest [H_step {g2}_]].

    inversion H_step;subst pre uid0 upost ms;clear H_step;try done;
      move:H_msg;rewrite mem_seq1 => /eqP [Hv Hr Hp];subst v0 r0 p0.
    +
    unfold softvote_new_ok in H2;decompose record H2;clear H2.
    contradict H3.
    unfold cert_may_exist.
    move:H1 => [H_r [H_u_p H_s]].
    by rewrite H_u_p H_r subn1.

    +
    unfold softvote_repr_ok in H2;decompose record H2;clear H2.
    move: H5 => [[H_cert H_asdfd1]|[H_cert H_stv0]].
     - contradict H_cert;unfold cert_may_exist.
         by move:H1 => [H_r [H_u_p H_s]];rewrite H_r H_u_p subn1;split.
     - by move:H_stv;rewrite H_stv0;clear;case.
Qed.

Lemma user_sent_honest_pre uid msg g1 g2
      (H_send: user_sent uid msg g1 g2):
      (g1.(users)[` user_sent_in_pre H_send]).(corrupt) = false.
Proof.
  set H_in := user_sent_in_pre H_send.
  clearbody H_in.
  move:H_send => [ms [H_in_ms [[d [inc H_ustep]]|H_ustep]]];
      simpl in H_ustep;decompose record H_ustep;clear H_ustep.
  apply/negP;contradict H0;move: H0.
    by rewrite (bool_irrelevance H_in x).
  apply/negP;contradict H;move: H.
    by rewrite (bool_irrelevance H_in x).
Qed.

Lemma user_sent_honest_post uid msg g1 g2
      (H_send: user_sent uid msg g1 g2):
      (g2.(users)[` user_sent_in_post H_send]).(corrupt) = false.
Proof.
  set H_in := user_sent_in_post H_send.
  clearbody H_in.
  suff: user_honest uid g2 by rewrite /user_honest in_fnd => /negbTE.
  move:H_send => [ms [H_in_ms [[d [inc H_ustep]]|H_ustep]]];
      simpl in H_ustep;decompose record H_ustep;clear H_ustep;subst g2.
  - unfold user_honest, delivery_result;simpl.
    rewrite fnd_set eq_refl.
    move: H H0. clear.
    move/utransition_msg_preserves_corrupt =>->.
    move => Hcorrupt.
    by apply/negP.
- unfold user_honest, step_result;simpl.
  rewrite fnd_set eq_refl.
  move: H0 H. clear.
  move/utransition_internal_preserves_corrupt =>->.
  move => Hcorrupt.
  by apply/negP.
Qed.

Lemma user_honest_in_from_send ix trace uid msg
   (H_vote: user_sent_at ix trace uid msg):
   let: (r,p,_) := msg_step msg in
   honest_in_period r p uid trace.
Proof.
  (* move => g0 trace H_path r p v H_p H_excl uid v' H_honest H_vote. *)
  destruct H_vote as (g1_v & g2_v & H_vote_step & H_vote_send).

  set H_in: uid \in g1_v.(users) := user_sent_in_pre H_vote_send.
  have H_u := in_fnd H_in.
  set u: UState := (g1_v.(users)[` H_in]) in H_u.

  have:= utransition_label_start H_vote_send H_u.
  move: (msg_step msg) => [[r p] s] [H_r H_p _].

  by exists ix;rewrite (step_in_path_onth_pre H_vote_step) H_u (user_sent_honest_pre H_vote_send).
Qed.

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
    apply (order_state_from_step H_path
               (step_in_path_onth_pre H_step_enter) (in_fnd ukey_ge1)
               (step_in_path_onth_pre H_step) (in_fnd ukey_gs1)).
  }

  exact
     (at_greachable H_path (ix1:=ix_e.+1) (ix2:=ix_s) H_order
                       (step_in_path_onth_post H_step_enter)
                       (step_in_path_onth_pre H_step)).
Qed.

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

(* L6: if all honest nodes that entered a period p >= 2 did so exclusively for value v *)
(* then an honest node cannot cert-vote for any value other than v in step 3 of period p'. *)
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

Lemma onth_last_take: forall T (s:seq T) n x,
    onth s n = Some x ->
    forall x0,
    last x0 (take n.+1 s) = x.
Proof using.
  clear.
  move => T s n x H_nth x0.
  have H_size := onth_size H_nth.
  move: H_nth.
  unfold onth, ohead.

  have ?: n < n.+1 by rewrite ltnS.
  rewrite -nth_last size_takel //= nth_take // (drop_nth x0) //.
  by case.
Qed.

Definition eqGState (g1 g2 : GState) : bool :=
  if pselect (g1 = g2) then true else false.

Lemma eqGStateP : Equality.axiom eqGState.
Proof.
by move => g1 g2; rewrite /eqGState; case: pselect => //= ?; apply/(iffP idP).
Qed.

Canonical GState_eqMixin := EqMixin eqGStateP.
Canonical GState_eqType := Eval hnf in EqType GState GState_eqMixin.

Lemma onth_index (T : eqType) (x : T) (s : seq T): x \in s -> onth s (index x s) = Some x.
Proof using.
  move => H_in.
    by rewrite /onth /ohead (drop_nth x);[rewrite nth_index|rewrite index_mem].
Qed.

Lemma honest_during_from_ustate trace g0 (H_path : is_trace g0 trace):
  forall ix g,
    onth trace ix = Some g ->
  forall uid u,
    g.(users).[? uid] = Some u ->
    ~~ u.(corrupt) ->
  forall r p s,
    step_lt (r,p,s) (step_of_ustate u) ->
    honest_during_step (r,p,s) uid trace.
Proof using.
  move => ix g H_g uid u H_u H_honest r p s H_lt.
  have H_g_honest: user_honest uid g by rewrite /user_honest H_u.
  apply/allP => x H_in_x.
  unfold upred'.
  case:fndP => // key_x.
  apply/implyP => /step_leP /step_le_lt_trans /(_ H_lt) H_x_lt.
  suff: user_honest uid x by rewrite /user_honest (in_fnd key_x).
  apply/honest_monotone:H_g_honest.
  have H_x := onth_index H_in_x.
  refine (at_greachable H_path (ltnW _) H_x H_g).
  exact (order_state_from_step H_path H_x (in_fnd key_x) H_g H_u H_x_lt).
Qed.

Lemma honest_at_from_during r p s uid trace:
      honest_during_step (r,p,s) uid trace ->
      forall g0 (H_path: is_trace g0 trace),
      forall n g, onth trace n = Some g ->
      forall u, g.(users).[? uid] = Some u ->
      step_le (step_of_ustate u) (r,p,s) ->
      user_honest_at n trace uid.
Proof using.
  clear.
  move => H_honest g0 H_path n g H_onth u H_u H_le.
  apply (onth_at_step H_onth).
  move: H_honest => /all_nthP - /(_ g n (onth_size H_onth)).
  rewrite (onth_nth H_onth) /upred' /user_honest H_u => /implyP.
  by apply;apply /step_leP.
Qed.

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

Definition saw_v trace r p v := fun uid =>
  has (fun g =>
         match g.(users).[? uid] with
         | None => false
         | Some u =>
           (v \in u.(certvals) r p)
             && has (fun b => `[< valid_block_and_hash b v>]) (u.(blocks) r)
             && step_leb (step_of_ustate u) (r,p,4)
         end) trace.

Axiom interquorum_c_v_certinfo:
  forall trace r p v,
    interquorum_property tau_c tau_v (saw_v trace r p v) trace.
Axiom interquorum_c_b_certinfo:
  forall trace r p v,
    interquorum_property tau_c tau_b (saw_v trace r p v) trace.

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
  move: H_saw => /(@hasP GState_eqType _ trace)=> -[g_mid H_g_mid].
  case:fndP => // key_mid.
  set u_mid: UState := g_mid.(users)[`key_mid].
  move => /andP [/andP[H_v_certval_mid H_blocks_mid] /step_leP H_mid_step_le].

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
    apply/andP;split;[apply/andP;split|].
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

Lemma honest_during_from_sent
  g0 trace (H_path: is_trace g0 trace)
  ix uid mty mval r p (H_send: user_sent_at ix trace uid (mty,mval,r,p,uid)):
    honest_during_step (msg_step (mty,mval,r,p,uid)) uid trace.
Proof using.
  move: H_send => [g1 [g2 [H_step H_send]]].
  have H_honest := negbT (user_sent_honest_post H_send).
  have H_in := in_fnd (user_sent_in_post H_send).
  apply (honest_during_from_ustate H_path (step_in_path_onth_post H_step) H_in H_honest).
  exact (utransition_label_end H_send H_in).
Qed.

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

  have H_no_nextvotes_open: forall uid s, honest_during_step (r,p,s) uid trace -> ~nextvoted_open_in_path trace r p s uid.
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

Lemma honest_in_from_during_and_send: forall r p s uid trace,
      honest_during_step (r,p,s) uid trace ->
  forall g0 (H_path : is_trace g0 trace),
  forall ix g1 g2,
    step_in_path_at g1 g2 ix trace ->
  forall mt v,
    user_sent uid (mt,v,r,p,uid) g1 g2 ->
  step_le (msg_step (mt,v,r,p,uid)) (r,p,s) ->
    honest_in_period r p uid trace.
Proof using.
  move => r p s uid trace H_honest g0 H_path ix g1 g2 H_step mt v H_sent H_msg_step.
  have H_g1 := step_in_path_onth_pre H_step.
  exists ix. rewrite H_g1.
  have key1 := user_sent_in_pre H_sent.
  rewrite (in_fnd key1).
  have H_step1 := utransition_label_start H_sent (in_fnd key1).
  lapply (user_honest_from_during H_path H_g1 (H_in:=key1)).
  *
    rewrite /user_honest (in_fnd key1) => /negP H_honest_g1.
    split;[assumption|].
    by injection H_step1.
  *
    revert H_honest.
    apply honest_during_le.
    rewrite H_step1.
    assumption.
Qed.

Theorem safety: forall g0 trace (r:nat),
    state_before_round r g0 ->
    is_trace g0 trace ->
    forall p1 v1, certified_in_period trace r p1 v1 ->
    forall p2 v2, certified_in_period trace r p2 v2 ->
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

(* L4: A vote message sent by t_H committee members in a step s>3 must have been sent by some honest nodes that decided to cert-vote for v during step 3. *)
(*
Definition from_cert_voter (v : Value) (r p s : nat) (m : Msg) (voters : {fset UserId}) path :=
  vote_msg m ->
  #|voters| >= tau_b ->
  (forall voter, voter \in voters -> committee_cred (credential voter round period step)) ->
  (forall voter, voter \in voters -> has_sent_vote_message_in r p s) ->
  s > 3 ->
*)

End AlgoSafety.
