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
Require Import algorand_model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* The user's state structure *)
(* Note that the user state structure and supporting functions and notations
   are all defined in local_state.v
 *)
Definition UState := algorand_model.UState.

Notation corrupt        := (local_state.corrupt UserId Value PropRecord Vote).
Notation round          := (local_state.round UserId Value PropRecord Vote).
Notation period         := (local_state.period UserId Value PropRecord Vote).
Notation step           := (local_state.step UserId Value PropRecord Vote).
Notation timer          := (local_state.timer UserId Value PropRecord Vote).
Notation deadline       := (local_state.deadline UserId Value PropRecord Vote).
Notation p_start        := (local_state.p_start UserId Value PropRecord Vote).
Notation stv            := (local_state.stv UserId Value PropRecord Vote).
Notation proposals      := (local_state.proposals UserId Value PropRecord Vote).
Notation blocks         := (local_state.blocks UserId Value PropRecord Vote).
Notation softvotes      := (local_state.softvotes UserId Value PropRecord Vote).
Notation certvotes      := (local_state.certvotes UserId Value PropRecord Vote).
Notation nextvotes_open := (local_state.nextvotes_open UserId Value PropRecord Vote).
Notation nextvotes_val  := (local_state.nextvotes_val UserId Value PropRecord Vote).

(* The global state *)
(* Note that the global state structure and supporting functions and notations
   are all defined in global_state.v
 *)
Definition GState := algorand_model.GState.

Notation now               := (global_state.now UserId algorand_model.UState [choiceType of Msg]).
Notation network_partition := (global_state.network_partition UserId algorand_model.UState [choiceType of Msg]).
Notation users             := (global_state.users UserId algorand_model.UState [choiceType of Msg]).
Notation msg_in_transit    := (global_state.msg_in_transit UserId algorand_model.UState [choiceType of Msg]).
Notation msg_history       := (global_state.msg_history UserId algorand_model.UState [choiceType of Msg]).

Notation "x # y ~> z" := (algorand_model.UTransitionInternal x y z) (at level 70) : type_scope.
Notation "a # b ; c ~> d" := (algorand_model.UTransitionMsg a b c d) (at level 70) : type_scope.
Notation "x ~~> y" := (algorand_model.GTransition x y) (at level 90) : type_scope.

Ltac finish_case := simpl;solve[repeat first[reflexivity|eassumption|split|eexists]].

(* Gather all the unfoldings we might want for working with transitions into
   a hint database for use with autounfold *)
Create HintDb utransition_unfold discriminated.
Hint Unfold
     (* UTransitionInternal *)
     propose_result      propose_ok repropose_ok no_propose_ok
     softvote_result     softvote_new_ok softvote_repr_ok no_softvote_ok
     certvote_result     certvote_ok no_certvote_ok
     nextvote_result     nextvote_val_ok nextvote_open_ok nextvote_stv_ok no_nextvote_ok
     certvote_timeout_ok
     (* UTransitionMsg *)
     set_softvotes       certvote_ok         certvote_result
     set_nextvotes_open  adv_period_open_ok  adv_period_open_result
     set_nextvotes_val   adv_period_val_ok   adv_period_val_result
     set_certvotes       certify_ok          certify_result
     vote_msg deliver_nonvote_msg_result : utransition_unfold.

Create HintDb gtransition_unfold discriminated.
Hint Unfold
     tick_ok tick_update tick_users
     delivery_result
     step_result
     is_partitioned recover_from_partitioned
     is_unpartitioned make_partitioned
     corrupt_user_result : gtransition_unfold.

Arguments delivery_result : clear implicits.

(* ------------------- *)
(* Generic path lemmas *)
(* ------------------- *)  

(* dropping elements from a path still results in a path *)
Lemma path_drop T (R:rel T) x p (H:path R x p) n:
  match drop n p with
  | List.nil => true
  | List.cons x' p' => path R x' p'
  end.
Proof using.
  by elim: n x p H=> [|n IHn] x [|a l /andP [] H_path];last apply IHn.
Qed.

Lemma path_drop' T (R:rel T) x p (H:path R x p) n:
  match drop n (x::p) with
  | [::] => true
  | [:: x' & p'] => path R x' p'
  end.
Proof using.
  elim: n x p H=> [|n IHn] x p H_path //=.
  move/IHn: {IHn}H_path.
  destruct n;simpl.
  by destruct p;[|move/andP => []].
  rewrite -add1n -drop_drop.
  by destruct (drop n p);[|destruct l;[|move/andP => []]].
Qed.

(* path still holds after taking n elements *)
Lemma path_prefix : forall T R p (x:T) n,
    path R x p -> path R x (take n p).
Proof using.
  induction p;[done|].
  move => /= x n /andP [Hr Hpath].
  destruct n. done.
  simpl;apply /andP;by auto.
Qed.

(* proposition does not hold initially but holds for last element implies there
   must be a point in the path where it becomes true *)
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

(* ----------------------- *)
(* generic multiset lemmas *)
(* ----------------------- *)

(* x in mset of seq iff x is in seq *)
Lemma in_seq_mset (T : choiceType) (x : T) (s : seq T):
  (x \in seq_mset s) = (x \in s).
Proof using.
  apply perm_eq_mem, perm_eq_seq_mset.
Qed.

Lemma map_mset_count {A B :choiceType} (f: A -> B) (m : {mset A}) :
  forall (b:B), (count (preim f (pred1 b)) m) = (map_mset f m) b.
Proof using.
  move => b.
  unfold map_mset.
  move: {m}(EnumMset.f m) => l.
  by rewrite mset_seqE count_map.
Qed.

Lemma map_mset_has {A B :choiceType} (f: A -> B) (m : {mset A}) :
  forall (b:pred B), has b (map_mset f m) = has (preim f b) m.
Proof using.
  move => b.
  rewrite -has_map.
  apply eq_has_r, perm_eq_mem, perm_eq_seq_mset.
Qed.

Lemma finsupp_mset_uniq (T:choiceType) (A:{mset T}):
  uniq (finsupp A).
Proof using.
  by rewrite -(perm_eq_uniq (perm_undup_mset A));apply undup_uniq.
Qed.

Lemma msubset_finsupp (T:choiceType) (A B: {mset T}):
  (A `<=` B)%mset ->
  perm_eq (finsupp A) [seq i <- finsupp B | i \in A].
Proof using.
  move=>H_sub.
  apply uniq_perm_eq.
    by apply finsupp_mset_uniq.
    by apply filter_uniq;apply finsupp_mset_uniq.
  move=>x.
  rewrite mem_filter.
  rewrite !msuppE.
  rewrite andb_idr //.
  move:H_sub => /msubset_subset. apply.
Qed.

Lemma msubset_size_sum (T:choiceType) (A B: {mset T}):
  (A `<=` B)%mset ->
  \sum_(i <- finsupp B) A i = size A.
Proof using.
  move=>H_sub.
  rewrite (bigID (fun i => i \in A)) /= -big_filter.
  rewrite -(eq_big_perm _ (msubset_finsupp H_sub)) -size_mset big1.
    by rewrite addn0.
    by move=>i /mset_eq0P.
Qed.

Lemma mset_add_size (T:choiceType) (A B : {mset T}):
  size (A `+` B) = (size A + size B)%nat.
Proof using.
  rewrite size_mset (eq_bigr (fun a => A a + B a)%nat);[|by move => ? _;rewrite msetE2].
  rewrite big_split !msubset_size_sum //.
  rewrite -{1}[B]mset0D. apply msetSD, msub0set.
  rewrite -{1}[A]msetD0. apply msetDS, msub0set.
Qed.

Lemma msetn_size (T:choiceType) n (x:T):
  size (msetn n x) = n.
Proof using.
  rewrite size_mset finsupp_msetn.
  case:n=>[|n] /=.
  exact: big_nil.
  by rewrite big_seq_fset1 msetnxx.
Qed.

Lemma msubset_size (T:choiceType) (A B : {mset T}):
  (A `<=` B)%mset -> size A <= size B.
Proof using.
  move=>H_sub.
  by rewrite -(msetBDK H_sub) mset_add_size leq_addl.
Qed.

Lemma msetD_seq_mset_perm_eq (T:choiceType) (A: {mset T}) (l l': seq T):
  A `+` seq_mset l = A `+` seq_mset l' -> perm_eq l l'.
Proof using.
  move/(f_equal (msetB^~A)); rewrite !msetDKB => H_seq_eq.
  apply/(perm_eq_trans _ (perm_eq_seq_mset l')).
  rewrite perm_eq_sym -H_seq_eq.
  apply perm_eq_seq_mset.
Qed.

(* ----------------------- *)
(* generic sequence lemmas *)
(* ----------------------- *)

Lemma perm_eq_cons1P (T : eqType) (s : seq T) (a : T) : reflect (s = [:: a]) (perm_eq s [:: a]).
Proof.
case: s => [|x s]; first by rewrite /perm_eq /= ?eqxx; constructor.
case: s => [|y s].
  apply: (iffP idP).
    rewrite /perm_eq /= ?eqxx.
    move/andP => [Ht Ht'].
    move: Ht.
    case Hax: (a == x) => //.
    by move/eqP: Hax =>->.
  by move =>->; apply perm_eq_refl.
apply: (iffP idP) => //.
set s1 := [:: _ & _].
set s2 := [:: _].
move => Hpr.
by have Hs: size s1 = size s2 by apply perm_eq_size.
Qed.

(* ------------------- *)
(* Generic definitions *)
(* ------------------- *)

(* turn pred on UState into pred on GState - assumed false if uid not present *)
Definition upred uid (P : pred UState) : pred GState :=
  fun g =>
    match g.(users).[? uid] with
    | Some u => P u
    | None => false
    end.

(* turn pred on UState into pred on GState - assumed true if uid not present *)
Definition upred' uid (P : pred UState) : pred GState :=
  fun g =>
    match g.(users).[? uid] with
    | Some u => P u
    | None => true
    end.

(* --------------------------------- *)
(* Lemmas about step of a user state *)
(* --------------------------------- *)

(* ssreflect: step_le is equivalent to step_leb *)
Lemma step_leP: forall s1 s2, reflect (step_le s1 s2) (step_leb s1 s2).
Proof using.
  clear.
  move => [[r1 p1] s1] [[r2 p2] s2].
  case H:(step_leb _ _);constructor;[|move/negP in H];
    by rewrite /step_le !(reflect_eq eqP, reflect_eq andP, reflect_eq orP).
Qed.

(* ssreflect: step_lt is equivalent to step_ltb *)
Lemma step_ltP: forall s1 s2, reflect (step_lt s1 s2) (step_ltb s1 s2).
Proof using.
  clear.
  move => [[r1 p1] s1] [[r2 p2] s2].
  case H:(step_ltb _ _);constructor;[|move/negP in H];
    by rewrite /step_lt !(reflect_eq eqP, reflect_eq andP, reflect_eq orP).
Qed.

(* weaken step: less-than implies less-than-or-equal *)
Lemma step_ltW a b:
  step_lt a b -> step_le a b.
Proof using.
  clear.
  destruct a as [[? ?] ?],b as [[? ?]?].
  unfold step_lt,step_le;intuition.
Qed.

(* transitivitity of step_le *)
Lemma step_le_trans a b c:
  step_le a b -> step_le b c -> step_le a c.
Proof using.
  destruct a as [[? ?] ?],b as [[? ?]?],c as [[? ?]?].
  unfold step_le.
  intros H_ab H_bc.
  destruct H_ab as [H_ab|[-> H_ab]];destruct H_bc as [H_bc|[-> H_bc]];[left..|];
    [eapply ltn_trans;eassumption|assumption|assumption|];
  right;split;[reflexivity|];clear -H_ab H_bc.
  destruct H_ab as [H_ab|[-> H_ab]];destruct H_bc as [H_bc|[-> H_bc]];[left..|];
    [eapply ltn_trans;eassumption|assumption|assumption|];
  right;split;[reflexivity|];clear -H_ab H_bc.
  eapply leq_trans;eassumption.
Qed.

(* transitivity of step_lt *)
Lemma step_lt_trans a b c:
  step_lt a b -> step_lt b c -> step_lt a c.
Proof using.
  destruct a as [[? ?] ?],b as [[? ?]?],c as [[? ?]?].
  unfold step_lt.
  intros H_ab H_bc.
  destruct H_ab as [H_ab|[-> H_ab]];destruct H_bc as [H_bc|[-> H_bc]];[left..|];
    [eapply ltn_trans;eassumption|assumption|assumption|];
  right;split;[reflexivity|];clear -H_ab H_bc.
  destruct H_ab as [H_ab|[-> H_ab]];destruct H_bc as [H_bc|[-> H_bc]];[left..|];
    [eapply ltn_trans;eassumption|assumption|assumption|];
  right;split;[reflexivity|];clear -H_ab H_bc.
  eapply ltn_trans;eassumption.
Qed.

(* a < b and b <= c -> a < c *)
Lemma step_lt_le_trans a b c:
  step_lt a b -> step_le b c -> step_lt a c.
Proof using.
  destruct a as [[? ?] ?],b as [[? ?]?],c as [[? ?]?].
  unfold step_lt, step_le.
  intros H_ab H_bc.
  destruct H_ab as [H_ab|[-> H_ab]];destruct H_bc as [H_bc|[-> H_bc]];[left..|];
    [eapply ltn_trans;eassumption|assumption|assumption|];
  right;split;[reflexivity|];clear -H_ab H_bc.
  destruct H_ab as [H_ab|[-> H_ab]];destruct H_bc as [H_bc|[-> H_bc]];[left..|];
    [eapply ltn_trans;eassumption|assumption|assumption|];
    right;split;[reflexivity|];clear -H_ab H_bc.
  eapply leq_trans;eassumption.
Qed.

(* a <= b and b < c -> a < c *)
Lemma step_le_lt_trans a b c:
  step_le a b -> step_lt b c -> step_lt a c.
Proof using.
  destruct a as [[? ?] ?],b as [[? ?]?],c as [[? ?]?].
  unfold step_lt, step_le.
  intros H_ab H_bc.
  destruct H_ab as [H_ab|[-> H_ab]];destruct H_bc as [H_bc|[-> H_bc]];[left..|];
    [eapply ltn_trans;eassumption|assumption|assumption|];
  right;split;[reflexivity|];clear -H_ab H_bc.
  destruct H_ab as [H_ab|[-> H_ab]];destruct H_bc as [H_bc|[-> H_bc]];[left..|];
    [eapply ltn_trans;eassumption|assumption|assumption|];
    right;split;[reflexivity|];clear -H_ab H_bc.
  eapply leq_ltn_trans;eassumption.
Qed.

(* step is not less than itself *)
Lemma step_lt_irrefl r p s: ~step_lt (r,p,s) (r,p,s).
Proof using.
  clear.
  unfold step_lt;intuition;by rewrite -> ltnn in * |- .
Qed.

(* step is less than or equal to itself *)
Lemma step_le_refl step: step_le step step.
Proof using.
  clear;unfold step_le;intuition.
Qed.

(* ustate_after and step_le equivalence *)
Lemma ustate_after_iff_step_le u1 u2:
  step_le (step_of_ustate u1) (step_of_ustate u2)
  <-> ustate_after u1 u2.
Proof using.
  unfold ustate_after;destruct u1, u2;simpl.
  clear;tauto.
Qed.

(* transitivity of ustate_after *)
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

(* --------------------------- *)
(* Lemmas about tick functions *)
(* --------------------------- *)

(* ssreflect: tick_ok_users function as a proposition *)
Lemma tick_ok_usersP : forall increment (g : GState),
  reflect
    (forall (uid : UserId) (h : uid \in domf g.(users)), user_can_advance_timer increment g.(users).[h])
    (tick_ok_users increment g).
Proof using.
move => increment g.
exact: allfP.
Qed.

(* Domain of users unchanged after tick *)
Lemma tick_users_domf : forall increment pre,
  domf pre.(users) = domf (tick_users increment pre).
Proof using.
move => increment pre.
by rewrite -updf_domf.
Qed.

(* tick_users at uid results in user_advance_timer *)
Lemma tick_users_upd : forall increment pre uid (h : uid \in domf pre.(users)),
  (tick_users increment pre).[? uid] = Some (user_advance_timer increment pre.(users).[h]).
Proof using.
move => increment pre uid h.
by rewrite updf_update.
Qed.

(* tick_users results in None if user not in domain of pre-state *)
Lemma tick_users_notin : forall increment pre uid (h : uid \notin domf pre.(users)),
  (tick_users increment pre).[? uid] = None.
Proof using.
  move => increment pre uid h.
  apply not_fnd.
  change (uid \notin domf (tick_users increment pre)); by rewrite -updf_domf.
Qed.

(* ------------------------------------------------- *)
(* Lemmas about merge_msgs_deadline, send_broadcasts *)
(* ------------------------------------------------- *)

(* A message in merge_msgs_deadline is either already in the mailbox or
   it is a member of the messages being merged *)
Lemma in_merge_msgs : forall d (msg:Msg) now msgs mailbox,
    (d,msg) \in merge_msgs_deadline now msgs mailbox ->
    msg \in msgs \/ (d,msg) \in mailbox.
Proof.
  move=> d msg now msgs mb.
  move=> /msetDP [|];[|right;done].
  by rewrite (perm_eq_mem (perm_eq_seq_mset _)) => /mapP [x H_x [_ ->]];left.
Qed.

(* send_broadcasts definition *)
Lemma send_broadcastsE now targets prev_msgs msgs:
  send_broadcasts now targets prev_msgs msgs = updf prev_msgs targets (fun _ => merge_msgs_deadline now msgs).
Proof using.
  by rewrite unlock.
Qed.

(* send_broadcasts at uid results in merge_msgs_deadline *)
Lemma send_broadcasts_in : forall (msgpool : MsgPool) now uid msgs targets
                                  (h : uid \in msgpool) (h' : uid \in targets),
  (send_broadcasts now targets msgpool msgs).[? uid] = Some (merge_msgs_deadline now msgs msgpool.[h]).
Proof using.
  by move => *;rewrite send_broadcastsE updf_update.
Qed.

(* send_brodcasts results in None if user not in domain of msgpool *)
Lemma send_broadcast_notin : forall (msgpool : MsgPool) now uid msgs targets
                                    (h : uid \notin domf msgpool),
  (send_broadcasts now targets msgpool msgs).[? uid] = None.
Proof using.
  move => *;apply not_fnd.
  change (?k \notin ?f) with (k \notin domf f).
  by rewrite send_broadcastsE -updf_domf.
Qed.

(* send_brodcasts at uid results in msgpool at uid if uid in msgpool but 
   uid not in targets of send_broadacsts function *)
Lemma send_broadcast_notin_targets : forall (msgpool : MsgPool) now uid msgs targets
                                            (h : uid \in msgpool) (h' : uid \notin targets),
  (send_broadcasts now targets msgpool msgs).[? uid] = msgpool.[? uid].
Proof using.
  move => msgpool now uid msg targets h h'.
  by rewrite send_broadcastsE updf_update' // in_fnd.
Qed.

(* send_broadcast contains msg but original mailbox does not, msg must be in l *)
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

(* ---------------------- *)
(* Lemmas about onth/step *)
(* -----------------------*)

(* onth results in Some if index is small *)
Lemma onth_size : forall T (s:seq T) n x, onth s n = Some x -> n < size s.
Proof using.
  clear.
  move => T s n x H.
  rewrite ltnNge.
  apply/negP.
  contradict H.
  unfold onth.
  by rewrite drop_oversize.
Qed.

(* If onth of a prefix is not None then onth of the original seq is the same *)
Lemma onth_from_prefix T (s:seq T) k n x:
    onth (take k s) n = Some x ->
    onth s n = Some x.
Proof.
  move => H_prefix.
  have H_inbounds: n < size (take k s)
    by rewrite ltnNge;apply/negP => H_oversize;
                                      rewrite /onth drop_oversize in H_prefix.
  move: H_prefix.
  unfold onth, ohead.
  rewrite -{2}(cat_take_drop k s) drop_cat H_inbounds.
  by case: (drop n (take k s)).
Qed.

(* onth is Some x implies nth is x *)
Lemma onth_nth T (s:seq T) ix x:
  onth s ix = Some x -> (forall x0, nth x0 s ix = x).
Proof using.
  unfold onth.
  unfold ohead.
  move => H_drop x0.
  rewrite -[ix]addn0 -nth_drop.
  destruct (drop ix s);simpl;congruence.
Qed.

(* onth is Some x means x is in the seq *)
Lemma onth_in (T:eqType) (s:seq T) ix x:
  onth s ix = Some x -> x \in s.
Proof using.
  clear.
  intro H.
  rewrite -(onth_nth H x).
  exact (mem_nth _ (onth_size H)).
Qed.

(* onth is Some x means last element of prefixed sequence is x *)
Lemma onth_take_last T (s:seq T) n x:
  onth s n = some x ->
  forall x0, last x0 (take n.+1 s) = x.
Proof using.
  clear.
  move => H_x x0.
  have H_size := onth_size H_x.
  rewrite -nth_last size_takel // nth_take //.
    by apply onth_nth.
Qed.

(* True for all elements of a sequence implies true for element returned by onth *)
Lemma all_onth T P s: @all T P s -> forall ix x, onth s ix = Some x -> P x.
Proof.
  move/all_nthP => H ix x H_g. rewrite -(onth_nth H_g x).
  apply H, (onth_size H_g).
Qed.

(* at_step holds for nth element with P and nth element is g, then P g holds *)
Lemma at_step_onth n (path : seq GState) (P : pred GState):
  at_step n path P ->
  forall g, onth path n = Some g ->
  P g.
Proof using.
  unfold at_step, onth.
  destruct (drop n path) eqn:Hdrop;rewrite Hdrop;simpl;congruence.
Qed.

(* nth element is g and P g holds, then at_step holds for n and P *)
Lemma onth_at_step n (path : seq GState) g:
  onth path n = Some g ->
  forall (P : pred GState), P g -> at_step n path P.
Proof using.
  unfold at_step, onth.
  destruct (drop n path) eqn:Hdrop;rewrite Hdrop;simpl;congruence.
Qed.

(* onth true at ix implies onth true at truncated trace for size of new trace - 1 *)
Lemma onth_take_some : forall (trace: seq GState) ix g,
  onth trace ix = Some g ->
  onth (take ix.+1 trace) (size (take ix.+1 trace)).-1 = Some g.
Proof.
  move => trace ix g H_onth.
  clear -H_onth.
  unfold onth.
  erewrite drop_nth with (x0:=g). simpl.
  rewrite nth_last. erewrite onth_take_last with (x:=g); try assumption.
  trivial.
  destruct trace. inversion H_onth. intuition.
Qed.

(* ---------------------------- *)
(* Lemmas about step_in_path_at *)
(* ---------------------------- *)

(* step in path at n from g1 to g2 means g1 is at index n *)
Lemma step_in_path_onth_pre {g1 g2 n path} (H_step : step_in_path_at g1 g2 n path)
  : onth path n = Some g1.
Proof using.
  unfold step_in_path_at in H_step.
  unfold onth. destruct (drop n path) as [|? []];destruct H_step.
  rewrite H;reflexivity.
Qed.

(* step in path at n from g1 to g2 means g2 is at index n+1 *)
Lemma step_in_path_onth_post {g1 g2 n path} (H_step : step_in_path_at g1 g2 n path)
  : onth path n.+1 = Some g2.
Proof using.
  unfold step_in_path_at in H_step.
  unfold onth. rewrite -add1n -drop_drop.
  destruct (drop n path) as [|? []];destruct H_step.
  rewrite H0;reflexivity.
Qed.

(* step_in_path_at of truncated path implies step_in_path_at of original path *)
Lemma step_in_path_prefix (g1 g2 : GState) n k (path : seq GState) :
  step_in_path_at g1 g2 n (take k path)
  -> step_in_path_at g1 g2 n path.
Proof using.
  revert k path;induction n.
  intros k path;
  destruct path;[done|];destruct k;[done|];
  destruct path;[done|];destruct k;done.
  intros k path. destruct k.
  clear;intro;exfalso;destruct path;assumption.
  unfold step_in_path_at.
  destruct path. done.
  simpl. apply IHn.
Qed.

(* step_in_path_at implies step_in_path_at of truncated path provided truncation
   is sufficiently long *)
Lemma step_in_path_take (g1 g2 : GState) n (path : seq GState) :
  step_in_path_at g1 g2 n path
  -> step_in_path_at g1 g2 n (take n.+2 path).
Proof using.
  revert path; induction n.
  intro path.
  destruct path;[done|];destruct path;done.
  intros path.
  unfold step_in_path_at.
  destruct path. done.
  simpl. apply IHn.
Qed.

(* -------------------------------------------------- *)
(* Lemmas for reset_msg_delays, reset_user_msg_delays *)
(* -------------------------------------------------- *)

(* Reset_deadline in reset_user_msg_delays if m in msgs *)
Lemma reset_msg_delays_fwd : forall (msgs : {mset R * Msg}) (m : R * Msg),
    m \in msgs -> forall now, (reset_deadline now m \in reset_user_msg_delays msgs now).
Proof using.
  move => msgs m Hm now.
  rewrite -has_pred1 /= has_count.
  have Hcnt: (0 < count_mem m msgs) by rewrite -has_count has_pred1.
  eapply leq_trans;[eassumption|clear Hcnt].
  rewrite (count_mem_mset (reset_deadline now m) (reset_user_msg_delays msgs now)).
  rewrite /reset_user_msg_delays -map_mset_count.
  apply sub_count.
  by move => H /= /eqP ->.
Qed.

(* If m was in reset_user_msg_delays then the deadline must have been reset *)
Lemma reset_user_msg_delays_rev (now : R) (msgs : {mset R * Msg}) (m: R*Msg):
  m \in reset_user_msg_delays msgs now ->
  exists d0, m = reset_deadline now (d0,m.2) /\ (d0,m.2) \in msgs.
Proof using.
  move => Hm.
  suff: (has (preim (reset_deadline now) (pred1 m)) msgs).
    move: m Hm => [d msg] Hm.
    move/hasP => [[d0 msg0] H_mem H_preim].
    move: H_preim; rewrite /preim /pred1 /= /reset_deadline /=.
    case/eqP => Hn Hd; rewrite -Hd -Hn.
    by exists d0; split.
  by rewrite has_count map_mset_count -count_mem_mset -has_count has_pred1.
Qed.

(* Domain of msgpool unchanged after reste_msg_delays *)
Lemma reset_msg_delays_domf : forall (msgpool : MsgPool) now,
   domf msgpool = domf (reset_msg_delays msgpool now).
Proof using. by move => msgpool pre; rewrite -updf_domf. Qed.

(* reset_msg_delays at uid results in reset_user_msg_delays *)
Lemma reset_msg_delays_upd : forall (msgpool : MsgPool) now uid (h : uid \in domf msgpool),
  (reset_msg_delays msgpool now).[? uid] = Some (reset_user_msg_delays msgpool.[h] now).
Proof using.
move => msgpool now uid h.
have Hu := updf_update _ h.
have Hu' := Hu (domf msgpool) _ h.
by rewrite Hu'.
Qed.

(* reset_msg_delays results in None if user not in domain of msgpool *)
Lemma reset_msg_delays_notin : forall (msgpool : MsgPool) now uid
  (h : uid \notin domf msgpool),
  (reset_msg_delays msgpool now).[? uid] = None.
Proof using.
  move => msgpool now uid h.
  apply not_fnd.
  change (uid \notin domf (reset_msg_delays msgpool now)).
  unfold reset_msg_delays.
  by rewrite -updf_domf.
Qed.

(* ------------------- *)
(* Reachability lemmas *)
(* ------------------- *)

(* step_in_path_at implies GTransition *)
Lemma transition_from_path
      g0 states ix (H_path: is_trace g0 states)
      g1 g2
      (H_step : step_in_path_at g1 g2 ix states):
  GTransition g1 g2.
Proof using.
  unfold step_in_path_at in H_step.
  destruct states. inversion H_path.
  destruct H_path as [H_g0 H_path]; subst.
  have {H_path} := path_drop' H_path ix.
  destruct (drop ix (g :: states));[done|].
  destruct l;[done|].
  destruct H_step as [-> ->].
  simpl.
  by move/andP => [] /asboolP.
Qed.

(* greachable and GReachable definitions are equivalent in our setting *)

Lemma greachable_GReachable : forall g0 g, greachable g0 g -> GReachable g0 g.
Proof using.
  move => g0 g; case => x.
  destruct x. inversion 1.
  move => [H_g0 H_path]; subst g1.
  revert H_path.
  move: g0 g.
  elim: x => /=; first by move => g0 g Ht ->; exact: rt1n_refl.
  move => g1 p IH g0 g.
  move/andP => [Hg Hp] Hgg.
  have IH' := IH _ _ Hp Hgg.
  move: IH'; apply: rt1n_trans.
    by move: Hg; move/asboolP.
Qed.

(* Lemma GReachable_greachable : forall g0 g, GReachable g0 g -> greachable g0 g. *)
(* Proof using. *)
(* move => g0 g. *)
(* elim; first by move => x; exists [::]. *)
(* move => x y z Hxy Hc. *)
(* case => p Hp Hl. *)
(* exists (y :: p) => //=. *)
(* apply/andP. *)
(* by split => //; apply/asboolP. *)
(* Qed. *)

(* ----------------------------------------------- *)
(* Definitions and lemmas for sent/forged messages *)
(* ----------------------------------------------- *)

Definition user_sent sender (m : Msg) (pre post : GState) : Prop :=
  exists (ms : seq Msg), m \in ms
  /\ ((exists d incoming, related_by (lbl_deliver sender d incoming ms) pre post)
      \/ (related_by (lbl_step_internal sender ms) pre post)).

Definition user_forged (msg:Msg) (g1 g2: GState) :=
  let: (mty,v,r,p,sender) := msg in
  related_by (lbl_forge_msg sender r p mty v) g1 g2.

Definition user_sent_at ix path uid msg :=
  exists g1 g2, step_in_path_at g1 g2 ix path
                /\ user_sent uid msg g1 g2.

(* user who sends a message must be in both pre and post states *)
Lemma user_sent_in_pre {sender m pre post} (H : user_sent sender m pre post):
  sender \in pre.(users).
Proof using.
  destruct H as [msgs [H_mem [[d [recv H_step]] | H_step]]];
    simpl in H_step; decompose record H_step;clear H_step;assumption.
Qed.

Lemma user_sent_in_post {sender m pre post} (H : user_sent sender m pre post):
  sender \in post.(users).
Proof using.
  destruct H as [msgs [H_mem [[d [recv H_step]] | H_step]]];
    simpl in H_step; decompose record H_step;subst post;clear;
      unfold delivery_result, step_result;destruct pre;simpl;clear;
  change (sender \in domf (users.[sender <- x0])); rewrite dom_setf; apply fset1U1.
Qed.

(* step of user in pre-state who sends message is same as message step *)
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

(* step of user in post-state who sends message is greater than message step *)
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

(* ---------------------------------- *)
(* Definitions for receiving messages *)
(* ---------------------------------- *)

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

(* --------------------- *)
(* Labelling transitions *)
(* --------------------- *)

(* all global transitions have some label *)
Lemma transitions_labeled: forall g1 g2,
    g1 ~~> g2 <-> exists lbl, related_by lbl g1 g2.
Proof using.
  split.
  + (* forward - find label for transition *)
    destruct 1;simpl.
    exists (lbl_tick increment);finish_case.
    destruct pending as [deadline msg];exists (lbl_deliver uid deadline msg sent);finish_case.
    exists (lbl_step_internal uid sent);finish_case.
    exists (lbl_exit_partition);finish_case.
    exists (lbl_enter_partition);finish_case.
    exists (lbl_corrupt_user uid);finish_case.
    exists (lbl_replay_msg uid);finish_case.
    exists (lbl_forge_msg sender r p mtype mval);finish_case.
  + (* reverse - find transition from label *)
    destruct 1 as [[] Hrel];simpl in Hrel;decompose record Hrel;clear Hrel;subst g2;
      [eapply step_tick
      |eapply step_deliver_msg
      |eapply step_internal
      |eapply step_exit_partition
      |eapply step_enter_partition
      |eapply step_corrupt_user
      |eapply step_replay_msg
      |eapply step_forge_msg];eassumption.
    (* econstructor takes a very long time being confused between
       different steps that build the result with send_broadcasts *)
Qed.

(* internal transition changes state - used in transition_label_unique *)
Lemma internal_not_noop :
  forall s pre post l,
    s # pre ~> (post, l) ->
    pre <> post.
Proof.
  move => s pre post l Hst;inversion Hst;subst;
  autounfold with utransition_unfold in H2;decompose record H2;clear H2;
    match goal with [H : valid_rps _ _ _ _ |- _] =>
      destruct H as [_ [_ H_s]];contradict H_s;rewrite H_s;simpl;clear
    end;try discriminate; by rewrite addn1 => /esym /n_Sn.
Qed.

(* delivery_result decreases size of mailbox - used in transition_label_unique *)
Lemma deliver_analysis1:
  forall g uid upost r m l
         (key_mbox : uid \in g.(msg_in_transit)),
    (r, m) \in g.(msg_in_transit).[key_mbox] ->
    let g2 := delivery_result g uid key_mbox (r, m) upost l in
    (forall uid2,
      ( size (odflt mset0 (g2.(msg_in_transit).[?uid2]))
      < size (odflt mset0 (g.(msg_in_transit).[?uid2]))) <->
      uid = uid2)
    /\ [mset (r,m)] =( odflt mset0 (g.(msg_in_transit).[?uid])
       `\` odflt mset0 (g2.(msg_in_transit).[?uid]))%mset.
Proof using.
  clear.
  move=> g uid upost r m l key_mbox H_pending g2.

  set mb1: {mset R*Msg} := odflt mset0 (g.(msg_in_transit).[?uid]).
  set mb2: {mset R*Msg} := odflt mset0 (g2.(msg_in_transit).[?uid]).
  assert (H_singleton: mb1 = (r,m) +` mb2).
  {
    subst mb1 mb2.
    rewrite /g2 /delivery_result send_broadcastsE.
  rewrite updf_update'.
  simpl. by rewrite in_fset1U; apply/orP; left.
  intro H_uid.
  rewrite in_fnd.
  repeat match goal with
           [|- context C[odflt mset0 (Some ?x)]] =>
           assert (H :odflt mset0 (Some x) = x) by done; rewrite H; clear H
         end.
  rewrite setfNK; rewrite eq_refl.
  by rewrite msetBDKC;[|rewrite msub1set].
  by rewrite fsetD11.
  }
  split;[|by move:H_singleton => /(f_equal (msetB^~mb2)) ->;rewrite msetDC msetDKB].

  move => uid2.
  split; last first.
  intros <-.
  fold mb1 mb2.
  by rewrite H_singleton mset_add_size msetn_size leqnn.

  intro H_size.
  case H_neq:(uid2 == uid);[by move/eqP: H_neq|exfalso].

  subst g2.
  unfold delivery_result in *.
  cbn [global_state.msg_in_transit
         set_GState_users
         set_GState_msg_history
         set_GState_msg_in_transit] in *.

  clear mb1 mb2 H_singleton.
  remember ((g.(msg_in_transit)).[uid <- ((g.(msg_in_transit)).[key_mbox] `\ (r, m))%mset]) as mailboxes'.
  case:mailboxes'.[?uid2]/fndP => H_mb.
  2: {
    assert (H_mb' := H_mb).
    move/not_fnd in H_mb'.
    subst mailboxes'. rewrite fnd_set in H_mb'.
    rewrite H_neq in H_mb'.
    rewrite H_mb' in H_size.
    rewrite size_mset0 in H_size.
    inversion H_size.
  }

  assert (H_uid2 : uid2 \in domf g.(msg_in_transit)).
  rewrite -fndSome.
  assert (mailboxes'.[? uid2] = Some mailboxes'.[H_mb]). by rewrite in_fnd.
  subst mailboxes'.
  rewrite fnd_set in H.
  rewrite H_neq in H. rewrite H.
  done.

  rewrite send_broadcastsE in H_size.
  destruct (uid2 \in domf (honest_users (g.(users)))) eqn:H_honest; last first.
  {
    rewrite updf_update' in H_size.
    rewrite in_fnd in H_size.
    simpl in H_size.
    subst.
    rewrite setfNK in H_size.
    rewrite H_neq in H_size.
    rewrite ltnn in H_size; discriminate.

    rewrite in_fsetD1.
    apply/andP. move => [_ H_honest'].
      by rewrite H_honest in H_honest'.
  }

  {
    rewrite updf_update in H_size.
    rewrite in_fnd in H_size.
    simpl in H_size.
    subst.
    rewrite setfNK in H_size.
    rewrite H_neq in H_size.
    simpl in H_size.
    move: H_size. rewrite ltnNge.
    apply/negP/negPn.
    apply/msubset_size.
    move: (g.(msg_in_transit)[`H_uid2]) => mb.
    rewrite -{1}[mb]mset0D.
    by apply msetSD, msub0set.

    rewrite in_fsetD1.
    apply/andP. split.
      by move/eqP in H_neq; move/eqP: H_neq.
      by apply/negP; move/negP in H_honest.
  }
Qed.

(* message transition with same resulting state has same output messages - 
   used in transition_label_unique *)
Lemma utransition_msg_result_analysis uid upre m upost l l'
      (H_step: uid # upre; m ~> (upost, l))
      (H_step': uid # upre; m ~> (upost, l')):
  l = l'.
Proof.
  clear -H_step H_step'.
  remember (upost,l) as ustate_out.
  destruct H_step eqn:H_trans; case: Hequstate_out;
    intros <- <-; inversion H_step'; subst; try (by []); exfalso.
  subst pre'; subst pre'0; clear -H2 H6.
  unfold set_softvotes, certvote_ok, valid_rps in H2; simpl in H2.
    by rewrite <- H6 in H2; intuition.
  subst pre'; subst pre'0; clear -c H6.
  unfold set_softvotes, certvote_ok, valid_rps in c; simpl in c.
    by rewrite H6 in c; intuition.
  unfold vote_msg in H3; simpl in H3.
    by intuition.
  subst pre'; subst pre'0.
  unfold deliver_nonvote_msg_result, certvote_result in H.
  destruct pre; simpl in *.
  case: H; intros <-; intro; clear -H3.
  unfold certvote_ok, set_softvotes, valid_rps in H3; simpl in H3.
    by intuition.
Qed.

(* delivery_result on a global state is the same means the message delivery
   transitions are equal - used in transition_label_unique *)
Lemma deliver_deliver_lbl_unique :
  forall g uid uid' upost upost' r r' m m' l l'
    (key_state : uid \in g.(users)) (key_mbox : uid \in g.(msg_in_transit))
    (key_state' : uid' \in g.(users)) (key_mbox' : uid' \in g.(msg_in_transit)),
    ~ g.(users).[key_state].(corrupt) ->
    (r, m) \in g.(msg_in_transit).[key_mbox] ->
    uid # g.(users).[key_state] ; m ~> (upost, l) ->
    ~ g.(users).[key_state'].(corrupt) ->
    (r', m') \in g.(msg_in_transit).[key_mbox'] ->
    uid' # g.(users).[key_state'] ; m' ~> (upost', l') ->
    delivery_result g uid key_mbox (r, m) upost l = delivery_result g uid' key_mbox' (r', m') upost' l' ->
    uid = uid' /\ r = r' /\ m = m' /\ l = l'.
Proof using.
  clear.
  move => g uid uid' upost upost' r r' m m' l l' key_state key_mbox key_state' key_mbox'
          H_honest H_pending H_step H_honest' H_pending' H_step' H_results.
  have Fact1 :=
    deliver_analysis1 upost l H_pending.
  have Fact1' :=
    deliver_analysis1 upost' l' H_pending'.
  have {Fact1 Fact1'}[H_uids H_pendings] : uid = uid' /\ [mset (r,m)] = [mset (r',m')].
  {
  move: H_results Fact1 Fact1' => <-.
  set g2 := delivery_result g uid key_mbox (r, m) upost l.
  cbv zeta. clearbody g2. clear.
  move => [H_uid H_pending] [H_uid' H_pending'].
  have H: uid = uid by reflexivity.
  rewrite <-H_uid, H_uid' in H;subst uid'.
  by split;[|rewrite H_pending -H_pending'].
  }
  subst uid'.
  have {H_pendings}[H_r H_m]: (r,m) = (r',m') by apply/mset1P;rewrite -H_pendings mset11.
  subst r' m'.
  repeat (split;[reflexivity|]).

  have H: upost = upost'
    by move: (f_equal (fun g => g.(users).[?uid]) H_results);
       rewrite !fnd_set eq_refl;clear;congruence.
  subst upost'.

  rewrite (bool_irrelevance key_state' key_state) in H_step'.
  move: (g.(users)[`key_state]) H_step H_step' => upre.
  clear.

  apply utransition_msg_result_analysis.
Qed.

(* message delivery transition cannot be the same as internal transition -
   used in transition_label_unique *)
Lemma deliver_internal_False :
  forall g uid uid' upost upost' r m l l'
    (key_state : uid \in g.(users)) (key_mbox : uid \in g.(msg_in_transit))
    (key_state' : uid' \in g.(users)),
    ~ g.(users).[key_state].(corrupt) ->
    (r, m) \in g.(msg_in_transit).[key_mbox] ->
    uid # g.(users).[key_state] ; m ~> (upost, l) ->
    ~ g.(users).[key_state'].(corrupt) ->
    uid' # g.(users).[key_state'] ~> (upost', l') ->
    delivery_result g uid key_mbox (r, m) upost l = step_result g uid' upost' l' ->
    False.
Proof using.
clear.
move => g uid uid' upost upost' r m l l' key_state key_mbox key_state'.
move => H_honest H_msg H_step H_honest' H_step'.
rewrite/delivery_result /= /step_result /=.
set us1 := _.[uid <- _].
set us2 := _.[uid' <- _].
set sb1 := send_broadcasts _ _ _ _.
set sb2 := send_broadcasts _ _ _ _.
move => Heq.
have Hus: us2 = us1 by move: Heq; move: (us1) (us2) => us3 us4; case.
have Hsb: sb1 = sb2 by case: Heq.
clear Heq.
case Hueq: (uid' == uid); last first.
  move/eqP: Hueq => Hueq.
  have Hus1c: us2.[? uid'] = us1.[? uid'] by rewrite Hus.
  move: Hus1c.
  rewrite 2!fnd_set.
  case: ifP; case: ifP.
  - by move/eqP.
  - move => _ _ Hpost.
    suff Hsuff: (global_state.users UserId UState [choiceType of Msg] g) [` key_state'] = upost'.
      move: H_step'.
      by move/internal_not_noop.
    apply sym_eq in Hpost.
    move: Hpost.
    rewrite in_fnd.
    by case.
  - by move /eqP.
  - by move => _ /eqP.
move/eqP: Hueq => Hueq.
move: Hsb.
rewrite /sb1 /sb2 Hueq.
move: H_msg.
clear.
set fs := [fset _ | _ in _].
set sb1 := send_broadcasts _ _ _ _.
set sb2 := send_broadcasts _ _ _ _.
move => H_msg Hsb.
have Hsb12: sb1.[? uid] = sb2.[? uid] by rewrite Hsb.
move: Hsb12.
rewrite send_broadcast_notin_targets; first rewrite send_broadcast_notin_targets //.
- rewrite fnd_set.
  case: ifP; last by move/eqP.
  move => _.
  rewrite in_fnd; case.
  move: H_msg.
  set ms := (global_state.msg_in_transit _ _ _ _ _).
  move => H_msg.
  move/msetP => Hms.
  move: (Hms (r, m)).
  rewrite msetB1E.
  case Hrm: ((r, m) == (r, m)); last by move/eqP: Hrm.
  rewrite /=.
  move: H_msg.
  rewrite -mset_neq0.
  move/eqP.
  case: (ms (r, m)) => //.
  move => n _.
  by ppsimpl; lia.
- rewrite in_fsetE /=.
  apply/negP.
  case/andP => Hf.
  case/negP: Hf.
  by rewrite in_fsetE.
- rewrite 2!in_fsetE.
  by apply/orP; left.
- rewrite in_fsetE /= in_fsetE.
  apply/negP.
  case/andP => Hf.
  by case/negP: Hf.
Qed.

(* internal transition with equal post-states with the same messages sent must
   have sent the messages in the same order - used in transition_label_unique *)
Lemma utransition_result_perm_eq uid upre upost l l' :
  uid # upre ~> (upost, l) ->
  uid # upre ~> (upost, l') ->
  perm_eq l l' ->
  l = l'.
Proof.
move => Htr Htr' Hpq.
case Hs: (size l') => [|n].
  move: Hs Hpq.
  move/size0nil =>->.
  by move/perm_eq_nilP.
case Hn: n => [|n'].
  move: Hs.
  rewrite Hn.
  destruct l' => //=.
  case Hl': (size l') => //.
  move: Hpq.
  move/size0nil: Hl' =>->.
  by move/perm_eq_cons1P.
move: Hs.
rewrite Hn => Hl'.
have Heq: size l = size l' by apply perm_eq_size.
move: Heq.
rewrite Hl' => Hl.
have Hll': size l' >= 2 by rewrite Hl'.
have Hll: size l >= 2 by rewrite Hl.
clear n n' Hn Hl' Hl.
inversion Htr; inversion Htr'; subst; simpl in *; try by [].
move: Hpq.
set m1 := (Proposal, _, _, _, _).
set m2 := (Block, _, _, _, _).
set s1 :=  [:: _; _].
set s2 :=  [:: _; _].
move => Hpm.
have Hm1: m1 \in s2.
  rewrite -(perm_eq_mem Hpm) /= inE.
  by apply/orP; left.
have Hm2: m2 \in s2.
  rewrite -(perm_eq_mem Hpm) /= inE.
  apply/orP; right.
  by rewrite inE.
move: Hm1 Hm2.
rewrite inE.
move/orP; case; last by rewrite inE.
rewrite /s2.
move/eqP =><-.
rewrite inE.
move/orP; case; first by move/eqP.
rewrite inE.
by move/eqP =><-.
Qed.

(* This lemma is necessary for technical reasons to rule out the possibility
   that a step that counts as one user sending a message can't also count as a
   send from a different user or different message *)
Lemma transition_label_unique : forall lbl lbl2 g1 g2,
    related_by lbl g1 g2 ->
    related_by lbl2 g1 g2 ->
    match lbl with
    | lbl_deliver _ _ _ _ =>
      match lbl2 with
      | lbl_deliver _ _ _ _ => lbl2 = lbl
      | lbl_step_internal _ _=> lbl2 = lbl
      | _ => True
      end
    | lbl_step_internal _ _=>
      match lbl2 with
      | lbl_deliver _ _ _ _ => lbl2 = lbl
      | lbl_step_internal _ _=> lbl2 = lbl
      | _ => True
      end
    | _ => True
    end.
Proof using.
  move => lbl lbl2 g1 g2.
  destruct lbl eqn:H_lbl;try done.
  + (* deliver *)
    (* one user changed, with a message removed from their mailbox *)
    rewrite /=.
    move => [key_ustate [ustate_post [H_step H]]].
    move: H => [Hcorrupt [key_mailbox [Hmsg Hg2]]].
    rewrite Hg2 {Hg2} /related_by.
    destruct lbl2;try done.
    * (* deliver/deliver *)
      move => [key_ustate' [ustate_post' [H_step' [Hcorrupt' [key_mailbox' [Hmsg' Heq]]]]]].
      eapply deliver_deliver_lbl_unique in Heq; eauto.
      move: Heq => [Hs [Hr [Hm Hl]]].
      by rewrite Hs Hr Hm Hl.
    * (* deliver/internal *)
      move => [key_user [ustate_post' [Hcorrupt' [H_step' Heq]]]].
      by eapply deliver_internal_False in Heq; eauto.
  + (* step internal *)
    rewrite /=. (* one user changed, no message removed *)
    move => [key_ustate [ustate_post [H_corrupt [Hstep Hres]]]].
    rewrite Hres {Hres} /related_by.
    destruct lbl2;try done.
    * (* internal/deliver *)
      move => [key_ustate' [upost' [H_step' [H_corrupt' [key_mbox [Hmsg Heq]]]]]].
      apply sym_eq in Heq.
      by eapply deliver_internal_False in Heq; eauto.
    * (* internal/internal *)
      move => [key_user [ustate_post0 [Hcorrupt0 [Htr0 Heq]]]].
      case Hs: (s == s0); last first.
        move/eqP: Hs => Hs.
        move: Heq.
        rewrite /step_result /= /step_result /=.
        set us1 := _.[_ <- _].
        set us2 := _.[_ <- _].
        move => Heq.
        have Hus: us1 = us2 by move: Heq; move: (us1) (us2) => us3 us4; case.
        clear Heq.
        have Hus1c: us1.[? s0] = us2.[? s0] by rewrite Hus.
        move: Hus1c.
        rewrite 2!fnd_set.
        case: ifP => [|_]; first by move/eqP => Hs'; case: Hs.
        case: ifP => [_|]; last by move/eqP.
        rewrite in_fnd; case => Hg.
        by apply internal_not_noop in Htr0.
      move/eqP: Hs => Hs.
      move: Heq.
      rewrite -Hs.
      rewrite /step_result /= /step_result /=.
      set us1 := _.[_ <- _].
      set us2 := _.[_ <- _].
      set mh1 := (_ `+` seq_mset _)%mset.
      set mh2 := (_ `+` seq_mset _)%mset.
      move => Heq.
      have Hus: us1 = us2 by move: Heq; move: (us1) (us2) => us3 us4; case.
      have Hus1c: us1.[? s0] = us2.[? s0] by rewrite Hus.
      move: Hus1c.
      rewrite 2!fnd_set -Hs.
      case: ifP; last by move/eqP.
      move => _; case => Hustate.
      have Hmh: mh1 = mh2 by case: Heq.
      clear Heq Hcorrupt0.
      move: key_user Htr0.
      rewrite -Hs -Hustate => key_user.
      rewrite -(eq_getf key_ustate) => Hstep'.
      move: Hmh.
      rewrite /mh1 /mh2.
      move/msetD_seq_mset_perm_eq => Hprm.
      suff Hsuff: l = l0 by rewrite Hsuff.
      move: Hstep Hstep' Hprm.
      exact: utransition_result_perm_eq.
Qed.

(* ----------------------------------------------- *)
(* User transition lemmas - destructing post state *)
(* ----------------------------------------------- *)

(* transition on uid results in msg sent by uid *)
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


(* internal transition does not change preserves corrupt flag *)
Lemma corrupt_preserved_ustep_internal : forall uid upre upost,
    uid # upre ~> upost ->
    upre.(corrupt) -> upost.1.(corrupt).
Proof using.
  by destruct 1.
Qed.

Lemma utransition_internal_preserves_corrupt uid pre post sent:
  uid # pre ~> (post,sent) -> pre.(corrupt) = post.(corrupt).
Proof using.
  set result:=(post,sent). change post with (result.1). clearbody result.
  destruct 1;reflexivity.
Qed.

(* --------------------------------------- *)
(* Definitions and lemmas for user honesty *)
(* --------------------------------------- *)

(* user honest at step (r,p,s) *)
Definition honest_at_step (r p s:nat) uid (path : seq GState) :=
  exists n,
    match onth path n with
    | None => False
    | Some gstate =>
      match gstate.(users).[? uid] with
      | None => False
      | Some ustate => ~ustate.(corrupt)
       /\ (r,p,s) = (step_of_ustate ustate)
      end
    end.

(* user honest at all points <= step in the path *)
Definition honest_during_step (step:nat * nat * nat) uid (path : seq GState) :=
  all (upred' uid (fun u => step_leb (step_of_ustate u) step ==> ~~u.(corrupt))) path.

(* propagate honest_during_step backwards *)
Lemma honest_during_le s1 s2 uid trace:
  step_le s1 s2 ->
  honest_during_step s2 uid trace ->
  honest_during_step s1 uid trace.
Proof using.
  clear.
  move => H_le.
  unfold honest_during_step.
  apply sub_all => g.
  unfold upred'. case: (g.(users).[?uid]) => [u|];[|done].
  move => /implyP H.
  apply /implyP => /step_leP H1.
  apply /H /step_leP /(step_le_trans H1 H_le).
Qed.

(* message transition preserves corrupt flag *)
Lemma utransition_msg_preserves_corrupt uid msg pre post sent:
  uid # pre ; msg ~> (post,sent) -> pre.(corrupt) = post.(corrupt).
Proof using.
  set result:=(post,sent). change post with (result.1). clearbody result.
  destruct 1;try reflexivity.
  + unfold deliver_nonvote_msg_result;simpl.
    destruct msg as [[[[? ?] ?] ?] ?];simpl.
    destruct e;[destruct m|..];reflexivity.
Qed.

(* propagate user_honest backwards through transition *)
Lemma honest_backwards_gstep : forall (g1 g2 : GState),
    GTransition g1 g2 ->
    forall uid, user_honest uid g2 ->
                user_honest uid g1.
Proof using.
  move => g1 g2 Hstep uid.
  destruct Hstep;unfold user_honest;destruct pre;
    unfold tick_update,tick_users;simpl global_state.users in * |- *;try done.
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

(* user honest at last state implies user honest in all states in path *)
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

(* honesty is monotone *)
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

(* propagating honest backwards *)
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

(* -------------------------- *)
(* Lemmas manipulating traces *)
(* -------------------------- *)

(* non-empty prefix of a trace is a trace *)
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

(* dropping elements from a trace still results in a trace *)
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

(* see path_steps: predicate not true initiall and true for some state g_p 
   implies there must have been a step from g1 to g2 where it became true *)
Lemma path_gsteps_onth
      g0 trace (H_path : is_trace g0 trace)
      ix_p g_p (H_g_p : onth trace ix_p = Some g_p):
    forall (P : pred GState),
    ~~ P g0 -> P g_p ->
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

(* -------------------------------- *)
(* Monotonicity/preservation lemmas *)
(* -------------------------------- *)

(* global transition preserves domain of users *)
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
  move => gs1 gs2 H_trans.
  apply gtrans_preserves_users in H_trans.
  move/eqP in H_trans; rewrite eqEfsubset in H_trans; move/andP in H_trans.
  tauto.
Qed.

(* softvotes monotone over internal user transition *)
Lemma softvotes_utransition_internal:
  forall uid pre post msgs, uid # pre ~> (post, msgs) ->
  forall r p, pre.(softvotes) r p \subset post.(softvotes) r p.
Proof using.
  move => uid pre post msgs step r p.
  remember (post,msgs) as result eqn:H_result;
  destruct step;case:H_result => [? ?];subst;done.
Qed.

(* softvotes monotone over user message transition *)
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

(* softvotes monotone over global transition *)
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

(* softvotes monotone between reachable states *)
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

(* weight of softvotes monotone between reachable states *)
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

(* blocks monotone over internal user transition *)
Lemma blocks_utransition_internal:
  forall uid pre post msgs, uid # pre ~> (post, msgs) ->
  forall r, pre.(blocks) r \subset post.(blocks) r.
Proof using.
  move => uid pre post msgs step r.
  remember (post,msgs) as result eqn:H_result;
  destruct step;case:H_result => [? ?];subst;done.
Qed.

(* blocks monotone over user message transition *)
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

(* blocks monotone over global transition *)
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

(* blocks monotone between reachable states *)
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

(* ------------------------------------------ *)
(* Transitions do not decrease step-of-ustate *)
(* ------------------------------------------ *)

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

(* ------------------------------------------------------ *)
(* Lemmas for deducing reachability between global states *)
(* ------------------------------------------------------ *)

(* index of g1 less than index of g2, both in trace implies g2 reachable from g1 *)
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

(* step_in_path_at from pre to post and pre2 to post2 implies pre2 reachable
   from post *)
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

(* ---------------------------------------- *)
(* Lemmas about order of indices in a trace *)
(* ---------------------------------------- *)

(* step of user is smaller in g1 than g2 implies index of g1 < index of g2 *)
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

(* step of msg_step for msg1 smaller than msg2 implies index of msg1 < index of msg2 *)
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
