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

Section AlgoSafetyHelpers.

(* -------------- *)
(* Generic lemmas *)
(* -------------- *)  

(* Dropping elements from a path still results in a path *)
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

(* multiset lemmas *)

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


End AlgoSafetyHelpers.
