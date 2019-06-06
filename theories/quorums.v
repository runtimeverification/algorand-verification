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
Require Import algorand_model safety_helpers.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* --------------------------------- *)
(* Quorum definitions and hypotheses *)
(* --------------------------------- *)

(* committee is set of users with sufficiently small credential *)
Definition committee (r p s:nat) : {fset UserId} :=
  [fset uid : UserId | `[<committee_cred (credential uid r p s)>] ].

(* two quorums must contain honest voter in both *)
Definition quorum_honest_overlap_statement tau : Prop :=
  forall trace r p s (quorum1 quorum2 : {fset UserId}),
    quorum1 `<=` committee r p s ->
    #|` quorum1 | >= tau ->
    quorum2 `<=` committee r p s ->
    #|` quorum2 | >= tau ->
    exists honest_voter,
      honest_voter \in quorum1
      /\ honest_voter \in quorum2
      /\ honest_during_step (r,p,s) honest_voter trace.

(* a single quorum must have an honest voter *)
Definition quorum_has_honest_statement tau : Prop :=
  forall trace r p s (quorum : {fset UserId}),
    quorum `<=` committee r p s ->
    #|` quorum | >= tau ->
   exists honest_voter, honest_voter \in quorum /\
     honest_during_step (r,p,s) honest_voter trace.

(* specialize two quorum statement to one quorum *)
Lemma quorum_has_honest_from_overlap_stmt tau:
  quorum_honest_overlap_statement tau ->
  quorum_has_honest_statement tau.
Proof using.
  clear.
  intros H_overlap trace r p s q H_q H_size.
  destruct (H_overlap trace _ _ _ _ _ H_q H_size H_q H_size) as [honest_voter H].
  exists honest_voter;tauto.
Qed.

(* One major purpose of cryptographic self-selection is
   to ensure an adversary cannot predict which users will be part
   of a future committee, so any manipulation targeting a subset
   of users should hit a similar fraction of the users which are
   on and not on a committee (up to reasonable statistical variance).

   For the proofs we need to be able to relate the membership of different
   committees. Intuitively, if a supermajority of one committee satisfies
   some time-independent property (such as having voted a certain way in
   a particular past round) then also a majority of honest users as a
   whole satisfy this property, and then it's overwhelmingly unlikely
   that another committee could contain a supermajority that doesn't
   satisfy the property, because most users do.

   However, this intuitive argument clearly fails for some properties
   like being a member of a specific committee (which is true for
   a supermajority of that committee despite failing for a majority
   of honest users as a whole), so only assume statments for
   particular properties of interest.

   In fact, it seems that for safety we only need to invoke this
   condition with the property being whether a node decided
   to certvote for a value in some step 3. (for honest nodes not
   on a committee the node "decides to certvote" if they receive
   enough softvotes for the value, even though they do not actually
   try to transmit a certvote message unless they are in the
   committee).
 *)
Definition interquorum_property tau1 tau2 (P: UserId -> Prop) trace :=
  forall r1 p1 s1 (quorum1 : {fset UserId}),
    quorum1 `<=` committee r1 p1 s1 ->
    #|` quorum1 | >= tau1 ->
    (forall uid, uid \in quorum1 ->
     honest_during_step (r1,p1,s1) uid trace ->
     P uid) ->
  forall r2 p2 s2 (quorum2 : {fset UserId}),
    quorum2 `<=` committee r2 p2 s2 ->
    #|` quorum2 | >= tau2 ->
    (exists honest_P_uid, honest_P_uid \in quorum2
     /\ P honest_P_uid
     /\ honest_during_step (r2,p2,s2) honest_P_uid trace).

Axiom quorums_s_honest_overlap : quorum_honest_overlap_statement tau_s.
Definition quorum_s_has_honest : quorum_has_honest_statement tau_s
  := quorum_has_honest_from_overlap_stmt quorums_s_honest_overlap.

Axiom quorums_c_honest_overlap : quorum_honest_overlap_statement tau_c.
Definition quorum_c_has_honest : quorum_has_honest_statement tau_c
  := quorum_has_honest_from_overlap_stmt quorums_c_honest_overlap.

Axiom quorums_b_honest_overlap : quorum_honest_overlap_statement tau_b.
Definition quorum_b_has_honest : quorum_has_honest_statement tau_b
  := quorum_has_honest_from_overlap_stmt quorums_b_honest_overlap.

Axiom quorums_v_honest_overlap : quorum_honest_overlap_statement tau_v.
Definition quorum_v_has_honest : quorum_has_honest_statement tau_v
  := quorum_has_honest_from_overlap_stmt quorums_v_honest_overlap.
