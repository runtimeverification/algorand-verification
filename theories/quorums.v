From mathcomp.ssreflect
Require Import all_ssreflect.

From mathcomp.finmap
Require Import finmap multiset.

From Coq
Require Import Reals Relation_Definitions Relation_Operators.

From mathcomp.analysis
Require Import boolp Rstruct.

From Algorand
Require Import R_util fmap_ext algorand_model safety_helpers.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope mset_scope.
Open Scope fmap_scope.
Open Scope fset_scope.

(** * Quorum definitions and axioms *)

(** This module contains core definitions and axioms related
to quorums. *)

(** ** Committees and quorum overlaps *)

(** A committee is a set of users with sufficiently small credentials. *)
Definition committee (r p s:nat) : {fset UserId} :=
  [fset uid : UserId | `[<committee_cred (credential uid r p s)>] ].

(** Any two quorums must both contain an honest voter. *)
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

(** A single quorum must have an honest voter. *)
Definition quorum_has_honest_statement tau : Prop :=
  forall trace r p s (quorum : {fset UserId}),
    quorum `<=` committee r p s ->
    #|` quorum | >= tau ->
   exists honest_voter, honest_voter \in quorum /\
     honest_during_step (r,p,s) honest_voter trace.

(** Specialize two quorum statement to one quorum. *)
Lemma quorum_has_honest_from_overlap_stmt tau:
  quorum_honest_overlap_statement tau ->
  quorum_has_honest_statement tau.
Proof.
  clear.
  intros H_overlap trace r p s q H_q H_size.
  destruct (H_overlap trace _ _ _ _ _ H_q H_size H_q H_size) as [honest_voter H].
  exists honest_voter;tauto.
Qed.

(** One major purpose of cryptographic self-selection is
to ensure an adversary cannot predict which users will be part
of a future committee, so any manipulation targeting a subset
of users should hit a similar fraction of the users which are
on and not on a committee (up to reasonable statistical variance). *)

(** For the proofs we need to be able to relate the membership of different
committees. Intuitively, if a supermajority of one committee satisfies
some time-independent property (such as having voted a certain way in
a particular past round) then also a majority of honest users as a
whole satisfy this property, and then it's overwhelmingly unlikely
that another committee could contain a supermajority that does not
satisfy the property, because most users do. *)

(** However, this intuitive argument clearly fails for some properties
like being a member of a specific committee (which is true for
a supermajority of that committee despite failing for a majority
of honest users as a whole), so only assume statments for
particular properties of interest. *)

(** In fact, it seems that for safety we only need to invoke this
condition with the property being whether a node decided
to certvote for a value in some step 3. For honest nodes not
on a committee the node "decides to certvote" if they receive
enough softvotes for the value, even though they do not actually
try to transmit a certvote message unless they are in the
committee). *)

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

Definition saw_v trace r p v := fun uid =>
  has (fun g =>
         match (g.(users)).[? uid] with
         | None => false
         | Some u =>
           [&& v \in certvals u r p,
               has (fun b => `[< valid_block_and_hash b v>]) (u.(blocks) r) &
               step_leb (step_of_ustate u) (r,p,4)]
         end) trace.

Axiom interquorum_c_v_certinfo:
  forall trace r p v,
    interquorum_property tau_c tau_v (saw_v trace r p v) trace.
Axiom interquorum_c_b_certinfo:
  forall trace r p v,
    interquorum_property tau_c tau_b (saw_v trace r p v) trace.

(** ** Definitions of voting and sufficient votes *)

(** A user has certvoted at a specifix index along a path. *)
Definition certvoted_in_path_at ix path uid r p v : Prop :=
  user_sent_at ix path uid (mkMsg Certvote (val v) r p uid).

(** A user has certvoted along a path. *)
Definition certvoted_in_path path uid r p v : Prop :=
  exists ix, certvoted_in_path_at ix path uid r p v.

(** Value [v] was certified in a given round/period along a path. *)
Definition certified_in_period trace r p v :=
  exists (certvote_quorum:{fset UserId}),
     certvote_quorum `<=` committee r p 3
  /\ #|` certvote_quorum | >= tau_c
  /\ forall (voter:UserId), voter \in certvote_quorum ->
       certvoted_in_path trace voter r p v.

(** A user has softvoted at a specific index along a path. *)
Definition softvoted_in_path_at ix path uid r p v : Prop :=
  exists g1 g2, step_in_path_at g1 g2 ix path
   /\ user_sent uid (mkMsg Softvote (val v) r p uid) g1 g2.

(** A user has softvoted along a path. *)
Definition softvoted_in_path path uid r p v : Prop :=
  exists ix, softvoted_in_path_at ix path uid r p v.

(** Enough softvotes for a value [v] in a given round/period along a path. *)
Definition enough_softvotes_in_period trace r p v :=
  exists (softvote_quorum:{fset UserId}),
     softvote_quorum `<=` committee r p 2
  /\ #|` softvote_quorum | >= tau_s
  /\ forall (voter:UserId), voter \in softvote_quorum ->
       softvoted_in_path trace voter r p v.

(** A user has nextvoted bottom at a specific index along a path. *)
Definition nextvoted_bot_in_path_at ix path uid (r p s:nat) : Prop :=
  exists g1 g2, step_in_path_at g1 g2 ix path
   /\ user_sent uid (mkMsg Nextvote_Open (step_val s) r p uid) g1 g2.

(** A user has nextvoted bottom along a path. *)
Definition nextvoted_bot_in_path path uid r p s : Prop :=
  exists ix, nextvoted_bot_in_path_at ix path uid r p s.

(** Enough nextvotes for bottom in a given round/period along a path. *)
Definition enough_nextvotes_bot_in_step trace r p s :=
  exists (nextvote_quorum:{fset UserId}),
     nextvote_quorum `<=` committee r p s
  /\ #|` nextvote_quorum | >= tau_b
  /\ forall (voter:UserId), voter \in nextvote_quorum ->
       nextvoted_bot_in_path trace voter r p s.

(** A user has nextvoted for a value [v] at a specific index along a path. *)
Definition nextvoted_val_in_path_at ix path uid r p s v : Prop :=
  exists g1 g2, step_in_path_at g1 g2 ix path
   /\ user_sent uid (mkMsg Nextvote_Val (next_val v s) r p uid) g1 g2.

(** A user has nextvoted for a value [v] along a path. *)
Definition nextvoted_val_in_path path uid r p s v : Prop :=
  exists ix, nextvoted_val_in_path_at ix path uid r p s v.

(** Enough nextvotes for a value [v] in a given round/period along a path. *)
Definition enough_nextvotes_val_in_step trace r p s v :=
  exists (nextvote_quorum:{fset UserId}),
     nextvote_quorum `<=` committee r p s
  /\ #|` nextvote_quorum | >= tau_v
  /\ forall (voter:UserId), voter \in nextvote_quorum ->
       nextvoted_val_in_path trace voter r p s v.
