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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* We assume a finite set of users *)
Parameter UserId : finType.

(* And a finite set of values (blocks and block hashes) *)
Parameter Value : finType.

(* An enumerated data type of all possible types (headers) of messages *)
Inductive MessageType :=
  | Block
  | Proposal
  | Reproposal
  | Softvote
  | Certvote
  | Nextvote_Open
  | Nextvote_Val.

Definition MessageType_eq (a b:MessageType) : bool :=
  nosimpl match a,b with
  | Block, Block => true
  | Proposal, Proposal => true
  | Reproposal, Reproposal => true
  | Softvote, Softvote => true
  | Certvote, Certvote => true
  | Nextvote_Open, Nextvote_Open => true
  | Nextvote_Val, Nextvote_Val => true
  | _, _ => false
  end.

Lemma MessageType_eqP: Equality.axiom MessageType_eq.
Proof using.
  move => a b;apply Bool.iff_reflect;split.
    by move <-;destruct a.
    by move/(ifT (a=b) True) => <-;destruct a, b.
Qed.

(* Make MessageType a finType by showing an isomorphism
   with the ssreflect bounded nat type 'I_7 *)
Definition mtype2o (m:MessageType) : 'I_7 :=
 inord (match m with
  | Block => 0
  | Proposal => 1
  | Reproposal => 2
  | Softvote => 3
  | Certvote => 4
  | Nextvote_Open => 5
  | Nextvote_Val => 6
  end).

Definition o2mtype (i:'I_7) : option MessageType :=
  match val i with
  | 0 => Some Block
  | 1 => Some Proposal
  | 2 => Some Reproposal
  | 3 => Some Softvote
  | 4 => Some Certvote
  | 5 => Some Nextvote_Open
  | 6 => Some Nextvote_Val
  | _ => None
  end.

Lemma pcancel_MessageType_7 : pcancel mtype2o o2mtype.
Proof using. by case;rewrite /o2mtype /= inordK. Qed.

(* Register canonical structures on MessageType; needed for using MessageType in fset, mset, etc. *)
Canonical messageType_eqType     := EqType     MessageType (Equality.Mixin MessageType_eqP).
Canonical messageType_choiceType := ChoiceType MessageType (PcanChoiceMixin pcancel_MessageType_7).
Canonical messageType_countType  := CountType  MessageType (PcanCountMixin  pcancel_MessageType_7).
Canonical messageType_finType    := FinType    MessageType (PcanFinMixin    pcancel_MessageType_7).

(* Message payload type, packaging Value and other data *)
Inductive ExValue :=
  | val      : Value -> ExValue
  | step_val : nat -> ExValue
  | repr_val : Value -> UserId -> nat -> ExValue
  | next_val : Value -> nat -> ExValue.

(* Make ExValue an eqType and a choiceType *)
Definition codeExVal (e:ExValue) :
  Value + nat + (Value * UserId * nat) + (Value * nat) :=
  match e with
  | val mv => inl (inl (inl mv))
  | step_val k => inl (inl (inr k))
  | repr_val v user n => inl (inr (v, user, n))
  | next_val v n => inr (v,n)
  end.

Definition decodeExVal (c:Value + nat + (Value * UserId * nat) + (Value * nat)) : ExValue :=
  match c with
  | inl (inl (inl mv)) => val mv
  | inl (inl (inr k)) => step_val k
  | inl (inr (v, user, n)) => repr_val v user n
  | inr (v,n) => next_val v n
  end.

Lemma cancelExVal : pcancel codeExVal (fun x => Some (decodeExVal x)).
Proof using. case;reflexivity. Qed.

(* Register canonical structures on ExValue; needed for using ExValue in fset, mset, etc. *)
Canonical exValue_eqType     := EqType     ExValue (PcanEqMixin     cancelExVal).
Canonical exValue_choiceType := ChoiceType ExValue (PcanChoiceMixin cancelExVal).
Canonical exValue_countType  := CountType  ExValue (PcanCountMixin  cancelExVal).

(* A message type as a product type *)
(* A message is a tuple (type, ev, r, p, id) where:
    type: message type as an MessageType
    ev  : message payload as an ExValue
    r   : round value
    p   : period value
    id  : sender's user id
 *)
Definition Msg : Type := MessageType * ExValue * nat * nat * UserId.
Definition msg_sender (m:Msg): UserId := m.2.
Definition msg_round (m:Msg): nat := m.1.1.2.
Definition msg_period (m:Msg): nat := m.1.2.

(* Messages are grouped by the target user.
   Messages are paired with a delivery deadline.
   In the absence of a partition, messages must be
   delivered before the deadline is reached.
 *)
Definition MsgPool := {fmap UserId -> {mset R * Msg}}%mset.

(* The credential of a User at a round-period-step triple
   Note: We abstract away the random value produced by an Oracle
   and the fact that credentials are interpreted as integer
   values. Instead, we model the type of credentials as an
   abstract totally ordered type.
 *)
Parameter credType : orderType tt.

(* A credential is constructed using the user's id and the
   current round-period-step values
 *)
Parameter credential : UserId -> nat -> nat -> nat -> credType.

(* Credentials of two differnet users must be different *)
Axiom credentials_different :
  forall (u u' : UserId) (r r' : nat) (p p' : nat) (s s' : nat),
  u <> u' -> credential u r p s <> credential u' r' p' s'.

(* A proposal/reproposal record is a quadruple consisting of
   a user id, a user's credential, a value and a boolean
   indicating whether the record represents a proposal (true)
   or a reproposal (false)
 *)
Definition PropRecord := (UserId * credType * Value * bool)%type.

(* A vote is a pair of UserId (the id of the voter) and Value
   (the value voted for)
 *)
Definition Vote := (UserId * Value)%type.

(* The user's state structure *)
(* Note that the user state structure and supporting functions and notations
   are all defined in local_state.v
 *)
Definition UState := local_state.UState UserId Value PropRecord Vote.

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

(* Update functions for lists maintained in the user state *)
Definition set_proposals u r' p' prop : UState :=
 {[ u with proposals := fun r p => if (r, p) == (r', p')
                                 then undup (prop :: u.(proposals) r p)
                                 else u.(proposals) r p ]}.

Definition set_blocks (u : UState) r' block : UState :=
 {[ u with blocks := fun r => if r == r'
                                 then undup (block :: u.(blocks) r)
                                 else u.(blocks) r]}.

Definition set_softvotes (u : UState) r' p' sv : UState :=
  {[ u with softvotes := fun r p => if (r, p) == (r', p')
                                 then undup (sv :: u.(softvotes) r p)
                                 else u.(softvotes) r p ]}.

Definition set_certvotes (u : UState) r' p' sv : UState :=
  {[ u with certvotes := fun r p => if (r, p) == (r', p')
                                 then undup (sv :: u.(certvotes) r p)
                                 else u.(certvotes) r p ]}.

Definition set_nextvotes_open (u : UState) r' p' s' nvo : UState :=
  {[ u with nextvotes_open := fun r p s => if (r, p, s) == (r', p', s')
                                   then undup (nvo :: u.(nextvotes_open) r p s)
                                   else u.(nextvotes_open) r p s ]}.

Definition set_nextvotes_val (u : UState) r' p' s' nvv : UState :=
  {[ u with nextvotes_val := fun r p s => if (r, p, s) == (r', p', s')
                                   then undup (nvv :: u.(nextvotes_val) r p s)
                                   else u.(nextvotes_val) r p s ]}.

(* Update function for advancing the period of a user state *)
Definition advance_period (u : UState) : UState :=
  {[ {[ {[ {[ {[ u with period := u.(period) + 1 ]}
                with step := 1 ]}
             with timer := 0%R ]}
          with deadline := 0%R ]}
       with p_start := u.(p_start) + u.(timer) ]}.

(* Update function for advancing the round of a user state *)
Definition advance_round (u : UState) : UState :=
  {[ {[ {[ {[ {[ {[ {[ u with round := u.(round) + 1 ]}
                      with period := 1 ]}
                   with step := 1 ]}
                with stv := fun x => None ]}
             with timer := 0%R ]}
           with deadline := 0%R ]}
        with p_start := u.(p_start) + u.(timer) ]}.

(* A proposition for whether a given credential qualifies its
   owner to be a committee member
   Note: This abstracts away how credential values are
   interpreted
 *)
Parameter committee_cred : credType -> Prop.

(* Whether the credential is a committee credential for the given
   round-period-step
 *)
Definition comm_cred_step uid r p s : Prop :=
  committee_cred (credential uid r p s) .

Axiom credentials_valid_period:
  forall uid r p s, comm_cred_step uid r p s -> 1 <= p.

(* The global state *)
(* Note that the global state structure and supporting functions and notations
   are all defined in global_state.v
 *)
Definition GState := global_state.GState UserId UState [choiceType of Msg].

Notation now               := (global_state.now UserId UState [choiceType of Msg]).
Notation network_partition := (global_state.network_partition UserId UState [choiceType of Msg]).
Notation users             := (global_state.users UserId UState [choiceType of Msg]).
Notation msg_in_transit    := (global_state.msg_in_transit UserId UState [choiceType of Msg]).
Notation msg_history       := (global_state.msg_history UserId UState [choiceType of Msg]).

(* State with empty maps, unpartitioned, at global time 0 *)
Definition null_state : GState := mkGState _ _ _ 0%R false [fmap] [fmap] mset0.

(* Equality of global states *)

Definition eqGState (g1 g2 : GState) : bool :=
  if pselect (g1 = g2) then true else false.

Lemma eqGStateP : Equality.axiom eqGState.
Proof.
by move => g1 g2; rewrite /eqGState; case: pselect => //= ?; apply/(iffP idP).
Qed.

Canonical GState_eqMixin := EqMixin eqGStateP.
Canonical GState_eqType := Eval hnf in EqType GState GState_eqMixin.

(* Flip the network_partition flag *)
Definition flip_partition_flag (g : GState) : GState :=
  {[ g with network_partition := ~~ g.(network_partition) ]}.

(* small - non-block - message delivery delay *)
Parameter lambda : R.

(* block message delivery delay *)
Parameter big_lambda : R.

(* recovery time period L *)
Parameter L : R.

(* assumptions on how these bounds relate *)
Axiom delays_positive : (lambda > 0)%R .
Axiom delays_order : (3 * lambda <= big_lambda < L)%R .

(* some other thresholds *)
(* number of soft-votes needed to cert-vote *)
Parameter tau_s : nat.

(* number of cert-votes needed for a certificate *)
Parameter tau_c : nat.

(* number of next-votes for bottom to move to next period *)
Parameter tau_b : nat.

(* number of next-votes for a value to move to next period *)
Parameter tau_v : nat.


(** Helper functions/propositions for the user-state-level trnasitions **)

(* valid is an abstract proposition on values that tells us whether a value
   is valid *)
Parameter valid : Value -> Prop.

(* correct_hash is an abstract proposition on values that tells us whether a
   given hash value is indeed the hash of the given block value *)
Parameter correct_hash : Value -> Value -> Prop.

(* The block has been seen and is valid and the given value is indeed its hash
   value *)
Definition valid_block_and_hash b v : Prop :=
  valid b /\ correct_hash v b.

(* Step of ustate is triple of (round,period,step) *)
Definition step_of_ustate (u:UState) :=
  (u.(round), u.(period), u.(step)).

(* Steps are ordered lexicographically (Prop versions) *)
Definition step_le (step1 step2: nat * nat * nat) :=
  let: (r1,p1,s1) := step1 in
  let: (r2,p2,s2) := step2 in
  r1 < r2 \/ r1 = r2 /\ (p1 < p2 \/ p1 = p2 /\ s1 <= s2).
Definition step_lt (step1 step2: nat * nat * nat) :=
  let: (r1,p1,s1) := step1 in
  let: (r2,p2,s2) := step2 in
  r1 < r2 \/ r1 = r2 /\ (p1 < p2 \/ p1 = p2 /\ s1 < s2).

(* Steps are ordered lexicographically (bool versions) *)
Definition step_leb (step1 step2: nat * nat * nat) : bool :=
  let: (r1,p1,s1) := step1 in
  let: (r2,p2,s2) := step2 in
  (r1 < r2) || (r1 == r2) && ((p1 < p2) || (p1 == p2) && (s1 <= s2)).
Definition step_ltb (step1 step2: nat * nat * nat) : bool :=
  let: (r1,p1,s1) := step1 in
  let: (r2,p2,s2) := step2 in
  (r1 < r2) || (r1 == r2) && ((p1 < p2) || (p1 == p2) && (s1 < s2)).

(* us2 is after us1 if the step of us1 is less than the step of us2 *)
Definition ustate_after_strict us1 us2 : Prop :=
  step_lt (step_of_ustate us1) (step_of_ustate us2).

(* State us2 is no earlier than state us1 in terms of round-period-step ordering *)
Definition ustate_after us1 us2 : Prop :=
  us1.(round) < us2.(round)
  \/ (us1.(round) = us2.(round) /\ us1.(period) < us2.(period))
  \/ (us1.(round) = us2.(round) /\ us1.(period) = us2.(period) /\ us1.(step) <= us2.(step)).

Definition msg_step_s (mhead: (MessageType * ExValue)): nat :=
  let (mtype,v) := mhead in
  match mtype with
  | Block => 1
  | Proposal => 1
  | Reproposal => 1
  | Softvote => 2
  | Certvote => 3
  | Nextvote_Val =>
    match v with
    | next_val _ s => s
    | _ => 111
    end
  | Nextvote_Open =>
    match v with
    | step_val s => s
    | _ => 111
    end
  end.

Definition msg_step (msg:Msg) : nat * nat * nat :=
  (msg_round msg,msg_period msg,msg_step_s msg.1.1.1).

(* Is the given message a vote (softvote, certvote or nextvote) message? *)
Definition vote_msg (msg : Msg) : Prop :=
  match msg.1.1.1.1 with
  | Softvote | Certvote | Nextvote_Open | Nextvote_Val => True
  | _ => False
  end.

(* Does the given round/period/step match the ones stored in the user state? *)
Definition valid_rps (u : UState) r p s : Prop :=
  u.(round) = r /\ u.(period) = p /\ u.(step) = s .

Definition advancing_rp (u : UState) r p : Prop :=
  u.(round) < r \/ u.(round) = r /\ u.(period) <= p.

(* Is the vote x for this value v? *)
Definition matchValue (x : Vote) (v : Value) : bool :=
  let: (u', v') := x in v == v' .

(* The sequence of all values appearing in a given sequence of votes with
   duplicates removed *)
Definition vote_values (vs: seq Vote) : seq Value :=
  undup [seq x.2 | x <- vs] .

Definition softvoters_for (v:Value) (u:UState) r p : {fset UserId} :=
  [fset x.1 | x in u.(softvotes) r p & matchValue x v].

Definition nextvoters_open_for (u:UState) r p s : {fset UserId} :=
  [fset x in u.(nextvotes_open) r p s].

Definition nextvoters_val_for (v:Value) (u:UState) r p s : {fset UserId} :=
  [fset x.1 | x in u.(nextvotes_val) r p s & matchValue x v].

(* The number of softvotes of a given value in a given user state for the round
   and period given (does not use the invariant that u.(softvotes) r p is duplicate-free) *)
Definition soft_weight (v:Value) (u:UState) r p : nat :=
  size (softvoters_for v u r p).
    (*[seq x <- undup (u.(softvotes) r p) | matchValue x v] . *)

(* The sequence of values with high enough softvotes in a given user state for given round and period *)
(* i.e. the sequence of values in softvotes having votes greater than or equal to the threshold *)
Definition certvals (u:UState) r p : seq Value :=
  [seq v <- vote_values (u.(softvotes) r p) | (soft_weight v u r p) >= tau_s] .
(* invariant: size should be <= 1 *)

(* The sequence of values certified for in the last period as seen by the given user *)
(* This corresponds to prev_certvals field in the automaton model *)
Definition prev_certvals (u:UState) : seq Value :=
  let p := u.(period) in
    if p > 1 then certvals u u.(round) (p - 1) else [::] .

(* Whether the user has seen enough votes for bottom in the given round/period/step *)
Definition nextvote_bottom_quorum (u:UState) r p s : Prop :=
  #|(u.(nextvotes_open) r p s)| >= tau_b.

(* Whether the user has seen enough nextvotes for a given value in the given round/period/step *)
Definition nextvote_value_quorum (u:UState) v r p s : Prop :=
  #|[seq x.1 | x <- u.(nextvotes_val) r p s & matchValue x v]| >= tau_v.

(* Whether the user has seen enough nextvotes for some value in the given round/period/step *)
Definition nextvote_quorum_for_some_value (u:UState) r p s : Prop :=
  exists v, nextvote_value_quorum u v r p s.

(* Whether a quorum for bottom was not seen in the last period
   of the current round (for some step during that period) *)
Definition cert_may_exist (u:UState) : Prop :=
  let p := u.(period) in
  let r := u.(round) in
  p > 1 /\ forall s, ~ nextvote_bottom_quorum u r (p - 1) s.

(* Proposal record ordering induced by ordering on credentials *)
Definition reclt (rec rec' : PropRecord) : bool := (rec.1.1.2 < rec'.1.1.2)%O.

(* Returns the proposal record in a given sequence of records having the least
   credential, i.e. the record of the potential leader
 *)
Fixpoint least_record (prs : seq PropRecord) : option PropRecord :=
  match prs with
  | [::]            => None
  | [:: rec & prs'] =>
  	  match least_record prs' with
  	  | None      => Some rec
  	  | Some rec' =>
      if reclt rec' rec
      then Some rec'
      else Some rec
    	end
  end.

(* Returns whether the given (proposal) value is the potential leader value *)
Definition leader_prop_value (v : Value) (prs : seq PropRecord) : Prop :=
  let opr := least_record prs in
  match opr with
  | None => False
  | Some (_,_, _, false) => False
  | Some (_,_, v', true) => v = v'
  end.

(* Returns whether the given (reproposal) value is the potential leader value *)
Definition leader_reprop_value (v : Value) (prs : seq PropRecord) : Prop :=
  let opr := least_record prs in
  match opr with
  | None => False
  | Some (_,_, _, true) => False
  | Some (_,_, v', false) => v = v'
  end.

(* The timer deadline value for the NEXT step following the given step value *)
(* Note: k is zero-based and hence the apparent difference from the algorand paper.
         The computed deadline values are exactly as given in the paper. *)
Definition next_deadline k : R :=
  match k with
  (* deadline for step 1 *)
  | 0 => 0
  (* deadline for step 2 *)
  | 1 => (2 * lambda)%R
  (* deadline for step 3 *)
  | 2 => (lambda + big_lambda)%R
  (* deadlines for steps 4, 5, 6, ... *)
  | n => (lambda + big_lambda + (INR n - 3) * L)%R
  end.


(** Step 1: Proposing propositions and user state update **)

(* The proposal step preconditions *)
(* Note that this covers both: (a) the case when p = 1, and (b)
   the case when p > 1 with the previous period voting for bottom.
   Just as in the automaton model, the fact that the last period's quorum
   was not for bottom is captured by the predicate cert_may_exist *)
Definition propose_ok (pre : UState) uid v b r p : Prop :=
  pre.(timer) = 0%R /\
  valid_rps pre r p 1 /\
  comm_cred_step uid r p 1 /\
  valid_block_and_hash b v /\
  ~ cert_may_exist pre.

(* The reproposal step preconditions *)
(* Note that this is the proposal step when p > 1 and a next-vote
   quorum for a value v was seen in p-1
   Note also that this may overlap with the case above, when cert_may_exist
   does not hold *)
Definition repropose_ok (pre : UState) uid v r p : Prop :=
  pre.(timer) = 0%R /\
  valid_rps pre r p 1 /\ p > 1 /\
  comm_cred_step uid r p 1 /\
  exists s, nextvote_value_quorum pre v r (p - 1) s.

(* The no-propose step preconditions *)
(* Note that this applies regardless of whether p = 1 *)
Definition no_propose_ok (pre : UState) uid r p : Prop :=
  pre.(timer) = 0%R /\
  valid_rps pre r p 1 /\
  (comm_cred_step uid r p 1 ->
    cert_may_exist pre /\
    forall s v, ~ nextvote_value_quorum pre v r (p - 1) s).

(* The proposing step (propose, repropose and nopropose) post-state *)
(* Move on to Softvoting and set the new deadline to 2*lambda *)
Definition propose_result (pre : UState) : UState :=
  {[ {[ pre with deadline := (2 * lambda)%R ]}
            with step := 2 ]}.

(** Step 2: Softvoting propositions and user state update **)

(* The Softvoting-a-proposal step preconditions *)
(* Note that this covers both: (a) the case when p = 1, and (b)
   the case when p > 1 with the previous period voting for bottom. *)
(* Notes: - the automaton model has the constraint clock >= 2*lambda
          - The phrase "v is a period 1 block" in the Algorand2 description
            is interpreted here as "v is a reproposal" for simplicity *)
Definition softvote_new_ok (pre : UState) uid v r p : Prop :=
  pre.(timer) = (2 * lambda)%R /\
  valid_rps pre r p 2 /\
  comm_cred_step uid r p 2 /\
  ~ cert_may_exist pre /\
  leader_prop_value v (pre.(proposals) r p) .

(* The Softvoting-a-reproposal step preconditions *)
(* Note that this is the Softvoting step when p > 1 and the previous-
   period's winning vote was for a value v *)
Definition softvote_repr_ok (pre : UState) uid v r p : Prop :=
  pre.(timer) = (2 * lambda)%R /\
  valid_rps pre r p 2 /\ p > 1 /\
  comm_cred_step uid r p 2 /\
  ( (~ cert_may_exist pre /\
    (exists s, nextvote_value_quorum pre v r (p - 1) s) /\
    leader_reprop_value v (pre.(proposals) r p))
    \/
    (cert_may_exist pre /\ pre.(stv) p = Some v) ).

(* The no-softvoting step preconditions *)
(* Three reasons a user may not be able to soft-vote:
   - Not being in the soft-voting committee, or
   - Not being able to identify a potential leader value to soft-vote for
   - Not seeing enough next-votes for a value reproposed when the previous period
     had a quorum for bottom
 *)
(* Note that this may apply regardless of whether p = 1*)
Definition no_softvote_ok (pre : UState) uid r p : Prop :=
  pre.(timer) = (2 * lambda)%R /\
  valid_rps pre r p 2 /\
  forall v,
  (comm_cred_step uid r p 2 ->
    (( cert_may_exist pre \/ ~ leader_prop_value v (pre.(proposals) r p))
    /\ ((cert_may_exist pre \/
        (forall s, ~ nextvote_value_quorum pre v r (p - 1) s) \/
        ~ leader_reprop_value v (pre.(proposals) r p))
       /\ (~ cert_may_exist pre \/ ~ pre.(stv) p = Some v)))).

(* The softvoting step (new or reproposal) post-state *)
(* NOTE: We keep the current deadline at 2 * lambda and let certvoting handle
         updating the deadline (to avoid timing out while certvoting is already
         enabled) *)
(* NOTE: This assumes it is ok to certvote at time 2 * lambda *)
Definition softvote_result (pre : UState) : UState :=
  {[ {[ pre with step := 3 ]}
            with deadline := (lambda + big_lambda)%R ]}.


(** Step 3: Certvoting propositions and user state update **)

(* Certvoting step preconditions *)
(* The successful case *)
Definition certvote_ok (pre : UState) uid (v b: Value) r p : Prop :=
  ((2 * lambda)%R < pre.(timer) <= lambda + big_lambda)%R /\
  valid_rps pre r p 3 /\
  comm_cred_step uid r p 3 /\
  valid_block_and_hash b v /\
  b \in pre.(blocks) r /\
  v \in certvals pre r p .

(* Certvoting step preconditions *)
(* The unsuccessful case -- not a committee member *)
Definition no_certvote_ok (pre : UState) uid r p : Prop :=
  ((2 * lambda)%R < pre.(timer) <= lambda + big_lambda)%R /\
  valid_rps pre r p 3 /\
  ~ comm_cred_step uid r p 3.

(* Certvote timeout preconditions *)
(* A user timeouts if the deadline is reached while waiting for some external messages
   (i.e. while observing softvotes in step 3) *)
Definition certvote_timeout_ok (pre : UState) uid r p : Prop :=
  (pre.(timer) >= pre.(deadline))%R /\
  valid_rps pre r p 3 /\
  comm_cred_step uid r p 3 /\
  forall b v,
  (~ valid_block_and_hash b v \/
   ~ b \in pre.(blocks) r \/
   ~ v \in certvals pre r p).

(* Certvoting step's resulting user state *)
(* The state update for all certvoting cases: move on to the next step
   (the deadline does not need updating) *)
Definition certvote_result (pre : UState) : UState :=
  {[ pre with step := 4 ]}.

(** Steps >= 4: Nextvoting propositions and user state update **)

(* Nextvoting step preconditions *)
(* The proper-value case *)
(* Notes: - Corresponds (roughly) to transition nextvote_val in the automaton
            model (but not the same) *)
(*        - Corresponds more closely to the Algorand2 description (but with the
            committee membership constraint)
 *)
Definition nextvote_val_ok (pre : UState) uid (v b : Value) r p s : Prop :=
  pre.(timer) = (lambda + big_lambda + (INR s - 4) * L)%R /\
  valid_rps pre r p s /\
  comm_cred_step uid r p s /\
  3 < s /\
  valid_block_and_hash b v /\
  b \in pre.(blocks) r /\
  v \in certvals pre r p.

(* Nextvoting step preconditions *)
(* The bottom-value case *)
(* Notes: - Corresponds (roughly) to transition nextvote_open in the automaton
            model (but not the same) *)
(*        - Corresponds more closely to the Algorand2 description (but with the
            committee membership constraint)
 *)
Definition nextvote_open_ok (pre : UState) uid r p s : Prop :=
  pre.(timer) = (lambda + big_lambda + (INR s - 4) * L)%R /\
  valid_rps pre r p s /\
  comm_cred_step uid r p s /\
  3 < s /\
  (forall v, v \in certvals pre r p -> forall b, b \in pre.(blocks) r ->
     ~valid_block_and_hash b v) /\
  (p > 1 -> nextvote_bottom_quorum pre r (p - 1) s ).

(* Nextvoting step preconditions *)
(* The aditional special case of using the starting value *)
(* Notes: - Not sure if this is captured in the automaton model *)
(*        - Corresponds more closely to the Algorand2 description (but with
            additional constraints given explicitly)
 *)
Definition nextvote_stv_ok (pre : UState) uid r p s : Prop :=
  pre.(timer) = (lambda + big_lambda + (INR s - 4) * L)%R /\
  valid_rps pre r p s /\
  comm_cred_step uid r p s /\
  3 < s /\
  (forall v, v \in certvals pre r p -> forall b, b \in pre.(blocks) r ->
     ~valid_block_and_hash b v) /\
  p > 1 /\ ~ nextvote_bottom_quorum pre r (p - 1) s.

(* Nextvoting step preconditions *)
(* The no-voting case *)
Definition no_nextvote_ok (pre : UState) uid r p s : Prop :=
  pre.(timer) = (lambda + big_lambda + (INR s - 4) * L)%R /\
  valid_rps pre r p s /\
  ~ comm_cred_step uid r p s.

(* Nextvoting step state update for steps s >= 4 (all cases) *)
Definition nextvote_result (pre : UState) s : UState :=
  {[ {[ pre with step := (s + 1) ]}
            with deadline := next_deadline s ]}.

(** Advancing period propositions and user state update **)

(* Preconditions -- The bottom-value case *)
(* Notes: - Corresponds to transition advance_period_open in the automaton model *)
Definition adv_period_open_ok (pre : UState) r p s : Prop :=
  valid_rps pre r p s /\
  nextvote_bottom_quorum pre r p s.

(* Preconditions -- The proper value case *)
(* Notes: - Corresponds to transition advance_period_val in the automaton model *)
Definition adv_period_val_ok (pre : UState) (v : Value) r p s : Prop :=
  valid_rps pre r p s /\
  nextvote_value_quorum pre v r p s.

(* State update -- The bottom-value case *)
Definition adv_period_open_result (pre : UState) : UState :=
  let prev_p := pre.(period) in
   {[ (advance_period pre)
      with stv := fun p => if p == prev_p.+1 then None else (pre.(stv) p) ]}.

(* State update -- The proper value case *)
Definition adv_period_val_result (pre : UState) v : UState :=
  let prev_p := pre.(period) in
   {[ (advance_period pre)
      with stv := fun p => if p == prev_p.+1 then Some v else (pre.(stv) p) ]}.

(** Advancing round propositions and user state update **)
(* Preconditions *)
(* Notes: - Corresponds to transition certify in the automaton model
          - The requirement valid_rps has been removed since certification
            may happen at any time *)
(* TODO - must have some assertion about message age *)
Definition certify_ok (pre : UState) (v : Value) r p : Prop :=
  advancing_rp pre r p /\
  exists b,
  valid_block_and_hash b v /\
  b \in pre.(blocks) r /\
  #|[seq x <- pre.(certvotes) r p | matchValue x v]| >= tau_c .

(* State update *)
Definition certify_result r (pre : UState) : UState := advance_round {[pre with round := r]}.

(* The post state of delivering a non-vote message *)
Definition deliver_nonvote_msg_result (pre : UState) (msg : Msg) c r p : UState :=
  let type := msg.1.1.1.1 in
  let id := msg.2 in
  let ev := msg.1.1.1.2 in
  match ev with
  | val v =>
    match type with
    | Proposal => set_proposals pre r p (id, c, v, true)
    | Reproposal => set_proposals pre r p (id, c, v, false)
    | Block => set_blocks pre r v
    | _ => pre
    end
  | _ => pre
  end.


(** The inductive definition of the user state transition relations **)

(* The internal user-level transition relation type *)
(* An internal transition is a transition that does not consume a message *)
(* A user transitions from a pre-state into a post-state while emitting
   a (possibly empty) sequence of outgoing messages *)
Definition u_transition_internal_type := UserId -> UState -> (UState * seq Msg) -> Prop.

Reserved Notation "x # z ~> y" (at level 70).

(* Internal actions are supposed to take place either:
	  - at a specific time instance (i.e. never triggered by a recevied message)
	  - during a time duration, but the preconditions are already satisfied that
	  	the action fires eagerly at the beginning of that time duration (again,
	  	without consuming a message)
 *)
Inductive UTransitionInternal : u_transition_internal_type :=

  (* Step 1: Block Proposal *)
  | propose : forall uid (pre : UState) v b r p,
      propose_ok pre uid v b r p ->
      uid # pre ~> (propose_result pre, [:: (Proposal, val v, r, p, uid) ; (Block, val b, r, p, uid)])

  (* Step 1: Block Proposal [Reproposal] *)
  | repropose : forall uid (pre : UState) v r p,
      repropose_ok pre uid v r p ->
      uid # pre ~> (propose_result pre, [:: (Reproposal, repr_val v uid p, r, p, uid)])

  (* Step 1: Block Proposal [failure] *)
  | no_propose : forall uid (pre : UState) r p,
      no_propose_ok pre uid r p ->
      uid # pre ~> (propose_result pre, [::])

  (* Step 2: Filtering Step [new value] *)
  | softvote_new : forall uid (pre : UState) v r p,
      softvote_new_ok pre uid v r p ->
      uid # pre ~> (softvote_result pre, [:: (Softvote, val v, r, p, uid)])

  (* Step 2: Filtering Step [old value] *)
  | softvote_repr : forall uid (pre : UState) v r p,
      softvote_repr_ok pre uid v r p ->
      uid # pre ~> (softvote_result pre, [:: (Softvote, val v, r, p, uid)])

  (* Step 2: Filtering Step [no value] *)
  | no_softvote : forall uid (pre : UState) r p,
      no_softvote_ok pre uid r p ->
      uid # pre ~> (softvote_result pre, [::])

  (* Step 3: Certifying Step [success] *)
  | certvote1 : forall uid (pre : UState) v b r p,
      certvote_ok pre uid v b r p ->
      uid # pre ~> (certvote_result pre, [:: (Certvote, val v, r, p, uid)])

  (* Step 3: Certifying Step [failure] *)
  | no_certvote : forall uid (pre : UState) r p,
      no_certvote_ok pre uid r p ->
      uid # pre ~> (certvote_result pre, [::])

  (* Steps >= 4: Finishing Step - i has cert-voted some v *)
  | nextvote_val : forall uid (pre : UState) v b r p s,
      nextvote_val_ok pre uid v b r p s ->
      uid # pre ~> (nextvote_result pre s, [:: (Nextvote_Val, next_val v s, r, p, uid)])

  (* Steps >= 4: Finishing Step - i has not cert-voted some v *)
  | nextvote_open : forall uid (pre : UState) r p s,
      nextvote_open_ok pre uid r p s ->
      uid # pre ~> (nextvote_result pre s, [:: (Nextvote_Open, step_val s, r, p, uid)])

  (* Steps >= 4: Finishing Step - special case of using stv *)
  | nextvote_stv : forall uid (pre : UState) v r p s,
      nextvote_stv_ok pre uid r p s /\ pre.(stv) p = Some v ->
        uid # pre ~> (nextvote_result pre s, [:: (Nextvote_Val, next_val  v s, r, p, uid)])

  (* Steps >= 4: Finishing Step - no next-voting *)
  | no_nextvote : forall uid (pre : UState) r p s,
      no_nextvote_ok pre uid r p s ->
      uid # pre ~> (nextvote_result pre s, [::])

  (* Certvote timeout transition -- Applicable only to step = 3 (after the 27March change) *)
  | certvote_timeout : forall uid (pre : UState) r p,
      certvote_timeout_ok pre uid p r ->
      uid # pre ~> (certvote_result pre, [::])

where "x # y ~> z" := (UTransitionInternal x y z) : type_scope.

(* The message-triggered user-level transition relation type *)
(* A message-triggered transition consumes an incoming message *)
(* A user transitions from a pre-state, while consuming a message, into a
   post-state and emits a (possibly empty) sequence of outgoing messages *)
Definition u_transition_msg_type := UserId -> UState -> Msg -> (UState * seq Msg) -> Prop.

Reserved Notation "a # b ; c ~> d" (at level 70).

(** Deliver messages and possibly trigger actions urgently **)
Inductive UTransitionMsg : u_transition_msg_type :=
  (* Deliver a softvote while not triggering any internal action *)
  | deliver_softvote : forall uid (pre : UState) r p i v b,
      let pre' := (set_softvotes pre r p (i, v)) in
        ~ certvote_ok pre' uid v b r p ->
        uid # pre ; (Softvote, val v, r, p, i) ~> (pre', [::])

  (* Deliver a softvote and cert-vote for the value [committee member case] *)
  | deliver_softvote_certvote1 : forall uid (pre : UState) r p i v b,
      let pre' := set_softvotes pre r p (i, v) in
        certvote_ok pre' uid v b r p ->
        uid # pre ; (Softvote, val v, r, p, i) ~> (certvote_result pre', [:: (Certvote, val v, r, p, uid)])

  (* Deliver a nextvote for bottom while not triggering any internal action *)
  | deliver_nextvote_open : forall uid (pre : UState) r p s i,
      let pre' := set_nextvotes_open pre r p s i in
      (* ~ nextvote_open_ok pre' v r p s -> *)
      ~ adv_period_open_ok pre' r p s ->
      uid # pre ; (Nextvote_Open, step_val s, r, p, i) ~> (pre', [::])

  (* Deliver a nextvote for bottom and advance the period *)
  (* Note: Advancing the period takes precedence over nextvote2_open actions *)
  | deliver_nextvote_open_adv_prd : forall uid (pre : UState) r p s i,
      let pre' := set_nextvotes_open pre r p s i in
        adv_period_open_ok pre' r p s ->
        uid # pre ; (Nextvote_Open, step_val s, r, p, i) ~> (adv_period_open_result pre', [::])

  (* Deliver a nextvote for value while not triggering any internal action *)
  | deliver_nextvote_val : forall uid (pre : UState) r p s i v,
      let pre' := set_nextvotes_val pre r p s (i, v) in
        ~ adv_period_val_ok pre' v r p s ->
        uid # pre ; (Nextvote_Val, next_val v s, r, p, i) ~> (pre', [::])

  (* Deliver a nextvote for value and advance the period *)
  | deliver_nextvote_val_adv_prd : forall uid (pre : UState) r p s i v,
      let pre' := set_nextvotes_val pre r p s (i, v) in
      adv_period_val_ok pre' v r p s ->
      uid # pre ; (Nextvote_Val, next_val v s, r, p, i) ~> (adv_period_val_result pre' v, [::])

  (* Deliver a certvote while not triggering any internal action *)
  | deliver_certvote : forall uid (pre : UState) v r p i,
      let pre' := set_certvotes pre r p (i, v) in
      ~ certify_ok pre' v r p ->
      uid # pre ; (Certvote, val v, r, p, i) ~> (pre', [::])

  (* Deliver a certvote for value and advance the round *)
  | deliver_certvote_adv_rnd : forall uid (pre : UState) v r p i,
      let pre' := set_certvotes pre r p (i, v) in
        certify_ok pre' v r p ->
        uid # pre ; (Certvote, val v, r, p, i) ~> (certify_result r pre', [::])
        (* Note: Some algorand documents say this transition may try to
           send anothe Certvote message from this node, but we have been
           informed that the implementation does not do this,
           and allowing it would complicated proofs.
           Further explanation in assumptions.md
         *)
  (* Deliver a message other than vote messages (i.e. Block, Proposal or Reproposal) *)
  | deliver_nonvote_msg : forall uid (pre : UState) msg c r p,
      ~ vote_msg msg ->
      uid # pre ; msg ~> (deliver_nonvote_msg_result pre msg c r p, [::])
where "a # b ; c ~> d" := (UTransitionMsg a b c d) : type_scope.

(* Global transition relation type *)
Definition g_transition_type := relation GState.

(* Is the network in a partitioned/unpartitioned state? *)
Definition is_partitioned pre : bool := pre.(network_partition).
Definition is_unpartitioned pre : bool := ~~ is_partitioned pre.

(* It's ok to advance time if:
   - the user is corrupt (its deadline is irrelevant), or
   - the increment does not go beyond the deadline *)
Definition user_can_advance_timer (increment : posreal) : pred UState :=
  fun u => u.(corrupt) || Rleb (u.(timer) + pos increment) u.(deadline).

(* Advance the timer of an honest user (timers of corrupt users are irrelevant) *)
Definition user_advance_timer (increment : posreal) (u : UState) : UState :=
  if ~~ u.(corrupt)
    then {[ u with timer := (u.(timer) + pos increment)%R ]}
    else u.

(* Is it ok to advance timers of all (honest) users by the given increment? *)
Definition tick_ok_users increment (pre:GState) : bool :=
  allf (user_can_advance_timer increment) pre.(users).

(* It is ok to advance time if:
   - the network is partitioned (message delivery delays are ignored), or
   - the time increment does not cause missing a message delivery deadline
 *)
Definition tick_ok_msgs (increment:posreal) (pre:GState) : bool :=
  is_partitioned pre ||
  let target_time := (pre.(now) + pos increment)%R in
  \big[andb/true]_(user_msgs <- codomf pre.(msg_in_transit))
   \big[andb/true]_(m <- (enum_mset user_msgs)) Rleb target_time (fst m).

(* Returns whether time may advance, taking into consideration the state of
   the network, users, their deadlines and message deadlines.
 *)
Definition tick_ok (increment:posreal) (pre:GState) : bool :=
  tick_ok_users increment pre && tick_ok_msgs increment pre.

(* Advance all (honest) user timers by the given increment *)
Definition tick_users increment pre : {fmap UserId -> UState} :=
  updf pre.(users) (domf pre.(users)) (fun _ us => user_advance_timer increment us).

(* Computes the global state after advancing time with the given increment *)
Definition tick_update increment pre : GState :=
  {[ {[ pre with now := (pre.(now) + pos increment)%R ]}
       with users := tick_users increment pre ]}.

(* Computes the standard deadline of a message based on its type *)
Definition msg_deadline (msg : Msg) now : R :=
  match msg.1.1.1.1 with
  | Block => (now + lambda + big_lambda)%R
  | _ => (now + lambda)%R
  end.

Definition merge_msgs_deadline (now : R) (msgs : seq Msg) (v : {mset R * Msg}) : {mset R * Msg} :=
  seq_mset [seq (msg_deadline msg now,msg) | msg <- msgs] `+` v.

Definition send_broadcasts_def (now : R) (targets : {fset UserId}) (prev_msgs : MsgPool) (msgs : seq Msg) : MsgPool :=
  updf prev_msgs targets (fun _ => merge_msgs_deadline now msgs).
Fact send_broadcasts_key: unit. Proof using. exact tt. Qed.
Definition send_broadcasts
  := locked_with send_broadcasts_key send_broadcasts_def.
Canonical send_broadcasts_unlockable := [unlockable fun send_broadcasts].

(* onth: option returning nth element of seq if n small enough *)
Definition onth {T : Type} (s : seq T) (n : nat) : option T :=
  ohead (drop n s).

(* returns True if P is true at nth element in path p *)
Definition at_step n (p : seq GState) (P : pred GState) : bool :=
  match drop n p with
  | g :: _ => P g
  | [::] => false
  end.

(* Returns true if the given user id is found in the map and the user state
   corresponding to that id is for a corrupt user *)
Definition is_user_corrupt (uid : UserId) (users : {fmap UserId -> UState}) : bool :=
  if users.[? uid] is Some u then u.(corrupt) else false.

Definition is_user_corrupt_gstate (uid : UserId) (g : GState) : bool :=
  is_user_corrupt uid (g.(users)).

Definition user_honest (uid:UserId) (g:GState) : bool :=
  if g.(users).[? uid] is Some ustate then ~~ (ustate.(corrupt)) else false.

Definition user_honest_at ix p (uid : UserId) : bool :=
  at_step ix p (user_honest uid).

(* Returns the given users map restricted to honest users only *)
Definition honest_users (users : {fmap UserId -> UState}) :=
  let corrupt_ids :=
    [fset x in domf users | is_user_corrupt x users] in
    users.[\ corrupt_ids] .

(* Computes the global state after a message delivery, given the result of the
   user transition and the messages sent out
   Notes: - the delivered message is removed from the user's mailbox
          - broadcasts new messages to honest users only
 *)
Definition delivery_result pre uid (uid_has_mailbox : uid \in pre.(msg_in_transit)) delivered ustate_post (sent: seq Msg) : GState :=
  let users' := pre.(users).[uid <- ustate_post] in
  let user_msgs' := (pre.(msg_in_transit).[uid_has_mailbox] `\ delivered)%mset in
  let msgs' := send_broadcasts pre.(now) (domf (honest_users pre.(users)) `\ uid)
                              pre.(msg_in_transit).[uid <- user_msgs'] sent in
  let msgh' := (pre.(msg_history)  `+` (seq_mset sent))%mset in
  {[ {[ {[ pre with users          := users' ]}
               with msg_in_transit := msgs' ]}
               with msg_history    := msgh' ]}.
Arguments delivery_result : clear implicits.

(* Computes the global state after an internal user-level transition
   given the result of the user transition and the messages sent out *)
Definition step_result pre uid ustate_post (sent: seq Msg) : GState :=
  let users' := pre.(users).[uid <- ustate_post] in
  let msgs' := send_broadcasts pre.(now) (domf (honest_users pre.(users)) `\ uid)
                               pre.(msg_in_transit) sent in
  let msgh' := (pre.(msg_history)  `+` (seq_mset sent))%mset in
  {[ {[ {[ pre with users          := users' ]}
               with msg_in_transit := msgs' ]}
               with msg_history    := msgh' ]}.

Definition new_deadline now cur_deadline msg : R :=
  let max_deadline := msg_deadline msg now in
  Rmax cur_deadline max_deadline.

(* Resets the deadline of a message having a missed deadline *)
Definition reset_deadline now (msg : R * Msg) : R * Msg :=
  (new_deadline now msg.1 msg.2, msg.2).

Definition map_mset {A B : choiceType} (f : A -> B) (m : {mset A}) : {mset B} :=
  seq_mset (map f m).

(* Recursively resets message deadlines of all the messages given *)
Definition reset_user_msg_delays msgs now : {mset R * Msg} :=
  map_mset (reset_deadline now) msgs.

(* Constructs a message pool with all messages having missed delivery deadlines
   updated appropriately based on the message type *)
Definition reset_msg_delays (msgpool : MsgPool) now : MsgPool :=
  updf msgpool (domf msgpool) (fun _ msgs => reset_user_msg_delays msgs now).

(* Postpones the deadline of a message (extending its delivery delay) *)
Definition extend_deadline r (msgs : {mset R * Msg}) (msg : R * Msg) : {mset R * Msg} :=
  let ext_deadline := (fst msg + r)%R in
  (msgs `+` [mset (ext_deadline, msg.2)])%mset.

(* Computes the state resulting from getting partitioned *)
(* Note: this no longer injects extended message delays (see the tick rule) *)
Definition make_partitioned (pre:GState) : GState :=
  flip_partition_flag pre.

(* Computes the state resulting from recovering from a partition *)
Definition recover_from_partitioned pre : GState :=
  let msgpool' := reset_msg_delays pre.(msg_in_transit) pre.(now) in
  {[ (flip_partition_flag pre) with msg_in_transit := msgpool' ]}.

(* Marks a user state corrupted by setting the corrupt flag *)
Definition make_corrupt ustate : UState :=
  {[ ustate with corrupt := true ]}.

(* Drop the set of messages targeted for a specific user from the given
   message map *)
Definition drop_mailbox_of_user uid (msgs : MsgPool) : MsgPool :=
  if msgs.[? uid] is Some mailbox then msgs.[uid <- mset0] else msgs.

(* Computes the state resulting from corrupting a user *)
(* The user will have its corrupt flag (in its local state) set to true
   and his mailbox in the global state removed *)
Definition corrupt_user_result (pre : GState) (uid : UserId)
                               (ustate_key : uid \in pre.(users)) : GState :=
  let ustate' := make_corrupt pre.(users).[ustate_key] in
  let msgs' := drop_mailbox_of_user uid  pre.(msg_in_transit) in
  let users' := pre.(users).[uid <- ustate'] in
    {[ {[ pre with users := users'         ]}
              with msg_in_transit := msgs' ]}.

(* Computes the state resulting from replaying a message to a user *)
(* The message is replayed to the given target user and added to his mailbox *)
(* It is not broadcast because other users have already seen the original *)
Definition replay_msg_result (pre : GState) (uid : UserId) (msg : Msg) : GState :=
  let msgs' := send_broadcasts pre.(now) [fset uid] (* (domf (honest_users pre.(users))) *)
                 pre.(msg_in_transit) [:: msg] in
  {[ pre with msg_in_transit := msgs' ]}.

(* Does the adversary have the keys of the user for the given r-p-s? *)
(* The adversary will have the keys if the user is corrupt and the given
   r-p-s comes after (or is equal to) the r-p-s of the user *)
Definition have_keys ustate r p s : Prop :=
  ustate.(corrupt) /\ step_le (step_of_ustate ustate) (r,p,s).

Definition mtype_matches_step mtype mval s : Prop :=
  match mtype, mval with
  | Block, val _ | Proposal, val _ | Reproposal, repr_val _ _ _ => s = 1
  | Softvote, val _ => s = 2
  | Certvote, val _ => s = 3
  | Nextvote_Open, step_val s' => s = s'
  | Nextvote_Val, next_val _ s' => s = s'
  | _, _ => False
  end.

(* Computes the state resulting from forging a message to a user *)
(* The message is first created and then queued at the target user's mailbox *)
Definition forge_msg_result (pre : GState) (uid : UserId) r p mtype mval : GState :=
  let msg := (mtype, mval, r, p, uid) in
  let msgs' := send_broadcasts pre.(now) (domf (honest_users pre.(users)))
                 pre.(msg_in_transit) [:: msg] in
  {[ pre with msg_in_transit := msgs' ]}.

(* The global transition relation *)

Reserved Notation "x ~~> y" (at level 90).

Inductive GTransition : g_transition_type :=
(* Advance the global time *)
(* Notes: - corrupt user deadlines are ignored
          - when partitioned, message delivery delays are ignored
 *)
| step_tick : forall increment pre,
    tick_ok increment pre ->
    pre ~~> tick_update increment pre

(* Deliver a message to a user (honest users only) *)
| step_deliver_msg : forall pre uid (msg_key : uid \in pre.(msg_in_transit)) pending,
    pending \in pre.(msg_in_transit).[msg_key] ->
    forall (key_ustate : uid \in pre.(users)) ustate_post sent,
      ~ pre.(users).[key_ustate].(corrupt) ->
      uid # pre.(users).[key_ustate] ; snd pending ~> (ustate_post, sent) ->
      pre ~~> delivery_result pre uid msg_key pending ustate_post sent

(* Progress based on an internal step of a user (honest users only) *)
| step_internal : forall pre uid (ustate_key : uid \in pre.(users)),
      ~ pre.(users).[ustate_key].(corrupt) ->
      forall ustate_post sent,
        uid # pre.(users).[ustate_key] ~> (ustate_post, sent) ->
        pre ~~> step_result pre uid ustate_post sent

(* Recover from a partition *)
| step_exit_partition : forall pre,
    is_partitioned pre ->
    pre ~~> recover_from_partitioned pre

(* [Adversary action] - partition the network *)
| step_enter_partition : forall pre,
    is_unpartitioned pre ->
    pre ~~> make_partitioned pre

(* [Adversary action] - corrupt a user *)
| step_corrupt_user : forall pre uid (ustate_key : uid \in pre.(users)),
    ~ pre.(users).[ustate_key].(corrupt) ->
    pre ~~> @corrupt_user_result pre uid ustate_key

(* [Adversary action] - inject extended message delays *)
(* -- modeled by step_tick ignoring message delivery deadlines when partitioned *)

(* [Adversary action] - replay a message seen before *)
| step_replay_msg : forall pre uid (ustate_key : uid \in pre.(users)) msg,
    ~ pre.(users).[ustate_key].(corrupt) ->
    msg \in pre.(msg_history) ->
    pre ~~> replay_msg_result pre uid msg

(* [Adversary action] - forge and send out a message *)
| step_forge_msg : forall pre sender (sender_key : sender \in pre.(users))
                          r p s mtype mval,
    have_keys pre.(users).[sender_key] r p s ->
    comm_cred_step sender r p s ->
    mtype_matches_step mtype mval s ->
    pre ~~> forge_msg_result pre sender r p mtype mval

where "x ~~> y" := (GTransition x y) : type_scope.

(* There is step at index n from g1 to g2 along a path p. This means g1 and g2
   are adjacent elements in the path *)
Definition step_in_path_at (g1 g2 : GState) n (p : seq GState) : Prop :=
  match drop n p with
  | g1' :: g2' :: _ => [/\ g1' = g1 & g2' = g2]
  | _ => False
  end.

(* definition of reachable global state via paths *)
Definition gtransition : rel GState := [rel x y | `[<GTransition x y>] ].

(* A trace starts from g0 and transitions via GTransitions at each step in the path p *)
Definition is_trace (g0 : GState) (p : seq GState) : Prop :=
  nosimpl match p with
          | [::] => False
          | [:: g' & rest] => [/\ g0 = g' & path gtransition g0 rest]
          end.

(* reachability between pairs of states under the reflexive-transitive closure of the transition relation *)
Definition greachable (g0 g : GState) : Prop := exists2 p, is_trace g0 p & g = last g0 p.

(* classic definition of reachable global state *)
Definition GReachable (g0 g : GState) : Prop := clos_refl_trans_1n _ GTransition g0 g.

(* labels to classify transitions more abstractly *)
Inductive GLabel : Type :=
| lbl_tick :  posreal -> GLabel
| lbl_deliver : UserId -> R -> Msg -> seq Msg -> GLabel
| lbl_step_internal : UserId -> seq Msg -> GLabel
| lbl_exit_partition : GLabel
| lbl_enter_partition : GLabel
| lbl_corrupt_user : UserId -> GLabel
| lbl_replay_msg : UserId -> GLabel
| lbl_forge_msg : UserId -> nat -> nat -> MessageType -> ExValue -> GLabel.

(* specify when labels classify a transition between pairs of global states *)
Definition related_by (label : GLabel) (pre post : GState) : Prop :=
  match label with
  | lbl_tick increment =>
      tick_ok increment pre /\ post = tick_update increment pre
  | lbl_deliver uid deadline delivered_msg sent =>
      exists (key_ustate : uid \in pre.(users)) ustate_post,
         uid # pre.(users).[key_ustate] ; delivered_msg ~> (ustate_post,sent)
         /\ ~ pre.(users).[key_ustate].(corrupt)
      /\ exists (key_mailbox : uid \in pre.(msg_in_transit)),
           (deadline,delivered_msg) \in pre.(msg_in_transit).[key_mailbox]
           /\ post = delivery_result pre uid key_mailbox (deadline,delivered_msg) ustate_post sent
  | lbl_step_internal uid sent =>
      exists (key_user : uid \in pre.(users)) ustate_post,
      ~ pre.(users).[key_user].(corrupt) /\
      uid # pre.(users).[key_user] ~> (ustate_post,sent)
      /\ post = step_result pre uid ustate_post sent
  | lbl_exit_partition =>
      is_partitioned pre /\ post = recover_from_partitioned pre
  | lbl_enter_partition =>
      is_unpartitioned pre /\ post = make_partitioned pre
  | lbl_corrupt_user uid =>
      exists (ustate_key : uid \in pre.(users)),
      ~ pre.(users).[ustate_key].(corrupt)
      /\ post = @corrupt_user_result pre uid ustate_key
  | lbl_replay_msg uid =>
      exists (ustate_key : uid \in pre.(users)) msg,
      ~ pre.(users).[ustate_key].(corrupt)
      /\ msg \in pre.(msg_history)
      /\ post = replay_msg_result pre uid msg
  | lbl_forge_msg sender r p mtype mval =>
      exists (sender_key : sender \in pre.(users)) s,
         have_keys pre.(users).[sender_key] r p s
      /\ comm_cred_step sender r p s
      /\ mtype_matches_step mtype mval s
      /\ post = forge_msg_result pre sender r p mtype mval
  end.
