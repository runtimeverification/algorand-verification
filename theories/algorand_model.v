From mathcomp.ssreflect
Require Import all_ssreflect.

From mathcomp.finmap
Require Import finmap multiset.

From Coq
Require Import Reals Relation_Definitions Relation_Operators.

From mathcomp.analysis
Require Import boolp Rstruct.

From RecordUpdate
Require Import RecordSet.
Import RecordSetNotations.

From Algorand
Require Import fmap_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope mset_scope.
Open Scope fmap_scope.
Open Scope fset_scope.

(** * Algorand parameters, data, and transition system *)

(** This module contains the definitions that comprise the Algorand consensus
protocol model. *)

(** ** Basic parameters *)

(** We assume a finite set of users. *)
Parameter UserId : finType.

(** We assume a countable set of values (blocks and block hashes). *)
Parameter Value : choiceType.

(** ** Message type *)

(** An enumeration of all possible types (headers) of messages. *)
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

Lemma MessageType_eqP : Equality.axiom MessageType_eq.
Proof.
  move => a b;apply Bool.iff_reflect;split.
    by move <-;destruct a.
    by move/(ifT (a=b) True) => <-;destruct a, b.
Qed.

(** Make [MessageType] a [finType] by showing a mapping
to the MathComp bounded [nat] type ['I_7].
*)
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
Proof. by case;rewrite /o2mtype /= inordK. Qed.

(** Register canonical structures on [MessageType]; needed for using it in [fset]s, [mset]s, etc. *)
Canonical messageType_eqType     := EqType     MessageType (Equality.Mixin MessageType_eqP).
Canonical messageType_choiceType := ChoiceType MessageType (PcanChoiceMixin pcancel_MessageType_7).
Canonical messageType_countType  := CountType  MessageType (PcanCountMixin  pcancel_MessageType_7).
Canonical messageType_finType    := FinType    MessageType (PcanFinMixin    pcancel_MessageType_7).

(** ** Extended value type *)

(** Message payload type, packaging [Value] and other data. *)
Inductive ExValue :=
  | val      : Value -> ExValue
  | step_val : nat -> ExValue
  | repr_val : Value -> UserId -> nat -> ExValue
  | next_val : Value -> nat -> ExValue.

(** Make [ExValue] an equality type and a choice type. *)
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
Proof. by case. Qed.

(** Register canonical structures on [ExValue]; needed for using it in [fset]s, [mset]s, etc. *)
Canonical exValue_eqType     := EqType     ExValue (PcanEqMixin     cancelExVal).
Canonical exValue_choiceType := ChoiceType ExValue (PcanChoiceMixin cancelExVal).

(** ** Messages *)

(** A message is represented by a record type for convenience, but
can be viewed as a tuple [(type, ev, r, p, id)] where:
- [type] is the message type, and
- [ev] is the message payload, and
- [r] is the round value, and
- [p] is the period value, and
- [id] is the sending user's identifier. *)

Record Msg : Type := mkMsg
 { msg_type : MessageType ;
   msg_ev : ExValue ;
   msg_round : nat ;
   msg_period : nat ;
   msg_sender : UserId
 }.

Definition codeMsg (m : Msg) : MessageType * ExValue * nat * nat * UserId :=
(msg_type m, msg_ev m, msg_round m, msg_period m, msg_sender m).

Definition decodeMsg (c: MessageType * ExValue * nat * nat * UserId) : Msg :=
mkMsg c.1.1.1.1 c.1.1.1.2 c.1.1.2 c.1.2 c.2.

Lemma cancelMsg : pcancel codeMsg (fun x => Some (decodeMsg x)).
Proof. by case. Qed.

(** Register canonical structures on [Msg]; needed for using it in [fset]s, [mset]s, etc. *)
Canonical Msg_eqType     := EqType     Msg (PcanEqMixin     cancelMsg).
Canonical Msg_choiceType := ChoiceType Msg (PcanChoiceMixin cancelMsg).

(** Messages are grouped by the target user, and are paired with a
delivery deadline. In the absence of a partition, messages must
be delivered before the deadline is reached. *)
Definition MsgPool := {fmap UserId -> {mset R * Msg}}%mset.

(** ** Credentials *)

(** The credential of a user at a round-period-step triple.
Note: We abstract away the random value produced by an oracle
and the fact that credentials are interpreted as integer
values. Instead, we model the type of credentials as an
abstract totally ordered type. *)
Parameter credType : orderType tt.

(** A credential is constructed using the user's identifier and the
current round-period-step values. *)
Parameter credential : UserId -> nat -> nat -> nat -> credType.

(** Credentials of two different users must be different. *)
Axiom credentials_different :
  forall (u u' : UserId) (r r' : nat) (p p' : nat) (s s' : nat),
  u <> u' -> credential u r p s <> credential u' r' p' s'.

(** A predicate defining whether a given credential qualifies its
owner to be a committee member. This abstracts away from how
credential values are interpreted. *)
Parameter committee_cred : credType -> Prop.

(** Whether the credential is a committee credential for the given
round-period-step triple. *)
Definition comm_cred_step uid r p s : Prop :=
  committee_cred (credential uid r p s).

Axiom credentials_valid_period:
  forall uid r p s, comm_cred_step uid r p s -> 1 <= p.

(** ** User state *)

(** A proposal/reproposal record is a quadruple consisting of
a user id, a user's credential, a value and a boolean
indicating whether the record represents a proposal ([true])
or a reproposal ([false]). *)
Definition PropRecord := (UserId * credType * Value * bool)%type.

(** A vote is a pair of a [UserId] (the identifier of the voter)
and a [Value] (the value voted for). *)
Definition Vote := (UserId * Value)%type.

(**
The structure of a user's state.
*)
Record UState :=
  mkUState {
    corrupt        : bool; (**r a flag indicating whether the user is corrupt *)
    round          : nat; (**r the user's current round (starts at 1) *)
    period         : nat; (**r the user's current period (starts at 1) *)
    step           : nat; (**r the user's current step counter (starts at 1) *)
    timer          : R; (**r the user's current timer value (since the beginning of the current period) *)
    deadline       : R; (**r the user's next deadline time value (since the beginning of the current period) *)
    p_start        : R; (**r the (local) time at which the user's current period started (i.e., local clock = p_start + timer) *)
    proposals      : nat -> nat -> seq PropRecord; (**r a sequence of proposal/reproposal records for the given round/period *)
    stv            : nat -> option Value; (**r starting value *)
    blocks         : {fsfun nat -> seq Value with [::]}; (**r a sequence of values seen for the given round *)
    softvotes      : nat -> nat -> seq Vote; (**r a sequence of softvotes seen for the given round/period *)
    certvotes      : nat -> nat -> seq Vote; (**r a sequence of certvotes seen for the given round/period *)
    nextvotes_open : nat -> nat -> nat -> seq UserId; (**r a sequence of bottom-nextvotes seen for the given round/period/step *)
    nextvotes_val  : nat -> nat -> nat -> seq Vote (**r a sequence of value-nextvotes seen for the given round/period/step *)
   }.

Instance UState_Settable : Settable _ :=
  settable! mkUState <corrupt;round;period;step;timer;deadline;p_start;
   proposals;stv;blocks;softvotes;certvotes;nextvotes_open;nextvotes_val>.

(** ** Updating user state *)

(** Update functions for sequences maintained in the user state. *)
Definition set_proposals u r' p' prop : UState :=
  u <| proposals := fun r p =>
        if (r, p) == (r', p')
        then undup (prop :: u.(proposals) r p)
        else u.(proposals) r p |>.

Definition set_blocks (u : UState) (r':nat) block : UState :=
  u <| blocks := setfs u.(blocks) r' (undup (block :: u.(blocks) r')) |>.

Definition set_softvotes (u : UState) r' p' sv : UState :=
  u <| softvotes := fun r p =>
        if (r, p) == (r', p')
        then undup (sv :: u.(softvotes) r p)
        else u.(softvotes) r p |>.

Definition set_certvotes (u : UState) r' p' sv : UState :=
  u <| certvotes := fun r p =>
        if (r, p) == (r', p')
        then undup (sv :: u.(certvotes) r p)
        else u.(certvotes) r p |>.

Definition set_nextvotes_open (u : UState) r' p' s' nvo : UState :=
  u <| nextvotes_open := fun r p s =>
        if (r, p, s) == (r', p', s')
        then undup (nvo :: u.(nextvotes_open) r p s)
        else u.(nextvotes_open) r p s |>.

Definition set_nextvotes_val (u : UState) r' p' s' nvv : UState :=
  u <| nextvotes_val := fun r p s =>
        if (r, p, s) == (r', p', s')
        then undup (nvv :: u.(nextvotes_val) r p s)
        else u.(nextvotes_val) r p s |>.

(** Update function for advancing the period of a user state. *)
Definition advance_period (u : UState) : UState :=
  u <| period := (u.(period) + 1)%nat |>
    <| step := 1%nat |>
    <| timer := 0%R |>
    <| deadline := 0%R |>
    <| p_start := (u.(p_start) + u.(timer))%R |>.

(** Update function for advancing the round of a user state. *)
Definition advance_round (u : UState) : UState :=
  u <| round := (u.(round) + 1)%nat |>
    <| period := 1%nat |>
    <| step := 1%nat |>
    <| stv := fun x => None |>
    <| timer := 0%R |>
    <| deadline := 0%R |>
    <| p_start := (u.(p_start) + u.(timer))%R |>.

(** ** Global State *)

(** The structure of the global state. *)
Record GState :=
  mkGState {
    now : R; (**r the current global time value *)
    network_partition : bool; (**r a flag indicating whether the network is currently partitioned *)
    users : {fmap UserId -> UState}; (**r the global set of users as a finite map of user ids to user states *)
    msg_in_transit : {fmap UserId -> {mset R * Msg}}; (**r messages in transit as a finite map from user identifiers (targets) to multisets of messages *)
    msg_history : {mset Msg} (**r the history of all broadcasted messages as a multiset of messages *)
  }.

Instance GState_Settable : Settable _ :=
 settable! mkGState <now;network_partition;users;msg_in_transit;msg_history>.

(** State with empty maps, unpartitioned, at global time 0. *)
Definition null_state : GState := mkGState 0%R false [fmap] [fmap] mset0.

(*
Definition codeGState (g : GState) :=
 (now g, network_partition g, users g, msg_in_transit g, msg_history g).

Definition decodeGState c :=
mkGState c.1.1.1.1 c.1.1.1.2 c.1.1.2 c.1.2 c.2.

Lemma cancelGState : pcancel codeGState (fun x => Some (decodeGState x)).
Proof. by case. Qed.

Canonical GState_eqType := EqType GState (PcanEqMixin cancelGState).
Canonical GState_choiceType := ChoiceType GState (PcanChoiceMixin cancelMsg).
*)

(** Equality of global states. *)
Definition eqGState (g1 g2 : GState) : bool := `[<g1 = g2>].

Lemma eqGStateP : Equality.axiom eqGState.
Proof. by move => g1 g2; apply/asboolP. Qed.

Canonical GState_eqMixin := EqMixin eqGStateP.
Canonical GState_eqType := Eval hnf in EqType GState GState_eqMixin.

(** Flipping the network partition flag. *)
Definition flip_partition_flag (g : GState) : GState :=
  g <| network_partition := ~~ g.(network_partition) |>.

(** ** Global parameters and axioms of the system *)

(** Small (non-block) message delivery delay. *)
Parameter lambda : R.

(** Block message delivery delay. *)
Parameter big_lambda : R.

(** Recovery time period. *)
Parameter L : R.

(** Axioms on how these bounds are related. *)
Axiom delays_positive : (lambda > 0)%R.

Axiom delays_order : (3 * lambda <= big_lambda < L)%R.

(** Number of soft-votes needed to cert-vote. *)
Parameter tau_s : nat.

(** Number of cert-votes needed for a certificate. *)
Parameter tau_c : nat.

(* Number of next-votes for bottom to move to next period. *)
Parameter tau_b : nat.

(* Number of next-votes for a value to move to next period. *)
Parameter tau_v : nat.

(** An abstract predicate on values that tells us whether a value is valid. *)
Parameter valid : Value -> Prop.

(** An abstract predicate on values that tells us whether a
given hash value is indeed the hash of the given block value. *)
Parameter correct_hash : Value -> Value -> Prop.

(** ** Helper definitions for user-state transitions *)

(** The block has been seen and is valid and the given value is
indeed its hash value. *)
Definition valid_block_and_hash b v : Prop :=
  valid b /\ correct_hash v b.

(** From user state, get round-period-step triple. *)
Definition step_of_ustate (u:UState) :=
  (u.(round), u.(period), u.(step)).

(** Steps are ordered lexicographically ([Prop] versions). *)
Definition step_le (step1 step2: nat * nat * nat) :=
  let: (r1,p1,s1) := step1 in
  let: (r2,p2,s2) := step2 in
  r1 < r2 \/ r1 = r2 /\ (p1 < p2 \/ p1 = p2 /\ s1 <= s2).

Definition step_lt (step1 step2: nat * nat * nat) :=
  let: (r1,p1,s1) := step1 in
  let: (r2,p2,s2) := step2 in
  r1 < r2 \/ r1 = r2 /\ (p1 < p2 \/ p1 = p2 /\ s1 < s2).

(** Steps are ordered lexicographically ([bool] versions). *)
Definition step_leb (step1 step2: nat * nat * nat) : bool :=
  let: (r1,p1,s1) := step1 in
  let: (r2,p2,s2) := step2 in
  (r1 < r2) || (r1 == r2) && ((p1 < p2) || (p1 == p2) && (s1 <= s2)).

Definition step_ltb (step1 step2: nat * nat * nat) : bool :=
  let: (r1,p1,s1) := step1 in
  let: (r2,p2,s2) := step2 in
  (r1 < r2) || (r1 == r2) && ((p1 < p2) || (p1 == p2) && (s1 < s2)).

(** [us2] is after [us1] if the step of [us1] is less than the step of [us2]. *)
Definition ustate_after_strict us1 us2 : Prop :=
  step_lt (step_of_ustate us1) (step_of_ustate us2).

(** [us2] is no earlier than [us1] in terms of round-period-step ordering. *)
Definition ustate_after us1 us2 : Prop :=
  us1.(round) < us2.(round)
  \/ (us1.(round) = us2.(round) /\ us1.(period) < us2.(period))
  \/ (us1.(round) = us2.(round) /\ us1.(period) = us2.(period) /\ us1.(step) <= us2.(step)).

Definition msg_step_s (mtype : MessageType) (v : ExValue) : nat :=
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
  (msg_round msg, msg_period msg, msg_step_s (msg_type msg) (msg_ev msg)).

(** Is the given message a vote (softvote, certvote, or nextvote) message? *)
Definition vote_msg (msg : Msg) : Prop :=
  match msg_type msg with
  | Softvote | Certvote | Nextvote_Open | Nextvote_Val => True
  | _ => False
  end.

(** Does the given round-period-step match the ones stored in the user state? *)
Definition valid_rps (u : UState) r p s : Prop :=
  u.(round) = r /\ u.(period) = p /\ u.(step) = s.

Definition advancing_rp (u : UState) r p : Prop :=
  u.(round) < r \/ u.(round) = r /\ u.(period) <= p.

(** Is the vote [x] for this value [v]? *)
Definition matchValue (x : Vote) (v : Value) : bool :=
  let: (u', v') := x in v == v'.

(**
The sequence of all values appearing in a given sequence of votes with
duplicates removed.
*)
Definition vote_values (vs: seq Vote) : seq Value :=
  undup [seq x.2 | x <- vs].

Definition softvoters_for (v:Value) (u:UState) r p : {fset UserId} :=
  [fset x.1 | x in u.(softvotes) r p & matchValue x v].

Definition nextvoters_open_for (u:UState) r p s : {fset UserId} :=
  [fset x in u.(nextvotes_open) r p s].

Definition nextvoters_val_for (v:Value) (u:UState) r p s : {fset UserId} :=
  [fset x.1 | x in u.(nextvotes_val) r p s & matchValue x v].

(** The number of softvotes of a given value in a given user state for the round
and period given. Does not use the invariant that [u.(softvotes) r p] is duplicate-free. *)
Definition soft_weight (v:Value) (u:UState) r p : nat :=
  size (softvoters_for v u r p).

(** The sequence of values with high enough softvotes in a given user state for given round 
and period, i.e., the sequence of values in softvotes having votes greater than or equal 
to the threshold. Invariant: size is [<= 1]. *)
Definition certvals (u:UState) r p : seq Value :=
  [seq v <- vote_values (u.(softvotes) r p) | (soft_weight v u r p) >= tau_s].

(** The sequence of values certified for in the last period as seen by the given user.
This corresponds to prev_certvals field in the automaton model. *)
Definition prev_certvals (u:UState) : seq Value :=
  let p := u.(period) in
  if p > 1 then certvals u u.(round) (p - 1) else [::].

(** Whether the user has seen enough votes for bottom in the given round-period-step. *)
Definition nextvote_bottom_quorum (u:UState) r p s : Prop :=
  #|(u.(nextvotes_open) r p s)| >= tau_b.

(** Whether the user has seen enough nextvotes for a given value in the given round-period-step. *)
Definition nextvote_value_quorum (u:UState) v r p s : Prop :=
  #|[seq x.1 | x <- u.(nextvotes_val) r p s & matchValue x v]| >= tau_v.

(** Whether the user has seen enough nextvotes for some value in the given round-period-step. *)
Definition nextvote_quorum_for_some_value (u:UState) r p s : Prop :=
  exists v, nextvote_value_quorum u v r p s.

(** Whether a quorum for bottom was not seen in the last period
of the current round (for some step during that period). *)
Definition cert_may_exist (u:UState) : Prop :=
  let p := u.(period) in
  let r := u.(round) in
  p > 1 /\ forall s, ~ nextvote_bottom_quorum u r (p - 1) s.

(** Proposal record ordering induced by ordering on credentials. *)
Definition reclt (rec rec' : PropRecord) : bool := (rec.1.1.2 < rec'.1.1.2)%O.

(** Returns the proposal record in a given sequence of records having the least
credential, i.e., the record of the potential leader. *)
Fixpoint least_record (prs : seq PropRecord) : option PropRecord :=
  match prs with
  | [::] => None
  | [:: rec & prs'] =>
    match least_record prs' with
    | None => Some rec
    | Some rec' =>
      if reclt rec' rec
      then Some rec'
      else Some rec
    end
  end.

(** Returns whether the given (proposal) value is the potential leader value. *)
Definition leader_prop_value (v : Value) (prs : seq PropRecord) : Prop :=
  let opr := least_record prs in
  match opr with
  | None => False
  | Some (_,_, _, false) => False
  | Some (_,_, v', true) => v = v'
  end.

(** Returns whether the given (reproposal) value is the potential leader value. *)
Definition leader_reprop_value (v : Value) (prs : seq PropRecord) : Prop :=
  let opr := least_record prs in
  match opr with
  | None => False
  | Some (_,_, _, true) => False
  | Some (_,_, v', false) => v = v'
  end.

(** The timer deadline value for the NEXT step following the given step value.
Note that [k] is zero-based and hence the apparent difference from the Algorand paper.
The computed deadline values are exactly as given in the paper. *)
Definition next_deadline k : R :=
  match k with
  | 0 => 0 (**r deadline for step 1 *)
  | 1 => (2 * lambda)%R (**r deadline for step 2 *)
  | 2 => (lambda + big_lambda)%R (**r deadline for step 3 *)
  | n => (lambda + big_lambda + (INR n - 3) * L)%R (**r deadlines for steps 4, 5, 6, ... *)
  end.

(** ** Step 1: Proposing predicates and user state updates *)

(** The proposal step preconditions. Note that this covers both:
- the case when [p = 1], and
- the case when [p > 1] with the previous period voting for bottom.

Just as in the automaton model, the fact that the last period's quorum
was not for bottom is captured by the predicate [cert_may_exist]. *)
Definition propose_ok (pre : UState) uid v b r p : Prop :=
  pre.(timer) = 0%R /\
  valid_rps pre r p 1 /\
  comm_cred_step uid r p 1 /\
  valid_block_and_hash b v /\
  ~ cert_may_exist pre.

(** The reproposal step preconditions. Note that this is the proposal
step when [p > 1] and a next-vote quorum for a value [v] was
seen in [p - 1]. Note also that this may overlap with the case
above, when [cert_may_exist] does not hold. *)
Definition repropose_ok (pre : UState) uid v r p : Prop :=
  pre.(timer) = 0%R /\
  valid_rps pre r p 1 /\ p > 1 /\
  comm_cred_step uid r p 1 /\
  exists s, nextvote_value_quorum pre v r (p - 1) s.

(** The no-propose step preconditions.Note that this applies
regardless of whether [p = 1]. *)
Definition no_propose_ok (pre : UState) uid r p : Prop :=
  pre.(timer) = 0%R /\
  valid_rps pre r p 1 /\
  (comm_cred_step uid r p 1 ->
    cert_may_exist pre /\
    forall s v, ~ nextvote_value_quorum pre v r (p - 1) s).

(** The proposing step (propose, repropose and nopropose) post-state.
Move on to softvoting and set the new deadline to [2*lambda]. *)
Definition propose_result (pre : UState) : UState :=
  pre <| deadline := (2 * lambda)%R |>
      <| step := 2%nat |>.

(** ** Step 2: Softvoting predicates and user state updates *)

(** The Softvoting-a-proposal step preconditions. This covers both:
- the case when [p = 1], and
- the case when [p > 1] with the previous period voting for bottom.

Note that:
- the automaton model has the constraint clock [>= 2*lambda], and
- the phrase "[v] is a period 1 block" in the Algorand2 description
  is interpreted here as "[v] is a reproposal", for simplicity. *)
Definition softvote_new_ok (pre : UState) uid v r p : Prop :=
  pre.(timer) = (2 * lambda)%R /\
  valid_rps pre r p 2 /\
  comm_cred_step uid r p 2 /\
  ~ cert_may_exist pre /\
  leader_prop_value v (pre.(proposals) r p) .

(** The Softvoting-a-reproposal step preconditions
Note that this is the Softvoting step when [p > 1] and the previous period's
winning vote was for a value [v]. *)
Definition softvote_repr_ok (pre : UState) uid v r p : Prop :=
  pre.(timer) = (2 * lambda)%R /\
  valid_rps pre r p 2 /\ p > 1 /\
  comm_cred_step uid r p 2 /\
  ( (~ cert_may_exist pre /\
    (exists s, nextvote_value_quorum pre v r (p - 1) s) /\
    leader_reprop_value v (pre.(proposals) r p))
    \/
    (cert_may_exist pre /\ pre.(stv) p = Some v) ).

(** The no-softvoting step preconditions. Three reasons a user may
not be able to soft-vote:
- not being in the soft-voting committee, or
- not being able to identify a potential leader value to soft-vote for
- not seeing enough next-votes for a value reproposed when the previous period
  had a quorum for bottom.

Note that this may apply regardless of whether [p = 1]. *)
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

(** The softvoting step (new or reproposal) post-state.
We keep the current deadline at [2 * lambda] and let certvoting handle
updating the deadline (to avoid timing out while certvoting is already
enabled). This assumes it is ok to certvote at time [2 * lambda]. *)
Definition softvote_result (pre : UState) : UState :=
  pre <| step := 3 |>
      <| deadline := (lambda + big_lambda)%R |>.

(** ** Step 3: Certvoting predicates and user state updates *)

(** Certvoting step preconditions: the successful case. *)
Definition certvote_ok (pre : UState) uid (v b: Value) r p : Prop :=
  ((2 * lambda)%R < pre.(timer) <= lambda + big_lambda)%R /\
  valid_rps pre r p 3 /\
  comm_cred_step uid r p 3 /\
  valid_block_and_hash b v /\
  b \in pre.(blocks) r /\
  v \in certvals pre r p .

(** Certvoting step preconditions: the unsuccessful case - not a committee member. *)
Definition no_certvote_ok (pre : UState) uid r p : Prop :=
  ((2 * lambda)%R < pre.(timer) <= lambda + big_lambda)%R /\
  valid_rps pre r p 3 /\
  ~ comm_cred_step uid r p 3.

(** Certvote timeout preconditions. A user timeouts if the deadline
is reached while waiting for some external messages
(i.e., while observing softvotes in step 3) *)
Definition certvote_timeout_ok (pre : UState) uid r p : Prop :=
  (pre.(timer) >= pre.(deadline))%R /\
  valid_rps pre r p 3 /\
  comm_cred_step uid r p 3 /\
  forall b v,
  (~ valid_block_and_hash b v \/
   ~ b \in pre.(blocks) r \/
   ~ v \in certvals pre r p).

(** The certvoting step's resulting user state.
The state update for all certvoting cases: move on to the next step
(the deadline does not need updating). *)
Definition certvote_result (pre : UState) : UState :=
  pre <| step := 4 |>.

(** ** Steps >= 4: Nextvoting predicates and user state updates *)

(** Nextvoting step preconditions, the proper-value case. Note:
- corresponds (roughly) to transition nextvote_val in the automaton
  model (but not the same), and
- corresponds more closely to the Algorand2 description (but with the
  committee membership constraint).
*)
Definition nextvote_val_ok (pre : UState) uid (v b : Value) r p s : Prop :=
  pre.(timer) = (lambda + big_lambda + (INR s - 4) * L)%R /\
  valid_rps pre r p s /\
  comm_cred_step uid r p s /\
  3 < s /\
  valid_block_and_hash b v /\
  b \in pre.(blocks) r /\
  v \in certvals pre r p.

(** Nextvoting step preconditions, the bottom-value case. Note:
- corresponds (roughly) to transition nextvote_open in the automaton
  model (but not the same), and
- corresponds more closely to the Algorand2 description (but with the
  committee membership constraint).
*)
Definition nextvote_open_ok (pre : UState) uid r p s : Prop :=
  pre.(timer) = (lambda + big_lambda + (INR s - 4) * L)%R /\
  valid_rps pre r p s /\
  comm_cred_step uid r p s /\
  3 < s /\
  (forall v, v \in certvals pre r p -> forall b, b \in pre.(blocks) r ->
     ~valid_block_and_hash b v) /\
  (p > 1 -> nextvote_bottom_quorum pre r (p - 1) s ).

(** Nextvoting step preconditions, the additional special case of using
the starting value. Note:
- this might not be captured in the automaton model, and
- corresponds more closely to the Algorand2 description (but with
  additional constraints given explicitly).
*)
Definition nextvote_stv_ok (pre : UState) uid r p s : Prop :=
  pre.(timer) = (lambda + big_lambda + (INR s - 4) * L)%R /\
  valid_rps pre r p s /\
  comm_cred_step uid r p s /\
  3 < s /\
  (forall v, v \in certvals pre r p -> forall b, b \in pre.(blocks) r ->
     ~valid_block_and_hash b v) /\
  p > 1 /\ ~ nextvote_bottom_quorum pre r (p - 1) s.

(** Nextvoting step preconditions, the no-voting case. *)
Definition no_nextvote_ok (pre : UState) uid r p s : Prop :=
  pre.(timer) = (lambda + big_lambda + (INR s - 4) * L)%R /\
  valid_rps pre r p s /\
  ~ comm_cred_step uid r p s.

(** Nextvoting step state update for steps [s >= 4] (all cases). *)
Definition nextvote_result (pre : UState) s : UState :=
  pre <| step :=  (s + 1)%nat |>
      <| deadline := next_deadline s |>.

(** Advancing period propositions and user state update. *)

(** Preconditions, the bottom-value case. Note that this corresponds
to transition advance_period_open in the automaton model. *)
Definition adv_period_open_ok (pre : UState) r p s : Prop :=
  valid_rps pre r p s /\
  nextvote_bottom_quorum pre r p s.

(** Preconditions, the proper value case. This corresponds to
transition advance_period_val in the automaton model. *)
Definition adv_period_val_ok (pre : UState) (v : Value) r p s : Prop :=
  valid_rps pre r p s /\
  nextvote_value_quorum pre v r p s.

(** State update, the bottom-value case. *)
Definition adv_period_open_result (pre : UState) : UState :=
  (advance_period pre) <| stv := fun p => if p == pre.(period).+1 then None else (pre.(stv) p) |>.

(** State updatem the proper value case. *)
Definition adv_period_val_result (pre : UState) v : UState :=
  (advance_period pre) <| stv := fun p => if p == pre.(period).+1 then Some v else (pre.(stv) p) |>.

(** Advancing round predicates and user state updates. Note:
- corresponds to transition certify in the automaton model, and
- the requirement [valid_rps] has been removed since certification
  may happen at any time.

TODO: need to have some assertion about message age. *)
Definition certify_ok (pre : UState) (v : Value) r p : Prop :=
  advancing_rp pre r p /\
  exists b,
  valid_block_and_hash b v /\
  b \in pre.(blocks) r /\
  size [seq x <- pre.(certvotes) r p | matchValue x v] >= tau_c.

(** State update. *)
Definition certify_result r (pre : UState) : UState :=
  advance_round (pre <| round := r |>).

(** The post state of delivering a non-vote message. *)
Definition deliver_nonvote_msg_result (pre : UState) (msg : Msg) c r p : UState :=
  let type := msg_type msg in
  let id := msg_sender msg in
  let ev := msg_ev msg in
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

(** ** User transition relation - internal transitions *)

(** The internal user-level transition relation type.
An internal transition is a transition that does not consume a message,
and a user transitions from a pre-state into a post-state while emitting
a (possibly empty) sequence of outgoing messages. *)
Definition u_transition_internal_type := UserId -> UState -> (UState * seq Msg) -> Prop.

Reserved Notation "x # z ~> y" (at level 70).

(** Internal actions are supposed to take place either:
- at a specific time instance (i.e. never triggered by a recevied message), or
- during a time duration, but the preconditions are already satisfied that
  the action fires eagerly at the beginning of that time duration (again,
  without consuming a message).
 *)
Inductive UTransitionInternal : u_transition_internal_type :=
| propose : (**r step 1: block proposal *)
    forall uid (pre : UState) v b r p,
      propose_ok pre uid v b r p ->
      uid # pre ~> (propose_result pre, [:: mkMsg Proposal (val v) r p uid ; mkMsg Block (val b) r p uid])

| repropose : (**r step 1: block proposal (reproposal) *)
    forall uid (pre : UState) v r p,
      repropose_ok pre uid v r p ->
      uid # pre ~> (propose_result pre, [:: mkMsg Reproposal (repr_val v uid p) r p uid])

| no_propose : (**r step 1: block proposal (failure) *)
    forall uid (pre : UState) r p,
      no_propose_ok pre uid r p ->
      uid # pre ~> (propose_result pre, [::])

| softvote_new : (**r step 2: filtering step (new value) *)
    forall uid (pre : UState) v r p,
      softvote_new_ok pre uid v r p ->
      uid # pre ~> (softvote_result pre, [:: mkMsg Softvote (val v) r p uid])

| softvote_repr : (**r step 2: filtering step (old value) *)
    forall uid (pre : UState) v r p,
      softvote_repr_ok pre uid v r p ->
      uid # pre ~> (softvote_result pre, [:: mkMsg Softvote (val v) r p uid])

| no_softvote : (**r step 2: filtering step (no value) *)
    forall uid (pre : UState) r p,
      no_softvote_ok pre uid r p ->
      uid # pre ~> (softvote_result pre, [::])

| certvote1 : (**r step 3: certifying step (success) *)
    forall uid (pre : UState) v b r p,
      certvote_ok pre uid v b r p ->
      uid # pre ~> (certvote_result pre, [:: mkMsg Certvote (val v) r p uid])

| no_certvote : (**r step 3: certifying step (failure) *)
    forall uid (pre : UState) r p,
      no_certvote_ok pre uid r p ->
      uid # pre ~> (certvote_result pre, [::])

| nextvote_val : (**r steps >= 4: finishing step, [i] has cert-voted some [v] *)
    forall uid (pre : UState) v b r p s,
      nextvote_val_ok pre uid v b r p s ->
      uid # pre ~> (nextvote_result pre s, [:: mkMsg Nextvote_Val (next_val v s) r p uid])

| nextvote_open : (**r steps >= 4: finishing step, [i] has not cert-voted some [v] *)
    forall uid (pre : UState) r p s,
      nextvote_open_ok pre uid r p s ->
      uid # pre ~> (nextvote_result pre s, [:: mkMsg Nextvote_Open (step_val s) r p uid])

| nextvote_stv : (**r steps >= 4: finishing step, special case of using [stv] *)
    forall uid (pre : UState) v r p s,
      nextvote_stv_ok pre uid r p s /\ pre.(stv) p = Some v ->
        uid # pre ~> (nextvote_result pre s, [:: mkMsg Nextvote_Val (next_val v s) r p uid])

| no_nextvote : (**r steps >= 4: finishing step, no next-voting *)
    forall uid (pre : UState) r p s,
      no_nextvote_ok pre uid r p s ->
      uid # pre ~> (nextvote_result pre s, [::])

| certvote_timeout : (**r certvote timeout transition, applicable only to step = 3 *)
    forall uid (pre : UState) r p,
      certvote_timeout_ok pre uid p r ->
      uid # pre ~> (certvote_result pre, [::])

where "x # y ~> z" := (UTransitionInternal x y z) : type_scope.

(** ** User transition relation - message transitions *)

(** The message-triggered user-level transition relation.
A message-triggered transition consumes an incoming message,
and a user transitions from a pre-state, while consuming a message, into a
post-state and emits a (possibly empty) sequence of outgoing messages. *)
Definition u_transition_msg_type := UserId -> UState -> Msg -> (UState * seq Msg) -> Prop.

Reserved Notation "a # b ; c ~> d" (at level 70).

(** Deliver messages and possibly trigger actions urgently.
Note that advancing the period takes precedence over nextvote2_open actions. *)
Inductive UTransitionMsg : u_transition_msg_type :=
| deliver_softvote : (**r deliver a softvote while not triggering any internal action *)
    forall uid (pre : UState) r p i v b,
      let pre' := (set_softvotes pre r p (i, v)) in
        ~ certvote_ok pre' uid v b r p ->
        uid # pre ; mkMsg Softvote (val v) r p i ~> (pre', [::])

| deliver_softvote_certvote1 : (**r deliver a softvote and cert-vote for the value (committee member case) *)
    forall uid (pre : UState) r p i v b,
      let pre' := set_softvotes pre r p (i, v) in
        certvote_ok pre' uid v b r p ->
        uid # pre ; mkMsg Softvote (val v) r p i ~> (certvote_result pre', [:: mkMsg Certvote (val v) r p uid])

| deliver_nextvote_open : (**r deliver a nextvote for bottom while not triggering any internal action *)
    forall uid (pre : UState) r p s i,
      let pre' := set_nextvotes_open pre r p s i in
      (* ~ nextvote_open_ok pre' v r p s -> *)
      ~ adv_period_open_ok pre' r p s ->
      uid # pre ; mkMsg Nextvote_Open (step_val s) r p i ~> (pre', [::])

| deliver_nextvote_open_adv_prd : (**r deliver a nextvote for bottom and advance the period *)
    forall uid (pre : UState) r p s i,
      let pre' := set_nextvotes_open pre r p s i in
        adv_period_open_ok pre' r p s ->
        uid # pre ; mkMsg Nextvote_Open (step_val s) r p i ~> (adv_period_open_result pre', [::])

| deliver_nextvote_val : (**r deliver a nextvote for value while not triggering any internal action *)
    forall uid (pre : UState) r p s i v,
      let pre' := set_nextvotes_val pre r p s (i, v) in
        ~ adv_period_val_ok pre' v r p s ->
        uid # pre ; mkMsg Nextvote_Val (next_val v s) r p i ~> (pre', [::])

| deliver_nextvote_val_adv_prd : (**r deliver a nextvote for value and advance the period *)
    forall uid (pre : UState) r p s i v,
      let pre' := set_nextvotes_val pre r p s (i, v) in
      adv_period_val_ok pre' v r p s ->
      uid # pre ; mkMsg Nextvote_Val (next_val v s) r p i ~> (adv_period_val_result pre' v, [::])

| deliver_certvote : (**r deliver a certvote while not triggering any internal action *)
    forall uid (pre : UState) v r p i,
      let pre' := set_certvotes pre r p (i, v) in
      ~ certify_ok pre' v r p ->
      uid # pre ; mkMsg Certvote (val v) r p i ~> (pre', [::])

| deliver_certvote_adv_rnd : (**r deliver a certvote for value and advance the round *)
    forall uid (pre : UState) v r p i,
      let pre' := set_certvotes pre r p (i, v) in
        certify_ok pre' v r p ->
        uid # pre ; mkMsg Certvote (val v) r p i ~> (certify_result r pre', [::])
(** Note that some Algorand documents say this transition may try to
send another certvote message from this node, but we have been
informed that the implementation does not do this,
and allowing it would complicated proofs. *)
| deliver_nonvote_msg : (**r deliver a message other than vote messages (i.e., [Block], [Proposal], or [Reproposal]) *)
    forall uid (pre : UState) msg c r p,
      ~ vote_msg msg ->
      uid # pre ; msg ~> (deliver_nonvote_msg_result pre msg c r p, [::])

where "a # b ; c ~> d" := (UTransitionMsg a b c d) : type_scope.

(** ** Helper functions for global transitions *)

(** Is the network in a partitioned/unpartitioned state? *)
Definition is_partitioned pre : bool := pre.(network_partition).
Definition is_unpartitioned pre : bool := ~~ is_partitioned pre.

(** It is OK to advance time if:
- the user is corrupt (its deadline is irrelevant), or
- the increment does not go beyond the deadline. *)
Definition user_can_advance_timer (increment : posreal) : pred UState :=
  fun u => u.(corrupt) || Rleb (u.(timer) + pos increment) u.(deadline).

(** Advance the timer of an honest user (timers of corrupt users are irrelevant). *)
Definition user_advance_timer (increment : posreal) (u : UState) : UState :=
  if ~~ u.(corrupt)
  then u <| timer := (u.(timer) + pos increment)%R |>
  else u.

(** Is it OK to advance timers of all (honest) users by the given increment? *)
Definition tick_ok_users increment (pre:GState) : bool :=
  allf (user_can_advance_timer increment) pre.(users).

(** It is OK to advance time if:
- the network is partitioned (message delivery delays are ignored), or
- the time increment does not cause missing a message delivery deadline.
 *)
Definition tick_ok_msgs (increment:posreal) (pre:GState) : bool :=
  is_partitioned pre ||
  let target_time := (pre.(now) + pos increment)%R in
  \big[andb/true]_(user_msgs <- codomf pre.(msg_in_transit))
   \big[andb/true]_(m <- (enum_mset user_msgs)) Rleb target_time (fst m).

(** Returns whether time may advance, taking into consideration the state of
the network, users, their deadlines and message deadlines. *)
Definition tick_ok (increment:posreal) (pre:GState) : bool :=
  tick_ok_users increment pre && tick_ok_msgs increment pre.

(** Advance all (honest) user timers by the given increment. *)
Definition tick_users increment pre : {fmap UserId -> UState} :=
  updf pre.(users) (domf pre.(users)) (fun _ us => user_advance_timer increment us).

(** Computes the global state after advancing time with the given increment. *)
Definition tick_update increment pre : GState :=
  pre <| now := (pre.(now) + pos increment)%R |>
      <| users := tick_users increment pre |>.

(** Computes the standard deadline of a message based on its type. *)
Definition msg_deadline (msg : Msg) now : R :=
  match msg_type msg with
  | Block => (now + lambda + big_lambda)%R
  | _ => (now + lambda)%R
  end.

Definition merge_msgs_deadline (now : R) (msgs : seq Msg) (v : {mset R * Msg}) : {mset R * Msg} :=
  seq_mset [seq (msg_deadline msg now,msg) | msg <- msgs] `+` v.

Definition send_broadcasts_def (now : R) (targets : {fset UserId}) (prev_msgs : MsgPool) (msgs : seq Msg) : MsgPool :=
  updf prev_msgs targets (fun _ => merge_msgs_deadline now msgs).

Definition send_broadcasts_key : unit.
Proof. exact: tt. Qed.

Definition send_broadcasts := locked_with send_broadcasts_key send_broadcasts_def.
Canonical send_broadcasts_unlockable := [unlockable fun send_broadcasts].

(** Returns [true] if [P] is true at nth element in path [p]. *)
Definition at_step n (p : seq GState) (P : pred GState) : bool :=
  match drop n p with
  | g :: _ => P g
  | [::] => false
  end.

(** Returns [true] if the given user id is found in the map and the user state
corresponding to that id is for a corrupt user. *)
Definition is_user_corrupt (uid : UserId) (users : {fmap UserId -> UState}) : bool :=
  if users.[? uid] is Some u then u.(corrupt) else false.

Definition is_user_corrupt_gstate (uid : UserId) (g : GState) : bool :=
  is_user_corrupt uid (g.(users)).

Definition user_honest (uid:UserId) (g:GState) : bool :=
  if g.(users).[? uid] is Some ustate then ~~ (ustate.(corrupt)) else false.

Definition user_honest_at ix p (uid : UserId) : bool :=
  at_step ix p (user_honest uid).

(** Returns the given users map restricted to honest users only. *)
Definition honest_users (users : {fmap UserId -> UState}) :=
  let corrupt_ids := [fset x in domf users | is_user_corrupt x users] in
  users.[\ corrupt_ids].

(** Computes the global state after a message delivery, given the result of the
user transition and the messages sent out. Note:

- the delivered message is removed from the user's mailbox, and
- broadcasts new messages to honest users only.
 *)
Definition delivery_result pre uid (uid_has_mailbox : uid \in pre.(msg_in_transit)) delivered ustate_post (sent: seq Msg) : GState :=
  let users' := pre.(users).[uid <- ustate_post] in
  let user_msgs' := (pre.(msg_in_transit).[uid_has_mailbox] `\ delivered)%mset in
  let msgs' := send_broadcasts pre.(now) (domf (honest_users pre.(users)) `\ uid)
                              pre.(msg_in_transit).[uid <- user_msgs'] sent in
  let msgh' := (pre.(msg_history)  `+` (seq_mset sent))%mset in
  pre <| users          := users' |>
      <| msg_in_transit := msgs'  |>
      <| msg_history    := msgh'  |>.

Arguments delivery_result : clear implicits.

(** Computes the global state after an internal user-level transition
given the result of the user transition and the messages sent out. *)
Definition step_result pre uid ustate_post (sent: seq Msg) : GState :=
  let users' := pre.(users).[uid <- ustate_post] in
  let msgs' := send_broadcasts pre.(now) (domf (honest_users pre.(users)) `\ uid)
                               pre.(msg_in_transit) sent in
  let msgh' := (pre.(msg_history)  `+` (seq_mset sent))%mset in
  pre <| users          := users' |>
      <| msg_in_transit := msgs'  |>
      <| msg_history    := msgh'  |>.

Definition new_deadline now cur_deadline msg : R :=
  let max_deadline := msg_deadline msg now in
  Rmax cur_deadline max_deadline.

(** Resets the deadline of a message having a missed deadline. *)
Definition reset_deadline now (msg : R * Msg) : R * Msg :=
  (new_deadline now msg.1 msg.2, msg.2).

Definition map_mset {A B : choiceType} (f : A -> B) (m : {mset A}) : {mset B} :=
  seq_mset (map f m).

(** Recursively resets message deadlines of all the messages given. *)
Definition reset_user_msg_delays msgs now : {mset R * Msg} :=
  map_mset (reset_deadline now) msgs.

(** Constructs a message pool with all messages having missed delivery deadlines
updated appropriately based on the message type. *)
Definition reset_msg_delays (msgpool : MsgPool) now : MsgPool :=
  updf msgpool (domf msgpool) (fun _ msgs => reset_user_msg_delays msgs now).

(** Postpones the deadline of a message (extending its delivery delay). *)
Definition extend_deadline r (msgs : {mset R * Msg}) (msg : R * Msg) : {mset R * Msg} :=
  let ext_deadline := (fst msg + r)%R in
  (msgs `+` [mset (ext_deadline, msg.2)])%mset.

(** Computes the state resulting from getting partitioned.
Note that this no longer injects extended message delays (see the [tick] rule). *)
Definition make_partitioned (pre:GState) : GState :=
  flip_partition_flag pre.

(** Computes the state resulting from recovering from a partition. *)
Definition recover_from_partitioned pre : GState :=
  let msgpool' := reset_msg_delays pre.(msg_in_transit) pre.(now) in
  (flip_partition_flag pre) <| msg_in_transit := msgpool' |>.

(** Marks a user state corrupted by setting the corrupt flag. *)
Definition make_corrupt ustate : UState :=
  ustate <| corrupt := true |>.

(** Drop the set of messages targeted for a specific user from the given
message map. *)
Definition drop_mailbox_of_user uid (msgs : MsgPool) : MsgPool :=
  if msgs.[? uid] is Some mailbox then msgs.[uid <- mset0] else msgs.

(** Computes the state resulting from corrupting a user.
The user will have its corrupt flag (in its local state) set to [true]
and his mailbox in the global state removed. *)
Definition corrupt_user_result (pre : GState) (uid : UserId)
 (ustate_key : uid \in pre.(users)) : GState :=
  let ustate' := make_corrupt pre.(users).[ustate_key] in
  let msgs' := drop_mailbox_of_user uid  pre.(msg_in_transit) in
  let users' := pre.(users).[uid <- ustate'] in
  pre <| users := users' |> <| msg_in_transit := msgs' |>.

(** Computes the state resulting from replaying a message to a user.
The message is replayed to the given target user and added to his mailbox.
It is not broadcast because other users have already seen the original. *)
Definition replay_msg_result (pre : GState) (uid : UserId) (msg : Msg) : GState :=
  let msgs' := send_broadcasts pre.(now) [fset uid] pre.(msg_in_transit) [:: msg] in
  pre <| msg_in_transit := msgs' |>.

(** Does the adversary have the keys of the user for the given r-p-s?
The adversary will have the keys if the user is corrupt and the given
r-p-s comes after (or is equal to) the r-p-s of the user. *)
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

(** Computes the state resulting from forging a message to a user.
The message is first created and then queued at the target user's mailbox *)
Definition forge_msg_result (pre : GState) (uid : UserId) r p mtype mval : GState :=
  let msg := mkMsg mtype mval r p uid in
  let msgs' := send_broadcasts pre.(now) (domf (honest_users pre.(users)))
                 pre.(msg_in_transit) [:: msg] in
  pre <| msg_in_transit := msgs' |>.

(** ** Global transition relation *)

(** Global transition relation type. *)
Definition g_transition_type := relation GState.

Reserved Notation "x ~~> y" (at level 90).

(** Note that corrupt user deadlines are ignored, and
when partitioned, message delivery delays are ignored.
This means that the adversary action to inject extended
message delays is modeled by [step_tick] ignoring message
delivery deadlines when partitioned. *)
Inductive GTransition : g_transition_type :=
| step_tick : (**r advance the global time *)
    forall increment pre,
    tick_ok increment pre ->
    pre ~~> tick_update increment pre

| step_deliver_msg : (**r deliver a message to a user (honest users only) *)
   forall pre uid (msg_key : uid \in pre.(msg_in_transit)) pending,
    pending \in pre.(msg_in_transit).[msg_key] ->
    forall (key_ustate : uid \in pre.(users)) ustate_post sent,
      ~ pre.(users).[key_ustate].(corrupt) ->
      uid # pre.(users).[key_ustate] ; snd pending ~> (ustate_post, sent) ->
      pre ~~> delivery_result pre uid msg_key pending ustate_post sent

| step_internal : (**r progress based on an internal step of a user (honest users only) *)
    forall pre uid (ustate_key : uid \in pre.(users)),
      ~ pre.(users).[ustate_key].(corrupt) ->
      forall ustate_post sent,
        uid # pre.(users).[ustate_key] ~> (ustate_post, sent) ->
        pre ~~> step_result pre uid ustate_post sent

| step_exit_partition : (**r recover from a partition *)
    forall pre,
    is_partitioned pre ->
    pre ~~> recover_from_partitioned pre

| step_enter_partition : (**r adversary action: partition the network *)
    forall pre,
    is_unpartitioned pre ->
    pre ~~> make_partitioned pre

| step_corrupt_user : (**r adversary action: corrupt a user *)
    forall pre uid (ustate_key : uid \in pre.(users)),
    ~ pre.(users).[ustate_key].(corrupt) ->
    pre ~~> @corrupt_user_result pre uid ustate_key

| step_replay_msg : (**r adversary action: replay a message seen before *)
    forall pre uid (ustate_key : uid \in pre.(users)) msg,
    ~ pre.(users).[ustate_key].(corrupt) ->
    msg \in pre.(msg_history) ->
    pre ~~> replay_msg_result pre uid msg

| step_forge_msg : (**r adversary action: forge and send out a message *)
    forall pre sender (sender_key : sender \in pre.(users))
      r p s mtype mval,
    have_keys pre.(users).[sender_key] r p s ->
    comm_cred_step sender r p s ->
    mtype_matches_step mtype mval s ->
    pre ~~> forge_msg_result pre sender r p mtype mval

where "x ~~> y" := (GTransition x y) : type_scope.

(** ** Reachability for global transition relation *)

(** There is a step at index [n] from [g1] to [g2] along a path [p].
This means that [g1] and [g2] are adjacent elements in the path. *)
Definition step_in_path_at (g1 g2 : GState) n (p : seq GState) : Prop :=
  match drop n p with
  | g1' :: g2' :: _ => [/\ g1' = g1 & g2' = g2]
  | _ => False
  end.

(** Definition of reachable global state via paths. *)
Definition gtransition : rel GState := [rel x y | `[<GTransition x y>] ].

(** A trace starts from [g0] and transitions via [GTransition] at each step in the path [p]. *)
Definition is_trace (g0 : GState) (p : seq GState) : Prop :=
  nosimpl match p with
          | [::] => False
          | [:: g' & rest] => [/\ g0 = g' & path gtransition g0 rest]
          end.

(** Reachability between pairs of states under the reflexive-transitive closure of the transition relation. *)
Definition greachable (g0 g : GState) : Prop := exists2 p, is_trace g0 p & g = last g0 p.

(** Classic definition of reachable global state. *)
Definition GReachable (g0 g : GState) : Prop := clos_refl_trans_1n _ GTransition g0 g.

(** We next prove that the above notions of reachability are equivalent in our setting. *)

(** Our definition of reachability implies the classic definition of reachable states. *)
Lemma greachable_GReachable : forall g0 g, greachable g0 g -> GReachable g0 g.
Proof.
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

(** Classic definition of reachable states implies our definition of reachable states. *)
Lemma GReachable_greachable : forall g0 g, GReachable g0 g -> greachable g0 g.
Proof.
  move => g0 g.
  elim. move => x; exists [:: x]; done.
  move => x y z Hxy Hc.
  case => p Hp Hl.
  unfold is_trace in Hp.
  destruct p. contradiction.
  destruct Hp as [Hy Hp].
  exists (x :: y :: p) => //=; last by subst.
  unfold is_trace; split; first by [].
  apply/andP.
    by split => //; apply/asboolP.
Qed.

(** ** Labeling global transitions *)

(** Labels to classify transitions more abstractly. *)
Inductive GLabel : Type :=
| lbl_tick :  posreal -> GLabel
| lbl_deliver : UserId -> R -> Msg -> seq Msg -> GLabel
| lbl_step_internal : UserId -> seq Msg -> GLabel
| lbl_exit_partition : GLabel
| lbl_enter_partition : GLabel
| lbl_corrupt_user : UserId -> GLabel
| lbl_replay_msg : UserId -> GLabel
| lbl_forge_msg : UserId -> nat -> nat -> MessageType -> ExValue -> GLabel.

(** Specify when labels classify a transition between pairs of global states. *)
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
