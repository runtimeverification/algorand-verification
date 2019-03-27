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
Require Import Interval.Interval_tactic.

From Algorand
Require Import Rstruct fmap_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** General Description of Assumptions in the Model
 **

We generally list the assumptions made in this version of the model so far:

- The set of users (identified by UserId) is finite
- The set of values (Value) is finite
- The system state gives each node its own clock but for now any transitions
  that advance clocks will advance all the same amount
- Deadlines are defined only for message delivery delays (local user actions
  are instantaneous)
- Messages are all broadcast messages. Network topologies are abstracted away
  (no peer-to-peer channels). A user may broadcast a message, which may reach
  all (honest) users at different times (guaranteed to arrive within the given
  time bounds in the absence of network partitions).
- We abstract over cyptographic and probabilistic computations (we assume
  perfect cryptographic schemes, and probabilistic transitions are modeled as
  non-deterministic transitions
- We abstract over nonces that are assumed to be produced by an Oracle and assume
  that randomness is unbiasable
- Credentials are modeled by abstract totally ordered types (the interpretation
  of a cedential as an unsigned integer is not needed)

**
**)

(* Union two fmaps, using a combining function when both have a value for a key *)
Definition catf_with {V : Type} (f : V -> V -> V) {K:choiceType} : {fmap K -> V} -> {fmap K -> V} -> {fmap K -> V}.
  refine (fun m1 m2 => [fmap x : (domf m1 `|` domf m2) => _]).
  (*  SearchAbout fnd. *)
  change (if true then V else unit).
  replace true with (m1.[? val x] || m2.[?val x]).
  Focus 2.
  pose proof (valP x).
  rewrite in_fsetU in H.
  rewrite fndSome; rewrite fndSome.
  assumption.
  refine(
                match m1.[? val x] as r1, m2.[? val x] as r2 return if r1 || r2 then V else unit with
                | Some v1, Some v2 => f v1 v2
                | Some v1, None => v1
                | None, Some v2 => v2
                | None, None => tt
                end).
Defined.

(* Some proofs about the model use lemmas that
   do not refer to model types, and only show
   properties of library types *)
Section UtilLemmas.
Lemma Forall_map : forall A B (f : A -> B) (P : B -> Prop) l,
    List.Forall (fun a => P (f a)) l -> List.Forall P (map f l).
Proof.
  intros A B f P.
  induction l.
  simpl.
  intro. constructor.
  simpl.
  inversion 1; subst.
  constructor;solve[auto].
Qed.

Lemma Forall_impl2 : forall A (P Q R : A -> Prop),
    (forall a, P a -> Q a -> R a) ->
    forall l, List.Forall P l -> List.Forall Q l -> List.Forall R l.
Proof.
  intros A P Q R Himpl.
  induction l.
  intros;constructor.
  inversion 1;subst. inversion 1;subst. constructor;solve[auto].
Qed.

Lemma Rle_pos_r : forall x y p,
    (x <= y -> x <= y + pos p)%R.
Proof.
  intros x y p Hxy.
  apply Rle_trans with (y + 0)%R.
  rewrite Rplus_0_r;assumption.
  clear x Hxy.
  apply Rplus_le_compat_l, Rlt_le, cond_pos.
Qed.
End UtilLemmas.

Section AlgoModel.


(* We first define a user's state structure *)
(* Note: these definitions follow quite closely the ones given by Victor
   in his automaton model of the system. We may stick to those or refine/abstract
   over some of the details as we move on.
*)

(* We assume a finite set of users *)
Variable UserId : finType.

(* And a finite set of values (blocks and block hashes) *)
Variable Value : finType .

(* An abstract representation of computing block hashes *)
(* Variable hash : Value -> Value . *)

(* An enumerated data type of all possible kinds of messages
*)
Inductive MType :=
  | Block
  | Proposal
  | Reproposal
  | Softvote
  | Certvote
  | Nextvote_Open
  | Nextvote_Val.

(* Make MType a finType by showing an isomorphism
   with the ssreflect bounded nat type 'I_7 *)
Definition mtype2o (m:MType) : 'I_7 :=
 inord  match m with
  | Block => 0
  | Proposal => 1
  | Reproposal => 2
  | Softvote => 3
  | Certvote => 4
  | Nextvote_Open => 5
  | Nextvote_Val => 6
  end.
Definition o2mtype (i:'I_7) : option MType :=
  match val i in nat with
  | 0 => Some Block
  | 1 => Some Proposal
  | 2 => Some Reproposal
  | 3 => Some Softvote
  | 4 => Some Certvote
  | 5 => Some Nextvote_Open
  | 6 => Some Nextvote_Val
  | _ => None
  end.
Lemma pcancel_MType_7 : pcancel mtype2o o2mtype.
Proof. by case;rewrite /o2mtype /= inordK. Qed.

Canonical mtype_eqType     := EqType     MType (PcanEqMixin     pcancel_MType_7).
Canonical mtype_choiceType := ChoiceType MType (PcanChoiceMixin pcancel_MType_7).
Canonical mtype_countType  := CountType  MType (PcanCountMixin  pcancel_MType_7).
Canonical mtype_finType    := FinType    MType (PcanFinMixin    pcancel_MType_7).

(* None means the value bottom *)
Definition MaybeValue := option Value.

(* Not sure if we will ever need this, but these are the strucutres used as values in
   messages in Victor's paper
*)
Inductive ExValue :=
  | val      : MaybeValue -> ExValue
  | step_val : nat -> ExValue
  | repr_val : Value -> UserId -> nat -> ExValue
  | next_val : Value -> nat -> ExValue.

Definition codeExVal (e:ExValue) :
  option Value + nat + (Value * UserId * nat) + (Value * nat) :=
  match e with
  | val mv => inl (inl (inl mv))
  | step_val k => inl (inl (inr k))
  | repr_val v user n => inl (inr (v, user, n))
  | next_val v n => inr (v,n)
  end.
Definition decodeExVal
           (c:option Value + nat + (Value * UserId * nat) + (Value * nat))
           : ExValue :=
  match c with
  | inl (inl (inl mv)) => val mv
  | inl (inl (inr k)) => step_val k
  | inl (inr (v, user, n)) => repr_val v user n
  | inr (v,n) => next_val v n
  end.
Lemma cancelExVal : pcancel codeExVal (fun x => Some (decodeExVal x)).
Proof. case;reflexivity. Qed.

Canonical exvalue_eqType     := EqType     ExValue (PcanEqMixin     cancelExVal).
Canonical exvalue_choiceType := ChoiceType ExValue (PcanChoiceMixin cancelExVal).
Canonical exvalue_countType  := CountType  ExValue (PcanCountMixin  cancelExVal).

(* A message type as a product type *)
Definition Msg : Type := MType * ExValue * nat * nat * UserId.

(* Alternatively, we could construct a message as a more elaborate record ??)
Record Msg :=
  mkMsg {
    type : MType ;
    val : Value ;
    round: nat ;
    period : nat ;
    user : UserId
  }.
*)

(* Messages are grouped by target.
   We do not need to remember the sender, everything only
   depends on which keys signed parts of the message.

   Messages are paired with a delivery deadline.
   In the absence of a partition, messages must be
   delivered before the deadline is reached.
 *)
Definition MsgPool := {fmap UserId -> {mset R * Msg}}%mset.

(* The credential of a User at a round-period-step triple *)
(* Note: We abstract away the random value produced by an Oracle *)
(* and the fact that credentials are interpreted as integer *)
(* values. Instead, we model the type of credentials as an *)
(* abstract totally ordered type. *)

Variable credType : orderType tt.

Variable credential : UserId -> nat -> nat -> nat -> credType.

Hypothesis credentials_different :
  forall (u u' : UserId) (r r' : nat) (p p' : nat) (s s' : nat),
  u <> u' -> credential u r p s <> credential u' r' p' s'.

(*
Inductive Credential :=
  | cred : UserId -> nat -> nat -> nat -> Credential.
*)

(* A proposal/preproposal record is a triple consisting of two
   values along with a boolean indicating whether this is
   a proposal (true) or a reproposal (false)
*)

Definition PropRecord := (credType * Value * bool)%type.

(* A vote is a pair of UserID and Value *)
Definition Vote := (UserId * Value)%type.

(* Constructors for the different steps in a period
*)
Inductive StepName :=
  | Proposing
  | Softvoting
  | Certvoting
  | Nextvoting .

(** And now the state of a user
    Note: again we may end up not using all of these fields (and there may
    be others we may want to add later)
    Note: We probably don't need to maintain deadline in the user state as
    it is a function of the current step. Also, deadline no longer needs to
    be an option type(?).
**)
Record UState :=
  mkUState {
    (* The user's unique identifier *)
    id            : UserId;
    (* A flag indicating whether the user is controlled by the attacker *)
    corrupt       : bool;
    (* The user's current round (starts at 1) *)
    round         : nat;
    (* The user's current period (starts at 1) *)
    period        : nat;
    (* The user's current step counter (starts at 1) *)
    step          : nat;
    (* The user's current step name (Proposing, Softvoting, ... etc) *)
    (* No longer needed -- replaced with a function *)
    (* step_name     : StepName; *)
    (* The user's current timer value (since the beginning of the current period) *)
    timer         : R;
    (* The user's next deadline time value (relative to beginning of first round) *)
    deadline      : option R;
    (* The (local) time at which the user's current period started (i.e. local clock = p_start + timer *)
    p_start       : R;
    (* unused -- will probably be dropped *)
    rec_msgs      : seq Msg;
    (* A sequence of proposal/reproposal records for the given round/period *)
    proposals     : nat -> nat -> seq PropRecord;
    (* A sequence of values seen for the given round/period *)
    blocks        : nat -> nat -> seq Value;
    (* A sequence of softvotes seen for the given round/period *)
    softvotes     : nat -> nat -> seq Vote;
    (* Need to maintain steps (??) *)
    (* A sequence of certvotes seen for the given round/period *)
    certvotes     : nat -> nat -> seq Vote;
    (* A sequence of bottom-nextvotes seen for the given round/period/step *)
    nextvotes_open: nat -> nat -> nat -> seq Vote;
    (* A sequence of value-nextvotes seen for the given round/period/step *)
    nextvotes_val : nat -> nat -> nat -> seq Vote;
    (* A flag for a given round and period indicating whether the preconditions
       of certvoting in step 3 were satisfied at the time of step 3, regardless
       of whether the user was actually in the committee of that step *)
    has_certvoted : nat -> nat -> bool;
    (* A sequence of values with high enough softvotes for for the given round/period *)
    (* i.e. the set of values in softvotes r p having more votes than the threshold *)
    (* No longer used: replaced by the function certvals *)
    (*   certvals      : nat -> nat -> seq Value; *)
    (* A sequence of values certified for in the last period *)
    (* (so prev_certvals = (certvals current_round previous_period)) *)
    (* No longer used: replaced by the function prev_certvals *)
    (*   prev_certvals : seq Value; *)
    (* A flag indicating whether the user has already certified a value in the previous period (current round) *)
    (* (i.e. whether prev_certvals of last period is non-empty) *)
    (* No longer used: replaced by the function cert_may_exist *)
    (*   cert_may_exist: bool; *)
  }.

(*
  {|
    id             := u.(id);
    corrupt        := u.(corrupt);
    round          := u.(round);
    period         := u.(period);
    step           := u.(step);
    timer          := u.(timer);
    deadline       := u.(deadline);
    p_start        := u.(p_start);
    rec_msgs       := u.(rec_msgs);
    proposals      := u.(proposals);
    blocks         := u.(blocks);
    softvotes      := u.(softvotes);
    certvotes      := u.(certvotes);
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := u.(nextvotes_val);
    has_certvoted  := u.(has_certvoted);
   |}.
 *)

Definition update_step (u : UState) step' : UState :=
  {|
    id             := u.(id);
    corrupt        := u.(corrupt);
    round          := u.(round);
    period         := u.(period);
    step           := step';
    timer          := u.(timer);
    deadline       := u.(deadline);
    p_start        := u.(p_start);
    rec_msgs       := u.(rec_msgs);
    proposals      := u.(proposals);
    blocks         := u.(blocks);
    softvotes      := u.(softvotes);
    certvotes      := u.(certvotes);
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := u.(nextvotes_val);
    has_certvoted  := u.(has_certvoted);
  |}.

Definition update_timer (u : UState) timer' : UState :=
  {|
    id             := u.(id);
    corrupt        := u.(corrupt);
    round          := u.(round);
    period         := u.(period);
    step           := u.(step);
    timer          := timer';
    deadline       := u.(deadline);
    p_start        := u.(p_start);
    rec_msgs       := u.(rec_msgs);
    proposals      := u.(proposals);
    blocks         := u.(blocks);
    softvotes      := u.(softvotes);
    certvotes      := u.(certvotes);
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := u.(nextvotes_val);
    has_certvoted  := u.(has_certvoted);
  |}.

Definition update_deadline (u : UState) deadline' : UState :=
  {|
    id             := u.(id);
    corrupt        := u.(corrupt);
    round          := u.(round);
    period         := u.(period);
    step           := u.(step);
    timer          := u.(timer);
    deadline       := deadline';
    p_start        := u.(p_start);
    rec_msgs       := u.(rec_msgs);
    proposals      := u.(proposals);
    blocks         := u.(blocks);
    softvotes      := u.(softvotes);
    certvotes      := u.(certvotes);
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := u.(nextvotes_val);
    has_certvoted  := u.(has_certvoted);
   |}.

Definition update_rec_msgs (u : UState) rec_msgs' : UState :=
  {|
    id             := u.(id);
    corrupt        := u.(corrupt);
    round          := u.(round);
    period         := u.(period);
    step           := u.(step);
    timer          := u.(timer);
    deadline       := u.(deadline);
    p_start        := u.(p_start);
    rec_msgs       := rec_msgs';
    proposals      := u.(proposals);
    blocks         := u.(blocks);
    softvotes      := u.(softvotes);
    certvotes      := u.(certvotes);
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := u.(nextvotes_val);
    has_certvoted  := u.(has_certvoted);
   |}.

Definition set_proposals (u : UState) r' p' prop : UState :=
  {|
    id             := u.(id);
    corrupt        := u.(corrupt);
    round          := u.(round);
    period         := u.(period);
    step           := u.(step);
    timer          := u.(timer);
    deadline       := u.(deadline);
    p_start        := u.(p_start);
    rec_msgs       := u.(rec_msgs);
    proposals      := fun r p => if (r, p) == (r', p')
                                 then prop :: u.(proposals) r p
                                 else u.(proposals) r p;
    blocks         := u.(blocks);
    softvotes      := u.(softvotes);
    certvotes      := u.(certvotes);
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := u.(nextvotes_val);
    has_certvoted  := u.(has_certvoted);
   |}.

Definition set_blocks (u : UState) r' p' block : UState :=
  {|
    id             := u.(id);
    corrupt        := u.(corrupt);
    round          := u.(round);
    period         := u.(period);
    step           := u.(step);
    timer          := u.(timer);
    deadline       := u.(deadline);
    p_start        := u.(p_start);
    rec_msgs       := u.(rec_msgs);
    proposals      := u.(proposals);
    blocks         := fun r p => if (r, p) == (r', p')
                                 then block :: u.(blocks) r p
                                 else u.(blocks) r p;
    softvotes      := u.(softvotes);
    certvotes      := u.(certvotes);
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := u.(nextvotes_val);
    has_certvoted  := u.(has_certvoted);
   |}.

Definition set_softvotes (u : UState) r' p' sv : UState :=
  {|
    id             := u.(id);
    corrupt        := u.(corrupt);
    round          := u.(round);
    period         := u.(period);
    step           := u.(step);
    timer          := u.(timer);
    deadline       := u.(deadline);
    p_start        := u.(p_start);
    rec_msgs       := u.(rec_msgs);
    proposals      := u.(proposals);
    blocks         := u.(blocks);
    softvotes      := fun r p => if (r, p) == (r', p')
                                 then sv :: u.(softvotes) r p
                                 else u.(softvotes) r p;
    certvotes      := u.(certvotes);
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := u.(nextvotes_val);
    has_certvoted  := u.(has_certvoted);
   |}.

Definition set_certvotes (u : UState) r' p' cv : UState :=
  {|
    id             := u.(id);
    corrupt        := u.(corrupt);
    round          := u.(round);
    period         := u.(period);
    step           := u.(step);
    timer          := u.(timer);
    deadline       := u.(deadline);
    p_start        := u.(p_start);
    rec_msgs       := u.(rec_msgs);
    proposals      := u.(proposals);
    blocks         := u.(blocks);
    softvotes      := u.(softvotes);
    certvotes      := fun r p => if (r, p) == (r', p')
                                 then cv :: u.(certvotes) r p
                                 else u.(certvotes) r p;
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := u.(nextvotes_val);
    has_certvoted  := u.(has_certvoted);
   |}.

Definition set_nextvotes_open (u : UState) r' p' s' nvo : UState :=
  {|
    id             := u.(id);
    corrupt        := u.(corrupt);
    round          := u.(round);
    period         := u.(period);
    step           := u.(step);
    timer          := u.(timer);
    deadline       := u.(deadline);
    p_start        := u.(p_start);
    rec_msgs       := u.(rec_msgs);
    proposals      := u.(proposals);
    blocks         := u.(blocks);
    softvotes      := u.(softvotes);
    certvotes      := u.(certvotes);
    nextvotes_open := fun r p s => if (r, p, s) == (r', p', s')
                                   then nvo :: u.(nextvotes_open) r p s
                                   else u.(nextvotes_open) r p s;
    nextvotes_val  := u.(nextvotes_val);
    has_certvoted  := u.(has_certvoted);
   |}.

Definition set_nextvotes_val (u : UState) r' p' s' nvv : UState :=
  {|
    id             := u.(id);
    corrupt        := u.(corrupt);
    round          := u.(round);
    period         := u.(period);
    step           := u.(step);
    timer          := u.(timer);
    deadline       := u.(deadline);
    p_start        := u.(p_start);
    rec_msgs       := u.(rec_msgs);
    proposals      := u.(proposals);
    blocks         := u.(blocks);
    softvotes      := u.(softvotes);
    certvotes      := u.(certvotes);
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := fun r p s => if (r, p, s) == (r', p', s')
                                   then nvv :: u.(nextvotes_val) r p s
                                   else u.(nextvotes_val) r p s;
    has_certvoted  := u.(has_certvoted);
   |}.

Definition set_has_certvoted (u : UState) r' p' b' : UState :=
  {|
    id             := u.(id);
    corrupt        := u.(corrupt);
    round          := u.(round);
    period         := u.(period);
    step           := u.(step);
    timer          := u.(timer);
    deadline       := u.(deadline);
    p_start        := u.(p_start);
    rec_msgs       := u.(rec_msgs);
    proposals      := u.(proposals);
    blocks         := u.(blocks);
    softvotes      := u.(softvotes);
    certvotes      := u.(certvotes);
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := u.(nextvotes_val);
    has_certvoted  := fun r p => if (r, p) == (r', p') then b' else u.(has_certvoted) r p;
   |}.

Definition advance_period (u : UState) : UState :=
  {|
    id             := u.(id);
    corrupt        := u.(corrupt);
    round          := u.(round);
    period         := u.(period) + 1;
    step           := 1;
    timer          := 0%R;
    deadline       := Some 0%R;
    p_start        := u.(p_start) + u.(timer);
    rec_msgs       := u.(rec_msgs);
    proposals      := u.(proposals);
    blocks         := u.(blocks);
    softvotes      := u.(softvotes);
    certvotes      := u.(certvotes);
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := u.(nextvotes_val);
    has_certvoted  := u.(has_certvoted);
   |}.

Definition advance_round (u : UState) : UState :=
  {|
    id             := u.(id);
    corrupt        := u.(corrupt);
    round          := u.(round) + 1;
    period         := 1;
    step           := 1;
    timer          := 0%R;
    deadline       := Some 0%R;
    p_start        := u.(p_start) + u.(timer);
    rec_msgs       := u.(rec_msgs);
    proposals      := u.(proposals);
    blocks         := u.(blocks);
    softvotes      := u.(softvotes);
    certvotes      := u.(certvotes);
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := u.(nextvotes_val);
    has_certvoted  := u.(has_certvoted);
   |}.

(* A proposition for whether a given credential qualifies its
   owner to be a committee member *)
(* Note: This abstract away how credential values are
   interpreted (which is a piece of detail that may not be
   relevant to the model at this stage) *)
(* generalize to round/periods/step *)
Variable committee_cred : credType -> Prop.

Definition comm_cred_step (u : UState) r p s : Prop :=
  committee_cred (credential u.(id) r p s) .

(* Similarly, a proposition for whether a given credential qualifies its
   owner to be a potential leader *)
Variable leader_cred : credType -> Prop.

Definition leader_cred_step (u : UState) r p s : Prop :=
  leader_cred (credential u.(id) r p s) .

(* The basic requirement that a potential leader for a particular round-period-step
   must by defintion be a committee member as well for that round-period-step *)
Hypothesis leader_is_comm_member :
  forall cr : credType, leader_cred cr -> committee_cred cr .


(** The global state **)
Record GState :=
  mkGState {
    (* The current global time value *)
    now               : R;
    (* A flag indicating whether the network is currently partitioned *)
    network_partition : bool;
    (* The global set of users as a finite map of user ids to user states *)
    users             : {fmap UserId -> UState};
    (* A multiset of messages in transit *)
    msg_in_transit    : MsgPool;
  }.

(*
  {| now := g.(now);
     network_partition := g.(network_partition);
     users := g.(users);
     msg_in_transit := g.(msg_in_transit)
  |}.
 *)

Definition update_now (now' : R) (g : GState) : GState :=
  {| now := now';
     network_partition := g.(network_partition);
     users := g.(users);
     msg_in_transit := g.(msg_in_transit)
  |}.

Definition update_users (users' : {fmap UserId -> UState}) (g : GState) : GState :=
  {| now := g.(now);
     network_partition := g.(network_partition);
     users := users';
     msg_in_transit := g.(msg_in_transit)
  |}.

Definition update_msgs_in_transit (msgs' : MsgPool) (g : GState) : GState :=
  {| now := g.(now);
     network_partition := g.(network_partition);
     users := g.(users);
     msg_in_transit := msgs'
  |}.

(* small - non-block - message delivery delay *)
Variable lambda : R.

(* block message delivery delay *)
Variable big_lambda : R.

(* recovery time period L *)
Variable L : R.

(* some other thresholds *)
(* number of soft-votes needed to cert-vote *)
Variable tau_s : nat.

(* number of cert-votes needed for a certificate *)
Variable tau_c : nat.

(* number of next-votes for None to move to next period *)
Variable tau_b : nat.

(* number of next-votes for a proper value to move to next period *)
Variable tau_v : nat.

(* upper bound on the credential to be part of the committee for step s *)
(* this is no longer needed!! *)
(* Variable chi   : nat -> nat. *)


(** Helper functions/propositions for the user-state-level trnasitions **)

(* valid is an abstract proposition on values that tells us whether a value
   is valid *)
Variable valid : Value -> Prop.

(* correct_hash is an abstract proposition on values that tells us whether a
   given hash value is indeed the hash of the given block value *)
Variable correct_hash : Value -> Value -> Prop.

(* The block has been seen and is valid and the given value is indeed its hash
   value *)
Definition valid_block_and_hash (u : UState) b v r p : Prop :=
  valid b /\ correct_hash v b /\ b \in u.(blocks) r p.

(* Returns the name of a given step value if valid, and None otherwise *)
Definition step_name s : option StepName :=
  match s with
  | 0 => None
  | 1 => Some Proposing
  | 2 => Some Softvoting
  | 3 => Some Certvoting
  | _ => Some Nextvoting
  end.

(* Does the given round/period/step match the ones stored in the user state? *)
Definition valid_rps (u : UState) r p w : Prop :=
  u.(round) = r /\ u.(period) = p /\ step_name(u.(step)) = Some w .

(* Is the vote x for this value v? *)
Definition matchValue (x : Vote) (v : Value) : bool :=
  let: (u', v') := x in v == v' .

(* The sequence of all values appearing a given sequence of votes *)
Definition vote_values (vs: seq Vote) : seq Value :=
  [seq x.2 | x <- vs] .

(* The number of softvotes of a given value in a given user state *)
Definition soft_weight (v:Value) (u:UState) : nat :=
  size [seq x <- u.(softvotes) u.(round) u.(period) | matchValue x v] .

(* The sequence of values with high enough softvotes in a given user state for given round and period *)
(* i.e. the sequence of values in softvotes having votes greater than or equal to the threshold *)
Definition certvals (u:UState) r p : seq Value :=
  [seq v <- vote_values (u.(softvotes) r p) | (soft_weight v u) >= tau_s] .
(* invariant: size should be <= 1 *)

(* The sequence of values certified for in the last period as seen by the given user *)
(* This corresponds to prev_certvals field in the automaton model *)
Definition prev_certvals (u:UState) : seq Value :=
  let p := u.(period) in
    if p > 1 then certvals u u.(round) (p - 1) else [::] .

(* Whether the user has seen enough votes for bottom in the given round/period/step *)
Definition nextvote_bottom_quorum (u:UState) r p s : Prop :=
  size (u.(nextvotes_open) r p s) >= tau_b .

(* Whether the user has seen enough votes for a value in the given round/period/step *)
Definition nextvote_val_quorum (u:UState) r p s : Prop :=
  exists v, size [seq x <- u.(nextvotes_val) r p s | matchValue x v] >= tau_v.

(* Whether the user has already certified a value (based on enough nextvotes) in the previous period
   of the current round (for some step during that period) *)
(* This corresponds to cert_may_exist field in the automaton model *)
(* Notes: - the step s is not specified in the automaton model so the assumption here is that
            step s is existentially quantified
          - the second condition (nextvote_bottom_quorum is never true in the current period) was added
            based on recent discussion
*)
Definition cert_may_exist (u:UState) : Prop :=
  let p := u.(period) in
  let r := u.(round) in
    exists s, nextvote_val_quorum u r (p - 1) s
    /\ forall s, ~ nextvote_bottom_quorum u r p s.

(** Step 1: Proposing propositions and user state update **)

(* The proposal step preconditions *)
(* Note that this covers both: (a) the case when p = 1, and (b)
   the case when p > 1 with the previous period voting for bottom.
   Just as in Victor's model, the fact that the last period's winning
   vote was for a value is captured by the predicate cert_may_exist *)
Definition propose_ok (pre : UState) v r p : Prop :=
  pre.(timer) = 0%R /\
  valid_rps pre r p Proposing /\
  leader_cred_step pre r p 1 /\
  ~ cert_may_exist pre /\
  valid v.

(* The reproposal step preconditions *)
(* Note that this is the proposal step when p > 1 and the previous-
   period's winning vote was for a value v *)
(* Note also that we do not distinguish values from their hashes (for now),
   and so the check that v = hash(B) is not used *)
Definition repropose_ok (pre : UState) v r p : Prop :=
  pre.(timer) = 0%R /\
  valid_rps pre r p Proposing /\ p > 1 /\
  leader_cred_step pre r p 1 /\
  v \in prev_certvals pre.

(* The no-propose step preconditions *)
(* Note that this applies regardless of whether p = 1 *)
Definition no_propose_ok (pre : UState) r p : Prop :=
  pre.(timer) = 0%R /\
  valid_rps pre r p Proposing /\
  ~ leader_cred_step pre r p 1.

(* The proposing step (propose, repropose and nopropose) post-state *)
(* Move on to Softvoting and set the new deadline to 2*lambda *)
Definition propose_result (pre : UState) : UState :=
  update_step
    (update_deadline pre (Some (2 * lambda)%R))
    2.

(** Step 2: Softvoting propositions and user state update **)

(* The Softvoting-a-proposal step preconditions *)
(* Note that this covers both: (a) the case when p = 1, and (b)
   the case when p > 1 with the previous period voting for bottom. *)
(* Notes: - Victor's model has the constraint clock >= 2*lambda
          -  The Algorand2 description includes an additional constraint
            about whether the value is a period-1 value or not
            [TODO: TBA in the specs of the transition relation below] *)
Definition softvote_new_ok (pre : UState) (v : Value) r p : Prop :=
  pre.(timer) = (2 * lambda)%R /\
  valid_rps pre r p Softvoting /\
  comm_cred_step pre r p 2 /\
  ~ cert_may_exist pre /\
  ~ pre.(proposals) r p = [::] . (* so a leader can be identified *)

(* The Softvoting-a-reproposal step preconditions *)
(* Note that this is the Softvoting step when p > 1 and the previous-
   period's winning vote was for a value v *)
(* Notes: - the automaton model includes an additional condition that is not
            explicitly given in the description [TODO: investigate]  *)
Definition softvote_repr_ok (pre : UState) (v : Value) r p : Prop :=
  pre.(timer) = (2 * lambda)%R /\
  valid_rps pre r p Softvoting /\ p > 1 /\
  comm_cred_step pre r p 2 /\
  v \in prev_certvals pre.

(* TODO: The Softvoting-conflict step preconditions *)
(* This seems to be related to the condition mentioned above in softvote_new_ok above *)

(* The softvoting step (new or reproposal) post-state *)
Definition softvote_result (pre : UState) : UState :=
  update_step
    (update_deadline pre (Some (lambda + big_lambda)%R))
    3.

(** Step 3: Certvoting propositions and user state update **)

(* Certvoting step preconditions *)
(* The successful case *)
(* Notes: - Note that this applies for all period values *)
(*        - Corresponds (roughly) to transitions cert_softvotes and certvote in
            the automaton model
          - The condition comm_cred_step is checked outside of this proposition
            to allow distinguishing the two cases of has_certvoted when
            defining the transitions later *)
Definition certvote_ok (pre : UState) (v b: Value) r p : Prop :=
  ((2 * lambda)%R < pre.(timer) < lambda + big_lambda)%R /\
  valid_rps pre r p Certvoting /\
  ~ cert_may_exist pre /\
  valid_block_and_hash pre b v r p /\
  v \in certvals pre r p .

(* Certvoting step preconditions *)
(* The unsuccessful case *)
(* Notes: - Corresponds (roughly) to no_certvote_nocred in the automaton model
          - The Algorand2 description does not explicitly specify what happens in this case
          - The timeout case is handled by a generic timeout transition given later
*)
Definition no_certvote_ok (pre : UState) r p : Prop :=
  ((2 * lambda)%R < pre.(timer) < lambda + big_lambda)%R /\
  valid_rps pre r p Certvoting /\
  nilp (certvals pre r p).

(* Certvoting step's resulting user state (both cases) *)
Definition certvote_result (pre : UState) b : UState :=
  update_step
    (update_deadline
      (set_has_certvoted pre pre.(round) pre.(period) b)
      (Some (lambda + big_lambda)%R)) (* Note: the deadline should already be this value *)
    4.

(** Even Steps >= 4: Nextvoting1 propositions and user state update **)

(* First nextvoting step preconditions *)
(* The proper-value case *)
(* Notes: - Corresponds (roughly) to transition nextvote_val in the automaton model (but not the same) *)
(*        - Corresponds more closely to the Algorand2 description (but with the committee membership constraint) *)
Definition nextvote1_val_ok (pre : UState) (v : Value) r p s : Prop :=
  pre.(timer) = (lambda + big_lambda)%R /\
  valid_rps pre r p Nextvoting /\
  Nat.Even s /\ s >= 4 /\
  comm_cred_step pre r p s /\ (* Note: we use s even here instead of 5 *)
  pre.(has_certvoted) r p.

(* First nextvoting step preconditions *)
(* The bottom-value case *)
(* Notes: - Corresponds (roughly) to transition nextvote_open in the automaton model (but not the same) *)
(*        - Corresponds more closely to the Algorand2 description (but with the committee membership constraint) *)
Definition nextvote1_open_ok (pre : UState) (v : Value) r p s : Prop :=
  pre.(timer) = (lambda + big_lambda)%R /\
  valid_rps pre r p Nextvoting /\
  Nat.Even s /\ s >= 4 /\
  comm_cred_step pre r p s /\
  ~ pre.(has_certvoted) r p /\
  (p = 1 \/ (p > 1 /\ nextvote_bottom_quorum pre r (p - 1) s )) /\
  ~ cert_may_exist pre . (* extra? *)

(* First nextvoting step preconditions *)
(* The aditional special case of using the starting value *)
(* Notes: - Not sure if this is captured in the automaton model *)
(*        - Corresponds more closely to the Algorand2 description (but with additional constraints given explicitly) *)
Definition nextvote1_stv_ok (pre : UState) (v : Value) r p s : Prop :=
  pre.(timer) = (lambda + big_lambda)%R /\
  valid_rps pre r p Nextvoting /\
  Nat.Even s /\ s >= 4 /\
  ~ pre.(has_certvoted) r p /\
  p > 1 /\ ~ nextvote_bottom_quorum pre r (p - 1) s /\
  comm_cred_step pre r p s. (* required (?) *)

(* Nextvoting step state update for odd step s >= 5 (all cases) *)
Definition nextvote1_result (pre : UState) s : UState :=
  update_step
    (update_deadline pre (Some (lambda + big_lambda + (INR s - 3) * L / 2)%R))
    (s + 1) .


(** Odd Steps >= 5: Nextvoting2 propositions and user state update **)

(* Second nextvoting step (Step 5.1) preconditions *)
(* The proper-value case *)
(* Notes: - Corresponds (roughly) to transition nextvote_val in the automaton model (but not the same) *)
(*        - Corresponds more closely to the Algorand2 description (but with the committee membership constraint) *)
Definition nextvote2_val_ok (pre : UState) (v b : Value) r p s : Prop :=
  (lambda + big_lambda <= pre.(timer) < lambda + big_lambda + L)%R /\
  valid_rps pre r p Nextvoting /\
  Nat.Odd s /\ s >= 5 /\
  comm_cred_step pre r p s /\
  valid_block_and_hash pre b v r p /\
  v \in certvals pre r p .

(* Second nextvoting step (Step 5.2) preconditions *)
(* The bottom-value case *)
(* Notes: - Corresponds (roughly) to transition nextvote_open in the automaton model (but not the same) *)
(*        - Corresponds more closely to the Algorand2 description (but with the committee membership constraint) *)
Definition nextvote2_open_ok (pre : UState) (v : Value) r p s : Prop :=
  (lambda + big_lambda <= pre.(timer) < lambda + big_lambda + L)%R /\
  valid_rps pre r p Nextvoting /\
  Nat.Odd s /\ s >= 5 /\
  comm_cred_step pre r p s /\ (* TODO: the step value here should be different from the above case *)
  ~ pre.(has_certvoted) r p /\
  p > 1 /\ nextvote_bottom_quorum pre r (p - 1) 5 /\
  ~ cert_may_exist pre . (* extra? *)

(* [TODO: What about the case when no certvals and not nextvote_bottom_quorum? => timeout?] *)

(* Nextvoting step state update for even step s >= 4 (all cases) *)
Definition nextvote2_result (pre : UState) s : UState :=
  update_step
    (update_deadline pre (Some (lambda + big_lambda + (INR s - 4) * L / 2)%R))
    (s + 1) .

(** Advancing period propositions and user state update **)

(* Preconditions -- The bottom-value case *)
(* Notes: - Corresponds to transition advance_period_open in the automaton model *)
Definition adv_period_open_ok (pre : UState) (v : Value) r p s : Prop :=
  valid_rps pre r p Nextvoting /\
  nextvote_bottom_quorum pre r p s .

(* Preconditions -- The proper value case *)
(* Notes: - Corresponds to transition advance_period_val in the automaton model *)
Definition adv_period_val_ok (pre : UState) (v : Value) r p s : Prop :=
  valid_rps pre r p Nextvoting /\
  size [seq x <- (pre.(nextvotes_val) r p s) | matchValue x v]  >= tau_v .

(* State update -- both cases *)
Definition adv_period_result (pre : UState) : UState := advance_period pre .


(** Advancing round propositions and user state update **)
(* Preconditions *)
(* Notes: - Corresponds to transition certify in the automaton model
          - The requirement valid_rps has been removed since certification
            may happen at any time *)
Definition certify_ok (pre : UState) (v b : Value) r p : Prop :=
  (* valid_rps pre r p Nextvoting /\ *)
  valid_block_and_hash pre b v r p /\
  size [seq x <- pre.(certvotes) r p | matchValue x v] >= tau_c .

(* State update *)
Definition certify_result (pre : UState) : UState := advance_round pre.


(** Timeout transitions **)

(* The timer deadline value for the NEXT step following the given step value *)
Definition next_deadline k : R :=
  match k with
  (* deadline for step 1 *)
  | 0 => 0
  (* deadline for step 2 *)
  | 1 => (2 * lambda)%R
  (* deadline for step 3 *)
  | 2 => (lambda + big_lambda)%R
  | n => if odd n
         (* deadlines for steps 4, 6, ... *)
         then (lambda + big_lambda + (INR n - 4) * L / 2)%R
         (* deadlines for steps 5, 7, ... *)
         else (lambda + big_lambda + (INR n - 3) * L / 2)%R
  end.

(* A user timeouts if a deadline passes while waiting for some external messages
   (observing softvotes or nextvotes in odd steps >= 3) *)
(* Note: This captures the timeout transitions in the automaton model in addition
         to timing out in the repeated steps *)
Definition timeout_ok (pre : UState) : Prop :=
  match pre.(deadline) with
  | Some r => pre.(step) > 1 /\ Nat.odd pre.(step) /\ (pre.(timer) >= r)%R
  | _ => False
  end.

Definition timeout_result (pre : UState) : UState :=
  let s := pre.(step) in
  update_step (update_deadline pre (Some (next_deadline s))) (s + 1) .


(** Message delivery transitions **)

(* TODO: second arg in message is ExValue, need Value out, better way to do this? *)
(* TODO: nextvotes_open is just UserId according to Victor's model *)
(* TODO: nextvotes_open/val don't take in step according to Victor's model *)
Definition deliver_result (pre : UState) (msg : Msg) c r p s : UState :=
  let: pre' := update_rec_msgs pre (msg :: pre.(rec_msgs)) in
  let: type := msg.1.1.1.1 in
  let: ev := msg.1.1.1.2 in
  let: sender := msg.2 in
  match ev with
  | val (Some v) =>
    let: vote := (sender, v) in
    match type with
    | Proposal => set_proposals pre' r p (c, v, true)
    | Reproposal => set_proposals pre' r p (c, v, false)
    | Softvote => set_softvotes pre' r p vote
    | Certvote => set_certvotes pre' r p vote
    | Nextvote_Open => set_nextvotes_open pre' r p s vote
    | Nextvote_Val => set_nextvotes_val pre' r p s vote
    | Blocks => set_blocks pre' r p v
    end
   | _ => pre'
  end.

(** The inductive definition of the user state transition relation **)

(* The transition relation type *)
(* A user transitions from a state, possibly consuming a message, into a post-state
   while emitting a (possibly empty) sequence of outgoing messages *)
Definition u_transition_type := (option Msg * UState) -> (UState * seq Msg) -> Prop.

Reserved Notation "x ~> y" (at level 70).

Inductive UTransition : u_transition_type := (***)
  (* Step 1: Block Proposal *)
  | propose : forall (pre : UState) B r p,
      propose_ok pre B r p ->
      (None, pre) ~> (propose_result pre,
          [:: (Proposal, val (Some B), r, p, pre.(id)) ;
              (Block, val (Some B), r, p, pre.(id))])
          (* the first message should have the hash of the block B *)
  (* Step 1: Block Proposal [Reproposal] *)
  | repropose : forall (pre : UState) v r p,
      repropose_ok pre v r p ->
      (None, pre) ~> (propose_result pre,
          [:: (Reproposal, repr_val v pre.(id) p, r, p, pre.(id)) ;
              (Block, step_val 2, r, p, pre.(id))])
  (* Step 1: Block Proposal [failure] *)
  | no_propose : forall (pre : UState) r p,
      no_propose_ok pre r p ->
      (None, pre) ~> (propose_result pre, [::])
  (* Step 2: Filtering Step *)
  | softvote_new : forall (pre : UState) v r p,
      softvote_new_ok pre v r p ->
      (None, pre) ~> (softvote_result pre,
          [:: (Softvote, val (Some v), r, p, pre.(id))]) (* v needs to come from pre *)
  (* Step 3: Certifying Step [success while being a committee member] *)
  | certvote1 : forall (pre : UState) v b r p,
      certvote_ok pre v b r p -> comm_cred_step pre r p 3 ->
        (None, pre) ~> (certvote_result pre true,
          [:: (Certvote, val (Some v), r, p, pre.(id))])
  (* Step 3: Certifying Step [success while NOT being a committee member] *)
  | certvote2 : forall (pre : UState) v b r p,
      certvote_ok pre v b r p -> ~ comm_cred_step pre r p 3 ->
        (None, pre) ~> (certvote_result pre true, [::])
  (* Step 3: Certifying Step [failure] *)
  | no_certvote : forall (pre : UState) r p,
      no_certvote_ok pre r p ->
      (None, pre) ~> (certvote_result pre false, [::])
  (* Even Steps >= 4: First Finishing Step - i has not cert-voted some v *)
  | nextvote1_open : forall (pre : UState) v r p s,
      nextvote1_open_ok pre v r p s ->
      (None, pre) ~> (nextvote1_result pre pre.(step), [:: (Nextvote_Open, next_val v 5, r, p, pre.(id))]) (* use bottom instead? *)
  (* Even Steps >= 4: First Finishing Step - i has cert-voted some v *)
  | nextvote1_val : forall (pre : UState) v r p s,
      nextvote1_val_ok pre v r p s ->
      (None, pre) ~> (nextvote1_result pre pre.(step), [:: (Nextvote_Val, step_val 4, r, p, pre.(id))])
  (* Even Steps >= 4: First Finishing Step - special case of using stv *)
  | nextvote1_stv : forall (pre : UState) v r p s,
      nextvote1_stv_ok pre v r p s ->
      (None, pre) ~> (nextvote1_result pre pre.(step), [:: (Nextvote_Val, step_val 4, r, p, pre.(id))])
  (* Odd Steps >= 5: Second Finishing Step - i has cert-voted some v *)
  | nextvote2_val : forall (pre : UState) v b r p s,
      nextvote2_val_ok pre v b r p s ->
      (None, pre) ~> (nextvote2_result pre pre.(step), [:: (Nextvote_Val, step_val 4, r, p, pre.(id))])
  (* Odd Steps >= 5: Second Finishing Step - special case of using stv *)
  | nextvote2_open : forall (pre : UState) v r p s,
      nextvote2_open_ok pre v r p s ->
      (None, pre) ~> (nextvote2_result pre pre.(step), [:: (Nextvote_Val, step_val 4, r, p, pre.(id))])
  (* Advance period (based on too many bottom-value votes) *)
  | adv_period_open : forall (pre : UState) v r p s,
      adv_period_open_ok pre v r p s ->
      (None, pre) ~> (adv_period_result pre, [::])
  (* Advance period (based on enough non-bottom-value votes) *)
  | adv_period_val : forall (pre : UState) v r p s,
      adv_period_val_ok pre v r p s ->
      (None, pre) ~> (adv_period_result pre, [::])
  (* Advance rounds - TODO: no broadcast in the automaton model *)
  | certify : forall (pre : UState) v b r p,
      certify_ok pre v b r p ->
      (None, pre) ~> (certify_result pre, [:: (Certvote, val (Some v), r, p, pre.(id))])
  (* Deliver - only transition that consumes messages *)
  | deliver : forall (pre : UState) msg c r p s,
      (Some msg, pre) ~> (deliver_result pre msg c r p s, [::])
  (* Timeout transitions -- Applies to odd steps > 1 *)
  | timeout : forall (pre : UState),
      timeout_ok pre ->
      (None, pre) ~> (timeout_result pre, [::])
where "x ~> y" := (UTransition x y) : type_scope .



(* Global transition relation type *)
Definition g_transition_type := relation GState .

Definition user_can_advance_timer (increment : posreal) : pred UState :=
  fun u => if u.(deadline) is Some d then Rleb (u.(timer) + pos increment) d else true.

Definition user_advance_timer (increment : posreal) (u : UState) : UState :=
  update_timer u (u.(timer) + pos increment)%R.

Definition tick_ok_users increment (pre:GState) : bool :=
  \big[andb/true]_(uid <- domf pre.(users))
   (* we can't use codomf without making UState a choiceType *)
   (if pre.(users).[? uid] is Some ustate then user_can_advance_timer increment ustate else true).
Definition tick_ok_msgs (increment:posreal) (pre:GState) : bool :=
  let target_time := (pre.(now) + pos increment)%R in
  \big[andb/true]_(user_msgs <- codomf pre.(msg_in_transit))
    \big[andb/true]_(m <- enum_mset user_msgs) Rleb target_time (fst m).
Definition tick_ok (increment:posreal) (pre:GState) : bool :=
  tick_ok_users increment pre && tick_ok_msgs increment pre.

Definition tick_users increment pre : {fmap UserId -> UState} :=
  \big[(@catf _ _)/[fmap]]_(i <- domf pre.(users))
   (if pre.(users).[? i] is Some us then [fmap].[i <- user_advance_timer increment us] else [fmap]).

Definition tick_update increment pre :=
  pre.(update_now (pre.(now) + pos increment)%R)
  .(update_users (tick_users increment pre)).

Definition send_broadcast (targets:{fset UserId}) (deadline : R)
           (prev_msgs:MsgPool) (msg: Msg) : MsgPool :=
  catf_with msetU prev_msgs [fmap x : targets => [mset (deadline, msg)]].

Definition send_broadcasts (targets:{fset UserId}) (deadline : R)
           (prev_msgs:MsgPool) (msgs: seq Msg) : MsgPool :=
  foldl (send_broadcast targets deadline) prev_msgs msgs.

(* Computes the global state after a message delivery,
   given the result of the user transition *)
Definition delivery_result pre uid (uid_has_mailbox : uid \in pre.(msg_in_transit)) delivered ustate_post (sent: seq Msg) : GState :=
  let users' := pre.(users).[uid <- ustate_post] in
  let user_msgs' := (pre.(msg_in_transit).[uid_has_mailbox] `\ delivered)%mset in
  let msgs' := send_broadcasts (domf (pre.(users)) `\ uid) (pre.(now)+lambda)%R
                     pre.(msg_in_transit).[uid <- user_msgs'] sent in
  pre.(update_users users').(update_msgs_in_transit msgs').
Arguments delivery_result : clear implicits.

Definition step_result pre uid ustate_post (sent: seq Msg) : GState :=
  let users' := pre.(users).[uid <- ustate_post] in
  let msgs' := send_broadcasts (domf (pre.(users)) `\ uid) (pre.(now)+lambda)%R
                               pre.(msg_in_transit) sent in
  pre.(update_users users').(update_msgs_in_transit msgs').

(* The global transition relation *)

Reserved Notation "x ~~> y" (at level 90).

Inductive GTransition : g_transition_type :=
| tick : forall increment pre, tick_ok increment pre ->
    pre ~~> tick_update increment pre
| deliver_msg : forall pre uid (key_msg:uid \in pre.(msg_in_transit))
                       pending,
    pending \in pre.(msg_in_transit).[key_msg] ->
    forall (key_ustate:uid \in pre.(users)) ustate_post sent,
      let ustate_pre := pre.(users).[key_ustate] in
      UTransition (Some (snd pending),ustate_pre) (ustate_post,sent) ->
      pre ~~> delivery_result pre uid key_msg pending ustate_post sent
| step_internal : forall pre uid (H:uid \in pre.(users)),
    let ustate_pre := pre.(users).[H] in
    (* ustate_pre.(deadline) = Some (ustate_pre.(timer)) -> *)
    forall ustate_post sent,
      (None,ustate_pre) ~> (ustate_post,sent) ->
      pre ~~> step_result pre uid ustate_post sent
where "x ~~> y" := (GTransition x y) : type_scope .

(* We might also think of an initial state S and a schedule of events X
   and comptue traces corresponding to S and X, and then showing properties
   on them
*)

(** Now we have lemmas showing that transitions preserve various invariants *)

Definition user_timers_valid : pred UState :=
  fun u =>
    (Rleb u.(p_start) u.(timer) &&
    if u.(deadline) is Some d then Rleb u.(timer) d else true).

(*
Lemma tick_preserves_timers : forall pre,
    List.Forall user_timers_valid pre.(users) ->
    forall increment, tick_ok increment pre ->
    List.Forall user_timers_valid (tick_result increment pre).(users).
Proof.
  destruct pre as [? ? users ?];unfold tick_ok;simpl;clear.
  intros Htimers_valid increment Hcan_advance.
  apply Forall_map. revert Htimers_valid Hcan_advance.
  apply Forall_impl2. clear. intro u.
  destruct u;simpl;clear.
  destruct deadline0;intuition auto using Rle_pos_r;constructor.
Qed.
*)

End AlgoModel.
