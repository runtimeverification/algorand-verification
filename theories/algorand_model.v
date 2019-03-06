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

(** Model Assumptions
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
- [TODO: Note on credentials]
**)


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

(* An abstract representation of coomputing block hashes *)
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

(* A proposal/preproposal record is a triple consisting of two
   values along with a boolean indicating with the this is
   a proposal (true) or a preproposal (false)
*)
Definition PropRecord := (Value * Value * bool)%type.

(* A vote is a pair of UserID and Value *)
Definition Vote := (UserId * Value)%type.

(* Constructors for the different steps in a period
*)
Inductive Step :=
  | Proposing
  | Softvoting
  | Certvoting
  | Nextvoting .

(* And now the state of a user
   Note: again we may end up not using all of these fields (and there may
   be others we may want to add later)
*)
Record UState :=
  mkUState {
    id            : UserId;
    corrupt       : bool;
    round         : nat;
    period        : nat;
    step          : Step;
    timer         : R;
    deadline      : option R;
    p_start       : R;
    rec_msgs      : seq Msg;
    cert_may_exist: bool;
    prev_certvals : seq Value;
    proposals     : nat -> nat -> seq PropRecord;
    blocks        : nat -> nat -> seq Value;
    softvotes     : nat -> nat -> seq Vote;
    certvotes     : nat -> nat -> seq Vote;
    certvals      : nat -> nat -> seq Value;
    nextvotes_open: nat -> nat -> nat -> seq Vote;
    nextvotes_val : nat -> nat -> nat -> seq Vote;
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
    cert_may_exist := u.(cert_may_exist);
    prev_certvals  := u.(prev_certvals);
    proposals      := u.(proposals);
    blocks         := u.(blocks);
    softvotes      := u.(softvotes);
    certvotes      := u.(certvotes);
    certvals       := u.(certvals);
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := u.(nextvotes_val);
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
    cert_may_exist := u.(cert_may_exist);
    prev_certvals  := u.(prev_certvals);
    proposals      := u.(proposals);
    blocks         := u.(blocks);
    softvotes      := u.(softvotes);
    certvotes      := u.(certvotes);
    certvals       := u.(certvals);
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := u.(nextvotes_val);
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
    cert_may_exist := u.(cert_may_exist);
    prev_certvals  := u.(prev_certvals);
    proposals      := u.(proposals);
    blocks         := u.(blocks);
    softvotes      := u.(softvotes);
    certvotes      := u.(certvotes);
    certvals       := u.(certvals);
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := u.(nextvotes_val);
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
    cert_may_exist := u.(cert_may_exist);
    prev_certvals  := u.(prev_certvals);
    proposals      := u.(proposals);
    blocks         := u.(blocks);
    softvotes      := u.(softvotes);
    certvotes      := u.(certvotes);
    certvals       := u.(certvals);
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := u.(nextvotes_val);
   |}.

Definition set_cert_may_exist (u : UState) : UState :=
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
    cert_may_exist := true;
    prev_certvals  := u.(prev_certvals);
    proposals      := u.(proposals);
    blocks         := u.(blocks);
    softvotes      := u.(softvotes);
    certvotes      := u.(certvotes);
    certvals       := u.(certvals);
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := u.(nextvotes_val);
   |}.

Definition update_prev_certvals (u : UState) prev_certvals' : UState :=
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
    cert_may_exist := u.(cert_may_exist);
    prev_certvals  := prev_certvals';
    proposals      := u.(proposals);
    blocks         := u.(blocks);
    softvotes      := u.(softvotes);
    certvotes      := u.(certvotes);
    certvals       := u.(certvals);
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := u.(nextvotes_val);
   |}.

Definition advance_period (u : UState) : UState :=
  {|
    id             := u.(id);
    corrupt        := u.(corrupt);
    round          := u.(round);
    period         := u.(period) + 1;
    step           := Proposing;
    timer          := 0%R;
    deadline       := Some 0%R;
    p_start        := u.(p_start); (* not maintained so far *)
    rec_msgs       := u.(rec_msgs);
    cert_may_exist := false;
    prev_certvals  := u.(prev_certvals);
    proposals      := u.(proposals);
    blocks         := u.(blocks);
    softvotes      := u.(softvotes);
    certvotes      := u.(certvotes);
    certvals       := (fun r p => [::]);
    nextvotes_open := u.(nextvotes_open);
    nextvotes_val  := u.(nextvotes_val);
   |}.

(* The credential of a User at a round-period-step triple *)
(* Note: We abstract away the random value produced by an Oracle *)
(* and the fact that credentials are interpreted as integer *)
(* values. Instead, we model the type of credentials as an *)
(* abstract totally ordered type. *)

Variable credType : orderType tt. 

Variable credential : UserId -> nat -> nat -> nat -> credType.

(* quick tests *)
Variable u : UserId.
Definition c1 := credential u 1 1 1.
Definition c2 := credential u 1 1 2.
Check (c1 < c2)%O.

(*
Inductive Credential :=
  | cred : UserId -> nat -> nat -> nat -> Credential.
*)

(* A proposition for whether a given credential qualifies its
   owner to be a committee member *)
(* Note: This abstract away how credential values are
   interpreted (which is a piece of detail that may not be
   relevant to the model at this stage) *)
Variable committee_cred : credType -> Prop.

Definition comm_cred_step (u : UState) r p k : Prop :=
  committee_cred (credential u.(id) r p k) .

(* Similarly, a proposition for whether a given credential qualifies its
   owner to be a potential leader *)
Variable leader_cred : credType -> Prop. 

Definition leader_cred_step (u : UState) r p k : Prop :=
  leader_cred (credential u.(id) r p k) .

(* The basic requirement that a potential leader for a particular round-period-step
   must by defintion be a committee member as well for that round-period-step *)
Hypothesis leader_is_comm_member : 
  forall cr : credType, leader_cred cr -> committee_cred cr .



(* The global state *)
Record GState :=
  mkGState {
    now     : R;
    network_partition : bool;
    users   : {fmap UserId -> UState};
    msg_in_transit : MsgPool;
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

(* small - non-block - message delivery delay *)
Variable lambda : R.

(* block message delivery delay *)
Variable big_lambda : R.

(* some other thresholds *)
(* number of soft-votes needed to cert-vote *)
Variable tau_s : nat.

(* number of cert-votes needed for a certificate *)
Variable tau_c : nat.

(* number of next-votes for None to move to next period *)
Variable tau_b : nat.

(* number of next-votes for a non-None value to move to next period *)
Variable tau_v : nat.

(* upper bound on the credential to be part of the committee for step k *)
(* this is no longer needed!! *)
(* Variable chi   : nat -> nat. *)

(* User-state-level trnasitions *)

(* valid is an abstract proposition on values that tells us whether a value
   is valid *)
Variable valid : Value -> Prop.

(* correct_hash is an abstract proposition on values that tells us whether a 
   given hash value is indeed the hash of the given block value *)
Variable correct_hash : Value -> Value -> Prop.


Definition valid_round_period (u : UState) r p : Prop :=
  u.(round) = r /\ u.(period) = p .

Definition valid_step (u : UState) s : Prop :=
  u.(step) = s .

(** Step 1: Proposing propositions and user state update **)

(* The proposal step preconditions *)
(* Note that this covers both: (a) the case when p = 1, and (b) 
   the case when p > 1 with the previous period voting for bottom. 
   Just as in Victor's model, the fact that the last period's winning 
   vote was for a value is captured by the field cert_may_exist *)
Definition propose_ok (pre : UState) v r p : Prop :=
  pre.(timer) = 0%R /\ 
  valid_round_period pre r p /\ 
  valid_step pre Proposing /\
  leader_cred_step pre r p 1 /\
  ~ pre.(cert_may_exist) /\ 
  valid v.

(* The reproposal step preconditions *)
(* Note that this is the proposal step when p > 1 and the previous-
   period's winning vote was for a value v *)
(* Note also that we do not distinguish values from their hashes (for now),
   and so the check that v = hash(B) is not used *)
Definition repropose_ok (pre : UState) v r p : Prop :=
  pre.(timer) = 0%R /\ 
  valid_round_period pre r p /\ p > 1 /\
  valid_step pre Proposing /\
  leader_cred_step pre r p 1 /\
  v \in pre.(prev_certvals).

(* The no-propose step preconditions *)
(* Note that this applies regardless of whether p = 1 *)
Definition no_propose_ok (pre : UState) r p : Prop :=
  pre.(timer) = 0%R /\ 
  valid_round_period pre r p /\
  valid_step pre Proposing /\
  ~ leader_cred_step pre r p 1.

(* The proposing step (propose, repropose and nopropose) post-state *)
(* Move on to Softvoting and set the new deadline to 2*lambda *)
Definition propose_result (pre : UState) : UState :=
  update_step
    (update_deadline pre (Some (2 * lambda)%R))
    Softvoting.

(** Step 2: Softvoting propositions and user state update **)

(* The Softvoting-a-proposal step preconditions *)
(* Note that this covers both: (a) the case when p = 1, and (b) 
   the case when p > 1 with the previous period voting for bottom. *)
(* Notes: - Victor's model has the constraint clock >= 2*lambda 
          - The Algorand2 description includes an additional constraint
            about whether the value is a p1 value or not *)
Definition softvote_new_ok (pre : UState) (v : Value) r p : Prop :=
  pre.(timer) = (2 * lambda)%R /\
  valid_round_period pre r p /\
  valid_step pre Softvoting /\
  comm_cred_step pre r p 2 /\
  ~ pre.(cert_may_exist) /\ 
  ~ pre.(proposals) r p = [::] . (* so a leader can be identified *)

(* TODO: The Softvoting-a-reproposal step preconditions *)
(* Note that this is the proposal step when p > 1 and the previous-
   period's winning vote was for a value v *)
(* Notes: [same notes as for the case above] *)

(* TODO: The Softvoting-conflict step preconditions *)
(* Need to look further into what this transition does *)

(* TODO: The Softvoting-timeout step preconditions *)
(* If the (honest) user timeouts this step, it must have been the case 
   the user was not a committee member*)

(* The softvoting step post-state *)
Definition softvote_result (pre : UState) : UState :=
  update_step
    (update_deadline pre (Some (lambda + big_lambda)%R))
    Certvoting.

(** Step 3: Certvoting propositions and user state update **)

(* Does the vote's value match the given value? *)
Definition matchValue (x : Vote) (v : Value) : bool :=
  let: (u', v') := x in if v == v' then true else false .

(* Certvoting step preconditions [successful certvoting case] *)
(* Corresponds to transitions cert_softvotes and certvote in Victor's model *)
Definition certvote_ok (pre : UState) (v b: Value) r p : Prop :=
  valid_round_period pre r p /\  
  valid_step pre Certvoting /\
  comm_cred_step pre r p 3 /\
  (pre.(timer) > 2 * lambda)%R /\ (pre.(timer) < lambda + big_lambda)%R /\
  ~ pre.(cert_may_exist) /\
  valid b /\ correct_hash v b /\
  b \in pre.(blocks) r p /\
  size [seq x <- pre.(softvotes) r p | matchValue x v] > tau_s .

(* Certvoting step preconditions [no certvoting case] *)
(* Corresponds to transitions no_certvote_timeout and no_certvote_nocred in Victor's model *)
Definition no_certvote_ok (pre : UState) r p : Prop :=
  valid_round_period pre r p /\ valid_step pre Certvoting /\
  (~ comm_cred_step pre r p 1 \/  
    ( (pre.(timer) >= lambda + big_lambda)%R /\
      forall v, size [seq x <- pre.(softvotes) r p | matchValue x v] <= tau_s ) 
  ) .

(* Certvoting step's resulting user state (for both cases) *)
Definition certvote_result (pre : UState) : UState :=
  update_step
    (update_deadline pre (Some (lambda + big_lambda)%R)) (* the deadline is already this value *)
    Nextvoting.

(** Step 4: Nextvoting propositions and user state update **)

(* TODO:  to be revisited *)
Definition nextvote_open_ok (pre : UState) (v : Value) r p : Prop :=
  valid_round_period pre r p /\ (* p = 1 /\ *)
  valid_step pre Nextvoting /\
  comm_cred_step pre r p 4 /\
  pre.(timer) = (lambda + big_lambda)%R /\
  forall v, size [seq x <- pre.(softvotes) r p | matchValue x v] <= tau_s /\
  (* pre.(certvals) r p = [::] /\ *) (* or we can maintain certvals and do this *)
  ~ pre.(cert_may_exist) .

(* TODO: to be revisited *)
Definition nextvote_val_ok (pre : UState) (v : Value) r p : Prop :=
  valid_round_period pre r p /\ (* p = 1 /\ *)
  valid_step pre Nextvoting /\
  comm_cred_step pre r p 5 /\
  pre.(timer) = (lambda + big_lambda)%R /\
  size [seq x <- pre.(softvotes) r p | matchValue x v] > tau_s
  (* v \in pre.(certvals) r p *) .

(* TODO: to be revisited *)
Definition adv_period_open_ok (pre : UState) (v : Value) r p : Prop :=
  valid_round_period pre r p /\ (* p = 1 /\ *)
  valid_step pre Nextvoting /\
  (* pre.(timer) = (lambda + big_lambda)%R /\ *)
  size (pre.(nextvotes_open) r p 4) > tau_b . (* TODO: using 4 arbitrarily here *)

Definition adv_period_open_result (pre : UState) : UState := advance_period pre .  


(* TODO: to be revisited *)
Definition adv_period_val_ok (pre : UState) (v : Value) r p : Prop :=
  valid_round_period pre r p /\ (* p = 1 /\ *)
  valid_step pre Nextvoting /\
  (* pre.(timer) = (lambda + big_lambda)%R /\ *)
  size [seq x <- (pre.(nextvotes_val) r p 4) | matchValue x v]  > tau_v . (* TODO: using 4 arbitrarily here *)

Definition adv_period_val_result (pre : UState) r p : UState := 
  set_cert_may_exist (advance_period (update_prev_certvals pre (pre.(certvals) r p))).   

(* TODO: Note: need to capture repetitions of steps 4 and 5 in the protocol description *)

(* [TODO: define user-state-level transitions ] *)
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
  | repropose : forall (pre : UState) v r p,
      repropose_ok pre v r p ->
      (None, pre) ~> (propose_result pre, 
          [:: (Reproposal, repr_val v pre.(id) p, r, p, pre.(id)) ; 
              (Block, step_val 2, r, p, pre.(id))])
  | no_propose : forall (pre : UState) r p,
      no_propose_ok pre r p ->
      (None, pre) ~> (propose_result pre, [::])
  (* Step 2: Filtering Step *)
  | softvote_new : forall (pre : UState) v r p,
      softvote_new_ok pre v r p ->
      (None, pre) ~> (softvote_result pre, 
          [:: (Softvote, val (Some v), r, p, pre.(id))]) (* v needs to come from pre *)
  (* Step 3: Certifying Step [success] *)
  | certvote : forall (pre : UState) v b r p,
      certvote_ok pre v b r p ->
      (None, pre) ~> (certvote_result pre, 
          [:: (Certvote, val (Some v), r, p, pre.(id))])
  (* Step 3: Certifying Step [failure] *)
  | no_certvote : forall (pre : UState) r p,
      no_certvote_ok pre r p ->
      (None, pre) ~> (certvote_result pre, [::])
  (* Step 4: First Finishing Step - i has not cert-voted some v *)
  | nextvote_open : forall (pre : UState) v r p,
      nextvote_open_ok pre v r p ->
      (None, pre) ~> (pre, [:: (Nextvote_Open, next_val v 5, r, p, pre.(id))]) (* use bottom instead? *)
  (* Step 4: First Finishing Step - i has cert-voted some v *)
  | nextvote_val : forall (pre : UState) v r p,
      nextvote_val_ok pre v r p ->
      (None, pre) ~> (pre, [:: (Nextvote_Val, step_val 4, r, p, pre.(id))])
  (* Advance period (based on too many bottom-value votes) *)
  | adv_period_open : forall (pre : UState) v r p,
      adv_period_open_ok pre v r p ->
      (None, pre) ~> (adv_period_open_result pre, [::]) 
  (* Advance period (based on enough non-bottom-value votes) *)
  | adv_period_val : forall (pre : UState) v r p,
      adv_period_val_ok pre v r p ->
      (None, pre) ~> (adv_period_val_result pre r p, [::])
where "x ~> y" := (UTransition x y) : type_scope .



(* Global transition relation type *)
Definition g_transition_type := relation GState .

Reserved Notation "x ~~> y" (at level 90).

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

(* [TODO: define the transition relation]
*)
Inductive GTransition : g_transition_type :=  (***)
| tick : forall increment pre, tick_ok increment pre ->
    pre ~~> tick_update increment pre
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
