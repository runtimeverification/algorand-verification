Require Import Lra.

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

Require Import Relation_Operators.

From Algorand
Require Import boolp Rstruct R_util fmap_ext.

From Algorand
Require Import local_state global_state.

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
  of a credential as an unsigned integer is not needed)

**
**)

Section AlgoModel.

(* We assume a finite set of users *)
Variable UserId : finType.

(* And a finite set of values (blocks and block hashes) *)
Variable Value : finType .

(* An abstract representation of computing block hashes *)
(* Variable hash : Value -> Value . *)

(* An enumerated data type of all possible kinds of messages *)
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

(* Inspired by the strucutres used as values in messages in Victor's paper *)
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
Definition decodeExVal
           (c:Value + nat + (Value * UserId * nat) + (Value * nat))
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
(* A message is a tuple (type, ev, r, p, id) where:
    type: message type as an MType
    ev  : message payload as an ExValue
    r   : round value
    p   : period value
    id  : sender's user id
 *)
Definition Msg : Type := MType * ExValue * nat * nat * UserId.

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
Variable credType : orderType tt.

(* A credential is constructed using the user's id and the
   current round-period-step values
 *)
Variable credential : UserId -> nat -> nat -> nat -> credType.

(* Credentials of two differnet users must be different *)
Hypothesis credentials_different :
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

(* An enumerated data type for the different step names in a period
*)
Inductive StepName :=
  | Proposing
  | Softvoting
  | Certvoting
  | Nextvoting.

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

Definition set_blocks (u : UState) r' p' block : UState :=
 {[ u with blocks := fun r p => if (r, p) == (r', p')
                                 then undup (block :: u.(blocks) r p)
                                 else u.(blocks) r p ]}.

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
  {[ {[ {[ {[ {[ {[ u with round := u.(round) + 1 ]}
                   with period := 1 ]}
                with step := 1 ]}
             with timer := 0%R ]}
          with deadline := 0%R ]}
       with p_start := u.(p_start) + u.(timer) ]}.

(* A proposition for whether a given credential qualifies its
   owner to be a committee member
   Note: This abstracts away how credential values are
   interpreted
 *)
Variable committee_cred : credType -> Prop.

(* Whether the credential is a committee credential for the given
   round-period-step
 *)
Definition comm_cred_step uid r p s : Prop :=
  committee_cred (credential uid r p s) .

(* The global state *)
(* Note that the global state structure and supporting functions and notations
   are all defined in global_state.v
 *)
Definition GState := global_state.GState UserId UState [choiceType of Msg].

Notation now               := (global_state.now UserId UState [choiceType of Msg]).
Notation network_partition := (global_state.network_partition UserId UState [choiceType of Msg]).
Notation users             := (global_state.users UserId UState [choiceType of Msg]).
Notation msg_in_transit    := (global_state.msg_in_transit UserId UState [choiceType of Msg]).

(* Flip the network_partition flag *)
Definition flip_partition_flag (g : GState) : GState :=
  {[ g with network_partition := ~~ g.(network_partition) ]}.

(* small - non-block - message delivery delay *)
Variable lambda : R.

(* block message delivery delay *)
Variable big_lambda : R.

(* recovery time period L *)
Variable L : R.

(* assumptions on how these bounds relate *)
Hypothesis delays_positive : (lambda > 0)%R .
Hypothesis delays_order : (lambda < big_lambda < L)%R .

(* additional (non-negative) time delay introduced by the adversary
   when the network is partitioned *)
Variable rho : R.
Hypothesis arbitrary_rho : (rho >= 0)%R .

(* some other thresholds *)
(* number of soft-votes needed to cert-vote *)
Variable tau_s : nat.

(* number of cert-votes needed for a certificate *)
Variable tau_c : nat.

(* number of next-votes for bottom to move to next period *)
Variable tau_b : nat.

(* number of next-votes for a value to move to next period *)
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
Definition valid_block_and_hash b v : Prop :=
  valid b /\ correct_hash v b.

(* Returns the name of a given step value if valid, and None otherwise *)
Definition step_name s : option StepName :=
  match s with
  | 0 => None
  | 1 => Some Proposing
  | 2 => Some Softvoting
  | 3 => Some Certvoting
  | _ => Some Nextvoting
  end.

(* Is the given message a vote (softvote, certvote or nextvote) message? *)
Definition vote_msg (msg : Msg) : Prop :=
  match msg.1.1.1.1 with
  | Softvote | Certvote | Nextvote_Open | Nextvote_Val => True
  | _ => False
  end.

(* Does the given round/period/step match the ones stored in the user state? *)
Definition valid_rps (u : UState) r p w : Prop :=
  u.(round) = r /\ u.(period) = p /\ step_name(u.(step)) = Some w .

Definition advancing_rp (u : UState) r p : Prop :=
  u.(round) < r \/ u.(round) = r /\ u.(period) <= p.

(* Is the vote x for this value v? *)
Definition matchValue (x : Vote) (v : Value) : bool :=
  let: (u', v') := x in v == v' .

(* The sequence of all values appearing in a given sequence of votes with
   duplicates removed *)
Definition vote_values (vs: seq Vote) : seq Value :=
  undup [seq x.2 | x <- vs] .

(* The number of softvotes of a given value in a given user state for the round
   and period given (assumes u.(softvotes) r p is duplicate-free) *)
Definition soft_weight (v:Value) (u:UState) r p : nat :=
  size [seq x <- u.(softvotes) r p | matchValue x v] .

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
  size (u.(nextvotes_open) r p s) >= tau_b .

(* Whether the user has seen enough votes for a value in the given round/period/step *)
Definition nextvote_val_quorum (u:UState) r p s : Prop :=
  exists v, size [seq x <- u.(nextvotes_val) r p s | matchValue x v] >= tau_v.

(* Whether a quorum for bottom was seen in the last period
   of the current round (for some step during that period) *)
(* This corresponds roughly to cert_may_exist field in the automaton model *)
(* Notes: - modified based on Victor's comment
          - assumes p > 1
*)
Definition cert_may_exist (u:UState) : Prop :=
  let p := u.(period) in
  let r := u.(round) in
  forall s, ~ nextvote_bottom_quorum u r (p - 1) s.
(* to be shown as an invariant (?): exists s, nextvote_val_quorum u r (p - 1) s *)


(* Returns the proposal record in a given sequence of records having the least
   credential (reproposal records are ignored)
   i.e. the record of the potential leader
 *)
Fixpoint least_record (prs : seq PropRecord) : option PropRecord :=
  match prs with
  | [::]                          => None
  | [:: (i, cr, v, false)]        => None
  | [:: (i, cr, v, true)]         => Some (i, cr, v, true)
  | [:: (i, cr, v, false) & prs'] => least_record prs'
  | [:: (i, cr, v, true) & prs']  =>
  	  match least_record prs' with
  	  | None => Some (i, cr, v, true)
  	  | Some (_,_, _, false) => Some (i, cr, v, true)
  	  | Some (i', cr', v', true) =>
      if (cr' < cr)%O then Some (i', cr', v', true) else Some (i, cr, v, true)
    	end
  end.

(* Returns whether the given value is the current potential leader value *)
Definition potential_leader_value (v : Value) (prs : seq PropRecord) : Prop :=
  let opr := least_record prs in
  match opr with
  | None => False
  | Some (_,_, _, false) => False
  | Some (i, cr, v', true) => v = v'
  end.

(** Step 1: Proposing propositions and user state update **)

(* The proposal step preconditions *)
(* Note that this covers both: (a) the case when p = 1, and (b)
   the case when p > 1 with the previous period voting for bottom.
   Just as in Victor's model, the fact that the last period's quorum
   was not for bottom is captured by the predicate cert_may_exist *)
Definition propose_ok (pre : UState) uid v b r p : Prop :=
  pre.(timer) = 0%R /\
  valid_rps pre r p Proposing /\
  comm_cred_step uid r p 1 /\
  valid_block_and_hash b v /\
  (p > 1 -> ~ cert_may_exist pre) .

(* The reproposal step preconditions *)
(* Note that this is the proposal step when p > 1 and the previous-
   period's winning vote was for a value v *)
Definition repropose_ok (pre : UState) uid v b r p : Prop :=
  pre.(timer) = 0%R /\
  valid_rps pre r p Proposing /\ p > 1 /\
  comm_cred_step uid r p 1 /\
  v \in prev_certvals pre /\
  valid_block_and_hash b v .

(* The no-propose step preconditions *)
(* Note that this applies regardless of whether p = 1 *)
Definition no_propose_ok (pre : UState) uid r p : Prop :=
  pre.(timer) = 0%R /\
  valid_rps pre r p Proposing /\
  ~ comm_cred_step uid r p 1.

(* The proposing step (propose, repropose and nopropose) post-state *)
(* Move on to Softvoting and set the new deadline to 2*lambda *)
Definition propose_result (pre : UState) : UState :=
  {[ {[ pre with deadline := (2 * lambda)%R ]}
       with step := 2 ]}.

(** Step 2: Softvoting propositions and user state update **)

(* The Softvoting-a-proposal step preconditions *)
(* Note that this covers both: (a) the case when p = 1, and (b)
   the case when p > 1 with the previous period voting for bottom. *)
(* Notes: - Victor's model has the constraint clock >= 2*lambda
          -  The Algorand2 description includes an additional constraint
            about whether the value is a period-1 value or not
            [TODO: TBA in the specs of the transition relation below] *)
Definition softvote_new_ok (pre : UState) uid v r p : Prop :=
  pre.(timer) = (2 * lambda)%R /\
  valid_rps pre r p Softvoting /\
  comm_cred_step uid r p 2 /\
  (p > 1 -> ~ cert_may_exist pre) /\
  potential_leader_value v (pre.(proposals) r p) .

(* The Softvoting-a-reproposal step preconditions *)
(* Note that this is the Softvoting step when p > 1 and the previous-
   period's winning vote was for a value v *)
Definition softvote_repr_ok (pre : UState) uid v r p : Prop :=
  pre.(timer) = (2 * lambda)%R /\
  valid_rps pre r p Softvoting /\ p > 1 /\
  comm_cred_step uid r p 2 /\
  v \in prev_certvals pre.

(* The no-softvoting step preconditions *)
(* Two reasons a user may not be able to soft-vote:
   - Not being in the soft-voting committee, or
   - Not being able to identify a potential leader value to soft-vote for
 *)
(* Note that this may apply regardless of whether p = 1*)
Definition no_softvote_ok (pre : UState) uid v r p : Prop :=
  pre.(timer) = (2 * lambda)%R /\
  valid_rps pre r p Softvoting /\
  (comm_cred_step uid r p 2 ->
    (nilp (prev_certvals pre) /\ ~ potential_leader_value v (pre.(proposals) r p))).

(* TODO: The Softvoting-conflict step preconditions *)
(* This seems to be related to the condition mentioned above in softvote_new_ok above *)

(* The softvoting step (new or reproposal) post-state *)
(* NOTE: We keep the current deadline at 2 * lambda and let certvoting handle
         updating the deadline (to avoid timing out while certvoting is already
         enabled) *)
(* NOTE: This assumes it is ok to certvote at time 2 * lambda *)
Definition softvote_result (pre : UState) : UState :=
  {[ pre with step := 3 ]}.

(** Step 3: Certvoting propositions and user state update **)

(* Certvoting step preconditions *)
(* The successful case *)
(* Notes: - Note that this applies for all period values *)
(*        - Corresponds (roughly) to transitions cert_softvotes and certvote in
            the automaton model
 *)
(* Note the time period is left-closed unlike the algorand paper to easily allow
    checking whether the action should fire at the beginning of the time period *)
Definition certvote_ok (pre : UState) uid (v b: Value) r p : Prop :=
  ((2 * lambda)%R <= pre.(timer) < lambda + big_lambda)%R /\
  valid_rps pre r p Certvoting /\
  comm_cred_step uid r p 3 /\
  (p > 1 -> ~ cert_may_exist pre) /\
  valid_block_and_hash b v /\ 
  b \in pre.(blocks) r p /\
  v \in certvals pre r p .

(* Certvoting step preconditions *)
(* The unsuccessful case *)
(* Notes: - The Algorand2 description does not explicitly specify what happens in this case
          - The timeout case is handled by a generic timeout transition given later
*)
(* Note the time period is left-closed unlike the algorand paper to easily allow
    checking whether the action should fire at the beginning of the time period *)
Definition no_certvote_ok (pre : UState) uid r p : Prop :=
  ((2 * lambda)%R <= pre.(timer) < lambda + big_lambda)%R /\
  valid_rps pre r p Certvoting /\
  (~ comm_cred_step uid r p 3 \/ nilp (certvals pre r p)).

(* Certvoting step's resulting user state (both cases) *)
Definition certvote_result (pre : UState) : UState :=
  {[ {[ pre with step := 4 ]}
            with deadline := (lambda + big_lambda)%R ]}.

(** Steps >= 4: Nextvoting1 propositions and user state update **)

(* Nextvoting step preconditions *)
(* The proper-value case *)
(* Notes: - Corresponds (roughly) to transition nextvote_val in the automaton
            model (but not the same) *)
(*        - Corresponds more closely to the Algorand2 description (but with the
            committee membership constraint)
          - Updated to accommodate the 27March change
 *)
Definition nextvote_val_ok (pre : UState) uid (v b : Value) r p s : Prop :=
  pre.(timer) = (lambda + big_lambda + (INR s - 4) * L)%R /\
  valid_rps pre r p Nextvoting /\
  valid_block_and_hash b v /\
  b \in pre.(blocks) r p /\
  (* Nat.Even s /\ *) s >= 4 /\
  comm_cred_step uid r p s /\
  v \in certvals pre r p.

(* Nextvoting step preconditions *)
(* The bottom-value case *)
(* Notes: - Corresponds (roughly) to transition nextvote_open in the automaton
            model (but not the same) *)
(*        - Corresponds more closely to the Algorand2 description (but with the
            committee membership constraint)
          - Updated to accommodate the 27March change
 *)
Definition nextvote_open_ok (pre : UState) uid (v : Value) r p s : Prop :=
  pre.(timer) = (lambda + big_lambda + (INR s - 4) * L)%R /\
  valid_rps pre r p Nextvoting /\
  (* Nat.Even s /\ *) s >= 4 /\
  comm_cred_step uid r p s /\
  (p > 1 -> nextvote_bottom_quorum pre r (p - 1) s ).

(* Nextvoting step preconditions *)
(* The aditional special case of using the starting value *)
(* Notes: - Not sure if this is captured in the automaton model *)
(*        - Corresponds more closely to the Algorand2 description (but with
            additional constraints given explicitly)
          - Updated to accommodate the 27March change
 *)
Definition nextvote_stv_ok (pre : UState) uid (v : Value) r p s : Prop :=
  pre.(timer) = (lambda + big_lambda + (INR s - 4) * L)%R /\
  valid_rps pre r p Nextvoting /\
  (*Nat.Even s /\ *) s >= 4 /\
  ~ v \in certvals pre r p /\
  p > 1 /\ ~ nextvote_bottom_quorum pre r (p - 1) s /\
  comm_cred_step uid r p s. (* required (?) *)

(* Nextvoting step state update for steps s >= 4 (all cases) *)
(* Note: Updated to accommodate the 27March change *)
Definition nextvote_result (pre : UState) s : UState :=
  {[ {[ pre with step := (s + 1) ]}
            with deadline := (lambda + big_lambda + (INR s - 3) * L)%R]}.

(** Advancing period propositions and user state update **)

(* Preconditions -- The bottom-value case *)
(* Notes: - Corresponds to transition advance_period_open in the automaton model *)
Definition adv_period_open_ok (pre : UState) r p s : Prop :=
  valid_rps pre r p Nextvoting /\
  nextvote_bottom_quorum pre r p s.

(* Preconditions -- The proper value case *)
(* Notes: - Corresponds to transition advance_period_val in the automaton model *)
Definition adv_period_val_ok (pre : UState) (v : Value) r p s : Prop :=
  valid_rps pre r p Nextvoting /\
  size [seq x <- (pre.(nextvotes_val) r p s) | matchValue x v]  >= tau_v.

(* State update -- both cases *)
Definition adv_period_result (pre : UState) : UState := advance_period pre.

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
  b \in pre.(blocks) r p /\
  size [seq x <- pre.(certvotes) r p | matchValue x v] >= tau_c .

(* State update *)
Definition certify_result (pre : UState) : UState := advance_round pre.

(** Timeout transitions **)

(* The timer deadline value for the NEXT step following the given step value *)
(* Note: k is zero-based and hence the apparent difference from the algorand paper.
         The computed deadline values are exactly as given in the paper. *)
(* Note: Updated to accommodate the 27March change *)
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

(* A user timeouts if a deadline is reached while waiting for some external messages
   (i.e. while observing softvotes in step 3) *)
(* Note: This captures the timeout transitions in the automaton model *)
(* Note: Updated to accommodate the 27March change *)
Definition timeout_ok (pre : UState) : Prop :=
  pre.(step) = 3 /\ (pre.(timer) >= pre.(deadline))%R.

(* On a timeout, move on to the next step *)
Definition timeout_result (pre : UState) : UState :=
  {[ pre with step := pre.(step) + 1 ]}.

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
    | Block => set_blocks pre r p v
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
  | repropose : forall uid (pre : UState) v b r p,
      repropose_ok pre uid v b r p ->
      uid # pre ~> (propose_result pre, [:: (Reproposal, repr_val v uid p, r, p, uid) ; (Block, val b, r, p, uid)])

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
  | no_softvote : forall uid (pre : UState) v r p,
      no_softvote_ok pre uid v r p ->
      uid # pre ~> (softvote_result pre, [::])

  (* Step 3: Certifying Step [success] *)
  | certvote1 : forall uid (pre : UState) v b r p,
      certvote_ok pre uid v b r p ->
      uid # pre ~> (certvote_result pre, [:: (Certvote, val v, r, p, uid)])

  (* Step 3: Certifying Step [success while NOT being a committee member]
  | certvote2 : forall uid (pre : UState) v b r p,
      certvote_ok pre v b r p -> ~ comm_cred_step uid r p 3 ->
      uid # pre ~> (certvote_result pre true, [::])
   *)

  (* Step 3: Certifying Step [failure] *)
  | no_certvote : forall uid (pre : UState) r p,
      no_certvote_ok pre uid r p ->
      uid # pre ~> (certvote_result pre, [::])

  (* Steps >= 4: Finishing Step - i has cert-voted some v *)
  | nextvote_val : forall uid (pre : UState) v b r p,
      nextvote_val_ok pre uid v b r p pre.(step) ->
      uid # pre ~> (nextvote_result pre pre.(step), [:: (Nextvote_Val, next_val v pre.(step), r, p, uid)])

  (* Steps >= 4: Finishing Step - i has not cert-voted some v *)
  | nextvote_open : forall uid (pre : UState) v r p,
      nextvote_open_ok pre uid v r p pre.(step) ->
      uid # pre ~> (nextvote_result pre pre.(step), [:: (Nextvote_Open, step_val pre.(step), r, p, uid)])

  (* Steps >= 4: Finishing Step - special case of using stv *)
  | nextvote_stv : forall uid (pre : UState) v r p,
      nextvote_stv_ok pre uid v r p pre.(step) ->
      uid # pre ~> (nextvote_result pre pre.(step), [:: (Nextvote_Val, next_val v pre.(step), r, p, uid)])

  (* Timeout transitions -- Applicable only to step = 3 (after the 27March change) *)
  | timeout : forall uid (pre : UState),
      timeout_ok pre ->
      uid # pre ~> (timeout_result pre, [::])

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

  (* Deliver a softvote and certvote for the value [non-committee member case] *)
  (*
  | deliver_softvote_certvote2 : forall uid (pre : UState) r p s i v b,
      let pre' := set_softvotes pre r p (i, v) in
        certvote_ok pre' uid v b r p -> ~ comm_cred_step uid r p s ->
        uid # pre ; (Softvote, val v, r, p, i) ~> (certvote_result pre', [::])
   *)

  (* Deliver a softvote and nextvote for the value *)
  (* No longer needed after the 27March change *)
  (*
  | deliver_softvote_nextvote_val : forall (pre : UState) r p s i v b,
      let pre' := set_softvotes pre r p (i, v) in
        nextvote_val_ok pre' v b r p s ->
        (* Note that this necessarily implies certvote_ok pre' v r p s cannot be true *)
        (Some (Softvote, val v, r, p, i), pre) ~> (nextvote2_result pre' s, [:: (Nextvote_Val, next_val v s, r, p, uid)])
  *)

  (* Deliver a nextvote for bottom while not triggering any internal action *)
  | deliver_nextvote_open : forall uid (pre : UState) r p s i,
      let pre' := set_nextvotes_open pre r p s i in
      (* ~ nextvote_open_ok pre' v r p s -> *)
      ~ adv_period_open_ok pre' r p s ->
      uid # pre ; (Nextvote_Open, step_val s, r, p, i) ~> (pre', [::])

  (* Deliver a nextvote for bottom and do the nextvote_open action *)
  (* No longer needed after the 27March change *)
  (*
    | deliver_nextvote_open_nextvote : forall (pre : UState) r p s i v,
      let pre' := set_nextvotes_open pre r p s i in
      	nextvote_open_ok pre' v r p s ->
        ~ adv_period_open_ok pre' r p s ->
        (Some (Nextvote_Open, step_val s, r, p, i), pre) ~>
          (nextvote2_result pre' s, [:: (Nextvote_Open, step_val s, r, p, uid)]) *)

  (* Deliver a nextvote for bottom and advance the period *)
  (* Note: Advancing the period takes precedence over nextvote2_open actions *)
  | deliver_nextvote_open_adv_prd : forall uid (pre : UState) r p s i,
      let pre' := set_nextvotes_open pre r p s i in
        adv_period_open_ok pre' r p s ->
        uid # pre ; (Nextvote_Open, step_val s, r, p, i) ~> (adv_period_result pre', [::])

  (* Deliver a nextvote for value while not triggering any internal action *)
  | deliver_nextvote_val : forall uid (pre : UState) r p s i v,
      let pre' := set_nextvotes_val pre r p s (i, v) in
        ~ adv_period_val_ok pre' v r p s ->
        uid # pre ; (Nextvote_Val, next_val v s, r, p, i) ~> (pre', [::])

  (* Deliver a nextvote for value and advance the period *)
  | deliver_nextvote_val_adv_prd : forall uid (pre : UState) r p s i v,
      let pre' := set_nextvotes_val pre r p s (i, v) in
      adv_period_val_ok pre' v r p s ->
      uid # pre ; (Nextvote_Val, next_val v s, r, p, i) ~> (adv_period_result pre', [::])

  (* Deliver a certvote while not triggering any internal action *)
  | deliver_certvote : forall uid (pre : UState) v r p i,
      let pre' := set_certvotes pre r p (i, v) in
      ~ certify_ok pre' v r p ->
      uid # pre ; (Certvote, val v, r, p, i) ~> (pre', [::])

  (* Deliver a certvote for value and advance the round *)
  | deliver_certvote_adv_rnd : forall uid (pre : UState) v r p i,
      let pre' := set_certvotes pre r p (i, v) in
        certify_ok pre' v r p ->
        uid # pre ; (Certvote, val v, r, p, i) ~> (certify_result pre', [:: (Certvote, val v, r, p, uid)])
  (* Deliver a message other than vote messages (i.e. Block, Proposal or Reproposal) *)
  | deliver_nonvote_msg : forall uid (pre : UState) msg c r p,
      ~ vote_msg msg ->
      uid # pre ; msg ~> (deliver_nonvote_msg_result pre msg c r p, [::])
where "a # b ; c ~> d" := (UTransitionMsg a b c d) : type_scope.

(*
Definition u_transition_type := UserId -> UState -> option Msg -> (UState * seq Msg) -> Prop.

Reserved Notation "a # b -/ c ~> d" (at level 70).

Inductive UTransition : u_transition_type :=
| u_transition_msg : forall uid pre msg post,
    uid # pre ; msg ~> post ->
    uid # pre -/ (Some msg) ~> post
| u_transition_internal : forall uid pre post,
    uid # pre ~> post ->
    uid # pre -/ None ~> post
where "a # b -/ c ~> d" := (UTransition a b c d) : type_scope.
*)

(* Gather all the unfoldings we might want for working with transitions into
   a hint database for use with autounfold *)
Create HintDb utransition_unfold discriminated.
Hint Unfold
     (* UTransitionInternal *)
     propose_ok repropose_ok no_propose_ok propose_result
     softvote_new_ok softvote_repr_ok no_softvote_ok softvote_result
     certvote_ok no_certvote_ok certvote_result
     nextvote_val_ok nextvote_open_ok nextvote_stv_ok nextvote_result
     timeout_ok timeout_result
     (* UTransitionMsg *)
     set_softvotes certvote_ok certvote_result
     set_nextvotes_open adv_period_open_ok
     set_nextvotes_val adv_period_val_ok adv_period_result
     set_certvotes certify_ok certify_result
     deliver_nonvote_msg_result : utransition_unfold.

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

(* As a proposition *)
Lemma tick_ok_usersP : forall increment (g : GState),
  reflect
    (forall (uid : UserId) (h : uid \in domf g.(users)), user_can_advance_timer increment g.(users).[h])
    (tick_ok_users increment g).
Proof.
move => increment g.
exact: allfP.
Qed.

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

Lemma tick_users_domf : forall increment pre,
  domf pre.(users) = domf (tick_users increment pre).
Proof.
move => increment pre.
by rewrite -updf_domf.
Qed.

Lemma tick_users_upd : forall increment pre uid (h : uid \in domf pre.(users)),
  (tick_users increment pre).[? uid] = Some (user_advance_timer increment pre.(users).[h]).
Proof.
move => increment pre uid h.
by rewrite updf_update.
Qed.

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

Definition merge_msg_deadline (now : R) (msg : Msg) (_ : UserId) (v : {mset R * Msg}) : {mset R * Msg} :=
  (msg_deadline msg now, msg) +` v.

Definition send_broadcast (now : R) (targets:{fset UserId}) (prev_msgs:MsgPool) (msg: Msg) : MsgPool :=
  updf prev_msgs targets (merge_msg_deadline now msg).

Definition send_broadcasts (deadline : R) (targets : {fset UserId}) (prev_msgs : MsgPool) (msgs : seq Msg) : MsgPool :=
  foldl (send_broadcast deadline targets) prev_msgs msgs.

Lemma send_broadcasts_domf : forall deadline targets prev_msgs msgs uids,
    domf prev_msgs `<=` uids ->
    targets `<=` uids ->
    domf (send_broadcasts deadline targets prev_msgs msgs) `<=` uids.
Admitted.

(* Returns true if the given user id is found in the map and the user state
   corresponding to that id is for a corrupt user *)
Definition is_user_corrupt (uid : UserId) (users : {fmap UserId -> UState}) : bool :=
  if users.[? uid] is Some u then u.(corrupt) else false.

Definition is_user_corrupt_gstate (uid : UserId) (g : GState) : bool :=
  is_user_corrupt uid (g.(users)).

(* Returns the given users map restricted to honest users only *)
Definition honest_users (users : {fmap UserId -> UState}) :=
  let corrupt_ids :=
    [fset x in domf users | is_user_corrupt x users] in
    users.[\ corrupt_ids] .

(* Computes the global state after a message delivery, given the result of the
   user transition
   Notes: - the delivered message is removed from the user's mailbox
          - broadcasts new messages to honest users only
 *)
Definition delivery_result pre uid (uid_has_mailbox : uid \in pre.(msg_in_transit)) delivered ustate_post (sent: seq Msg) : GState :=
  let users' := pre.(users).[uid <- ustate_post] in
  let user_msgs' := (pre.(msg_in_transit).[uid_has_mailbox] `\ delivered)%mset in
  let msgs' := send_broadcasts (pre.(now)+lambda)%R (domf (honest_users pre.(users)) `\ uid)
                              pre.(msg_in_transit).[uid <- user_msgs'] sent in
  {[ {[ pre with users := users' ]} with msg_in_transit := msgs' ]}.
Arguments delivery_result : clear implicits.

(* Computes the global state after an internal user-level transition
   given the result of the user transition and the messages sent out *)
Definition step_result pre uid ustate_post (sent: seq Msg) : GState :=
  let users' := pre.(users).[uid <- ustate_post] in
  let msgs' := send_broadcasts (pre.(now))%R (domf (pre.(users)) `\ uid)
                               pre.(msg_in_transit) sent in
  {[ {[ pre with users := users' ]} with msg_in_transit := msgs' ]}.

Definition new_deadline now cur_deadline msg : R :=
  let max_deadline := msg_deadline msg now in
  Rmax cur_deadline max_deadline.

Definition reset_deadline now (msg : R * Msg) : R * Msg :=
  (new_deadline now msg.1 msg.2, msg.2).

Definition map_mset {A B : choiceType} (f : A -> B) (m : {mset A}) : {mset B} :=
  foldl (fun m x => f x +` m) mset0 m.

Lemma map_mset_count_inj {A B :choiceType} (f: A -> B) (m : {mset A}) :
  injective f -> forall (a :A), m a = (map_mset f m) (f a).
Proof.
  rewrite /map_mset => H_inj a.
  move: (mset0) (mset0E (f a)) => x Hx.
  have ->: m a = ((x (f a) + (count_mem a) m))%nat.
  rewrite Hx.
  symmetry; apply count_mem_mset.
  move: (EnumMset.f m) => l {m}.
  move: l x {Hx}.
  elim => //= x l IHl x0.
  apply/eqP.
  by rewrite -IHl addnA mset1DE eqn_add2r addnC eqn_add2r (eq_sym x) (eqtype.inj_eq H_inj).
Qed.

Lemma map_mset_count {A B :choiceType} (f: A -> B) (m : {mset A}) :
  forall (b:B), (count (preim f (pred1 b)) m) = (map_mset f m) b.
Proof.
  rewrite /map_mset => b.
  move: (mset0) (mset0E b) => x Hx.
  set lh := count _ _.
  have {Hx} ->: lh = (x b + lh)%nat by rewrite Hx.
  rewrite /lh {lh}.
  move: (EnumMset.f m) => l {m}.
  move: l (x).
  elim => //= x0 l IHl x1.
  apply/eqP.
  by rewrite -IHl addnA mset1DE eqn_add2r addnC eqn_add2r (eq_sym b).
Qed.

(* Recursively resets message deadlines of all the messages given *)
Definition reset_user_msg_delays msgs now : {mset R * Msg} :=
  map_mset (reset_deadline now) msgs.

Lemma reset_msg_delays_fwd : forall (msgs : {mset R * Msg}) (m : R * Msg),
    m \in msgs -> forall now, (reset_deadline now m \in reset_user_msg_delays msgs now).
Proof.
  move => msgs m Hm now.
  rewrite -has_pred1 /= has_count.
  have Hcnt: (0 < count_mem m msgs) by rewrite -has_count has_pred1.
  eapply leq_trans;[eassumption|clear Hcnt].
  rewrite (count_mem_mset (reset_deadline now m) (reset_user_msg_delays msgs now)).
  rewrite /reset_user_msg_delays -map_mset_count.
  apply sub_count.
  by move => H /= /eqP ->.
Qed.

Lemma reset_user_msg_delays_rev (now : R) (msgs : {mset R * Msg}) (m: R*Msg):
  m \in reset_user_msg_delays msgs now ->
  exists d0, m = reset_deadline now (d0,m.2) /\ (d0,m.2) \in msgs.
Proof.
  move => Hm.
  suff: (has (preim (reset_deadline now) (pred1 m)) msgs).
    move: m Hm => [d msg] Hm.
    move/hasP => [[d0 msg0] H_mem H_preim].
    move: H_preim; rewrite /preim /pred1 /= /reset_deadline /=.
    case/eqP => Hn Hd; rewrite -Hd -Hn.
    by exists d0; split.
  by rewrite has_count map_mset_count -count_mem_mset -has_count has_pred1.
Qed.

(* Constructs a message pool with all messages having missed delivery deadlines
   updated appropriately based on the message type *)
Definition reset_msg_delays (msgpool : MsgPool) now : MsgPool :=
  updf msgpool (domf msgpool) (fun _ msgs => reset_user_msg_delays msgs now).

Lemma reset_msg_delays_domf : forall (msgpool : MsgPool) now,
   domf msgpool = domf (reset_msg_delays msgpool now).
Proof. by move => msgpool pre; rewrite -updf_domf. Qed.

Lemma reset_msg_delays_upd : forall (msgpool : MsgPool) now uid (h : uid \in domf msgpool),
  (reset_msg_delays msgpool now).[? uid] = Some (reset_user_msg_delays msgpool.[h] now).
Proof.
move => msgpool now uid h.
have Hu := updf_update _ h.
have Hu' := Hu (domf msgpool) _ h.
by rewrite Hu'.
Qed.

Lemma reset_msg_delays_notin : forall (msgpool : MsgPool) now uid
  (h : uid \notin domf msgpool),
  (reset_msg_delays msgpool now).[? uid] = None.
Proof.
  move => msgpool now uid h.
  apply not_fnd.
  change (uid \notin domf (reset_msg_delays msgpool now)).
  unfold reset_msg_delays.
  rewrite <- updf_domf.
  assumption.
Qed.

(* Postpones the deadline of a message (extending its delivery delay) *)
Definition extend_deadline r (msgs : {mset R * Msg}) (msg : R * Msg) : {mset R * Msg} :=
  let ext_deadline := (fst msg + r)%R in
  (msgs `+` [mset (ext_deadline, msg.2)])%mset.

(* Recursively postpones the deadlines of all the messages given *)
Definition extend_user_msg_delays r msgs : {mset R * Msg} :=
  foldl (extend_deadline r) mset0 msgs.

(* Constructs a message pool with all deadlines postponed by rho *)
Definition extend_msg_deadlines (msgpool : MsgPool) : MsgPool :=
  updf msgpool (domf msgpool) (fun _ msgs => extend_user_msg_delays rho msgs).

Lemma extend_msg_deadlines_domf : forall msgpool,
  domf msgpool = domf (extend_msg_deadlines msgpool).
Proof. by move => msgpool; rewrite -updf_domf. Qed.

Lemma extend_msg_deadlines_updf : forall msgpool uid (h : uid \in domf msgpool),
  (extend_msg_deadlines msgpool).[? uid] = Some (extend_user_msg_delays rho msgpool.[h]).
Proof.
move => msgpool uid h.
by rewrite updf_update.
Qed.

(* Computes the state resulting from getting partitioned *)
(* Note: this no longer injects extended message delays (see the tick rule) *)
Definition make_partitioned (pre:GState) : GState :=
  flip_partition_flag pre.
(*
  let msgpool' := extend_msg_deadlines pre.(msg_in_transit) in
  {[ (flip_partition_flag pre) with msg_in_transit := msgpool' ]}.
*)

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

(* Adversary action - partition the network *)
| step_enter_partition : forall pre,
    is_unpartitioned pre ->
    pre ~~> make_partitioned pre

(* Adversary action - corrupt a user *)
| step_corrupt_user : forall pre uid (ustate_key : uid \in pre.(users)),
    pre.(users).[ustate_key].(corrupt) = false ->
    pre ~~> @corrupt_user_result pre uid ustate_key

(* Adversary action - inject extended message delays *)
(* -- modeled by ignoring message delivery deadlines when partitioned *)

(* Adversary action - send out a message *)

where "x ~~> y" := (GTransition x y) : type_scope.

Create HintDb gtransition_unfold discriminated.
Hint Unfold
     tick_ok tick_update tick_users
     delivery_result
     step_result
     is_partitioned recover_from_partitioned
     is_unpartitioned make_partitioned
     corrupt_user_result : gtransition_unfold.

Definition step_in_path_at (g1 g2 : GState) n (path : seq GState) : Prop :=
  match drop n path with
  | (g1'::g2'::_) => g1' = g1 /\ g2' = g2
  | _ => False
  end.

(* definition of reachable global state via paths *)
Definition gtransition : rel GState := [rel x y | `[<GTransition x y>] ].

Definition greachable (g0 g : GState) : Prop := exists2 p, path gtransition g0 p & g = last g0 p.

(* classic definition of reachable global state *)

Definition GReachable (g0 g : GState) : Prop := clos_refl_trans_1n _ GTransition g0 g.

(* definitions are equivalent in our setting *)

Lemma greachable_GReachable : forall g0 g, greachable g0 g -> GReachable g0 g.
Proof.
move => g0 g; case => x.
move: g0 g.
elim: x => /=; first by move => g0 g Ht ->; exact: rt1n_refl.
move => g1 p IH g0 g.
move/andP => [Hg Hp] Hgg.
have IH' := IH _ _ Hp Hgg.
move: IH'; apply: rt1n_trans.
by move: Hg; move/asboolP.
Qed.

Lemma GReachable_greachable : forall g0 g, GReachable g0 g -> greachable g0 g.
Proof.
move => g0 g.
elim; first by move => x; exists [::].
move => x y z Hxy Hc.
case => p Hp Hl.
exists (y :: p) => //=.
apply/andP.
by split => //; apply/asboolP.
Qed.

(* More definitions for stating that a state or transition exists along a path *)
Lemma step_in_path_prefix (g1 g2 : GState) n k (path : seq GState) :
  step_in_path_at g1 g2 n (take k path)
  -> step_in_path_at g1 g2 n path.
Proof.
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

Inductive GLabel : Type :=
| lbl_tick :  posreal -> GLabel
| lbl_deliver : UserId -> R -> Msg -> seq Msg -> GLabel
| lbl_step_internal : UserId -> seq Msg -> GLabel
| lbl_exit_partition : GLabel
| lbl_corrupt_user : UserId -> GLabel
| lbl_enter_partition : GLabel.

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
  | lbl_corrupt_user uid =>
      exists (ustate_key : uid \in pre.(users)),
      pre.(users).[ustate_key].(corrupt) = false
      /\ post = @corrupt_user_result pre uid ustate_key
  | lbl_enter_partition =>
      is_unpartitioned pre /\ post = make_partitioned pre
  end.

Definition msg_list_includes (m : Msg) (ms : seq Msg) : Prop :=
  m \in ms.

Definition user_sent sender (m : Msg) (pre post : GState) : Prop :=
  exists ms,
  ((exists d incoming, related_by (lbl_deliver sender d incoming ms) pre post)
  \/ (related_by (lbl_step_internal sender ms) pre post))
  /\ msg_list_includes m ms.

Lemma transitions_labeled: forall g1 g2,
    g1 ~~> g2 <-> exists lbl, related_by lbl g1 g2.
Proof.
  split.
  + (* forward - find label for transition *)
    Ltac finish_case := simpl;solve[repeat first[reflexivity|eassumption|split|eexists]].
    destruct 1;simpl.
    exists (lbl_tick increment);finish_case.
    destruct pending as [deadline msg];exists (lbl_deliver uid deadline msg sent);finish_case.
    exists (lbl_step_internal uid sent);finish_case.
    exists (lbl_exit_partition);finish_case.
    exists (lbl_enter_partition);finish_case.
    exists (lbl_corrupt_user uid);finish_case.
  + (* reverse - find transition from label *)
    destruct 1 as [[] Hrel];simpl in Hrel;decompose record Hrel;subst;econstructor;solve[eauto].
Qed.

(* This predicate says a particular step on the path
   is consistent with the given transition label *)
Definition step_at path ix lbl :=
  match drop ix path with
  | pre :: post :: _ => related_by lbl pre post
  | _ => False
  end.

Definition msg_received uid msg_deadline msg path : Prop :=
  exists n ms, step_at path n
   (lbl_deliver uid msg_deadline msg ms).

Definition received_next_vote u voter round period step value path : Prop :=
  exists d, msg_received u d ((match value with
                               | Some v => (Nextvote_Val,next_val v step)
                               | None => (Nextvote_Open,step_val step)
                               end),round,period,voter) path.

Definition honest_after (r p s:nat) uid path :=
  exists n,
    match ohead (drop n path) with
    | None => False
    | Some gstate =>
      match gstate.(users).[? uid] with
      | None => False
      | Some ustate => ~ustate.(corrupt)
       /\ (ustate.(round) > r
       \/ ((ustate.(round) = r) /\
          (ustate.(period) > p
           \/ (ustate.(period) = p /\ ustate.(step) > s))))
      end
    end.

Definition committee (r p s:nat) : {fset UserId} :=
  [fset uid : UserId | `[<committee_cred (credential uid r p s)>] ].

Hypothesis quorums_c_honest_overlap :
  forall trace r p s (quorum1 quorum2 : {fset UserId}),
    quorum1 `<=` committee r p s ->
    #| quorum1 | >= tau_c ->
    quorum2 `<=` committee r p s ->
    #| quorum2 | >= tau_c ->
    exists honest_voter,
      honest_voter \in quorum1
      /\ honest_voter \in quorum2
      /\ honest_after r p s honest_voter trace.

Lemma quorum_c_has_honest :
  forall trace r p s (quorum : {fset UserId}),
    quorum `<=` committee r p s ->
    #| quorum | >= tau_c ->
   exists honest_voter, honest_voter \in quorum /\
     honest_after r p s honest_voter trace.
Proof.
  intros trace r p s q H_q H_size.
  pose proof (quorums_c_honest_overlap trace H_q H_size H_q H_size).
  clear -H. decompose record H;eauto.
Qed.

Ltac unfold_step_result :=
  unfold tick_update, tick_users.

Lemma corrupt_preserved_ustep_msg : forall uid upre msg upost,
    uid # upre ; msg ~> upost ->
    upre.(corrupt) -> upost.1.(corrupt).
Proof.
  destruct 1;simpl;try done.
  * (* Only one case remains *)
  unfold deliver_nonvote_msg_result;simpl.
  destruct msg as [[[[? ?] ?] ?] ?];simpl.
  destruct e;[destruct m|..];unfold set_blocks,set_proposals;simpl;done.
Qed.

Lemma corrupt_preserved_ustep_internal : forall uid upre upost,
    uid # upre ~> upost ->
    upre.(corrupt) -> upost.1.(corrupt).
Proof.
  by destruct 1.
Qed.

Lemma corrupt_preserved_gstep : forall (g1 g2 : GState),
    GTransition g1 g2 ->
    forall uid, is_user_corrupt_gstate uid g1 ->
                is_user_corrupt_gstate uid g2.
Proof.
  move => g1 g2 Hstep uid.
  destruct Hstep;unfold is_user_corrupt_gstate;destruct pre;
    unfold_step_result;simpl in * |- *;try done;unfold is_user_corrupt.
  + (* step_tick *)
  destruct (fndP users uid);[|by (intro;exfalso)];
  rewrite updf_update;[by destruct (users.[kf]),corrupt|assumption].
  + (* step_deliver_msg UTransitionMsg *)
  rewrite fnd_set.
  destruct (@eqP (Finite.choiceType UserId) uid uid0);[|done].
  subst uid0;rewrite (in_fnd key_ustate);simpl.
  intro; eapply corrupt_preserved_ustep_msg in H1;assumption.
  + (* step_internal UTransitionInternal *)
  rewrite fnd_set.
  destruct (@eqP (Finite.choiceType UserId) uid uid0);[|done].
  subst uid0;rewrite (in_fnd ustate_key);simpl.
  intro; apply corrupt_preserved_ustep_internal in H0;assumption.
  + (* step_corrupt_user *)
  rewrite fnd_set.
  destruct (@eqP (Finite.choiceType UserId) uid uid0);[|done].
  simpl. trivial.
Qed.

Lemma honest_monotone : forall (p : seq GState) (g0 : GState) uid,
    path gtransition g0 p ->
    ~~ is_user_corrupt_gstate uid (last g0 p) ->
    all (fun g => ~~ is_user_corrupt_gstate uid g) p.
Proof.
  intros p g0 uid. revert p.
  induction p using last_ind;[done|].
  rewrite rcons_path last_rcons all_rcons.
  move => /andP [Hpath Hstep] H_x. apply /andP;split;[assumption|].
  apply IHp. assumption. revert H_x.
  apply contraNN. apply corrupt_preserved_gstep. apply /asboolP. assumption.
Qed.

Lemma path_steps : forall {T} (R : rel T) (P : pred T) x0 p,
    path R x0 p ->
    ~~ P x0 -> P (last x0 p) ->
    exists n,
      match drop n (x0 :: p) with
      | x1 :: x2 :: _ => ~~ P x1 && P x2
      | _ => false
      end.
Proof.
  intros T R P x0 p H_path H_x0.
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

(* This proof will need to be adjusted once the adversary can
   replay messages *)
Lemma send_step_sent : forall (g0 g1:GState) (target:UserId) msg,
    match g0.(msg_in_transit).[? target] with
    | Some mailbox => forall d, (d,msg) \notin mailbox
    | None => True
    end ->
    match g1.(msg_in_transit).[? target] with
    | Some mailbox => exists d, (d,msg) \in mailbox
    | None => False
    end ->
    GTransition g0 g1 ->
    let (_,sender) := msg in
    ~~is_user_corrupt_gstate sender g0 ->
    user_sent sender msg g0 g1.
Proof.
  intros g0 g1 target msg H_unsent_g0 H_sent_g1.
  destruct 1;
    try solve[
              exfalso;
    destruct pre;simpl in * |- *;
    destruct (msg_in_transit.[? target]);[|assumption];
    match goal with
    | [H_sent : exists d, is_true ((d,?msg) \in ?m)
       ,H_unsent : forall d, is_true ((d,?msg) \notin ?m) |- _] =>
      destruct H_sent as [d H_sent];revert H_sent;apply /negP;by apply H_unsent
    end].
  * (* deliver step *)
    assert (msg.2 = uid).
     (* I think this fails because we have the wrong meaning
        of the sender msg.2? *)
     admit.
    assert (msg \in sent).
    (* we must have that an entry is found in H_sent_g1,
       and by H_unsent_g0 and properties of send_broadcasts
       we can show the message doesn't come from the g0 mailbox,
       so it must be derived from sent.
     *)
      admit.

    unfold is_user_corrupt_gstate.
    rewrite (surjective_pairing msg).
    rewrite <- surjective_pairing.
    intro H_honest.

    unfold user_sent.
    exists sent.
    split;[|assumption].
    left.
    exists (pending.1). exists (pending.2).

    rewrite H2 in H_honest |- *.
    simpl.
    rewrite <- surjective_pairing.

    by repeat (esplit||eassumption).
  * (* internal step *)
  admit.
  * (* recover partition *)
    exfalso.
    destruct pre. simpl in H_unsent_g0.
    cbn -[in_mem mem] in H_sent_g1.
    destruct (target \in msg_in_transit) eqn:H_target.
  + rewrite reset_msg_delays_upd in H_sent_g1.
    rewrite (in_fnd H_target) in H_unsent_g0.
    destruct (H_sent_g1) as [d H_sent].
    destruct (reset_user_msg_delays_rev H_sent) as [d0 [H_reset H_in]].
    simpl in H_reset, H_in.
    revert H_in.
    apply /negP.
    by apply H_unsent_g0.
  + rewrite reset_msg_delays_notin in H_sent_g1.
    assumption.
    rewrite H_target.
    reflexivity.
    * (* corrupt user *)
    exfalso.
    destruct pre;simpl in * |- *.
    destruct (target == uid) eqn:H_same.
  + { assert (target = uid) by (apply /eqP;assumption).
      subst uid;clear -H_sent_g1.
      move: H_sent_g1; rewrite /drop_mailbox_of_user.
      case: fndP; case: fndP => //.
        move => Ht Hf [d Hd]; move: Hd.
        by rewrite getf_set in_mset0.
      move => Ht kf [d Hd].
      by case/negP: Ht.
    }
  + revert H_sent_g1.
    unfold drop_mailbox_of_user.
    destruct (uid \in msg_in_transit) eqn:H_uid.
    - rewrite (in_fnd H_uid).
      rewrite fnd_set H_same.
      match goal with | [ |- match ?A with _ => _ end -> False ] => destruct A end;
        [case => x;apply /negP|];done.
    - apply negbT in H_uid. rewrite (not_fnd H_uid).
      match goal with | [ |- match ?A with _ => _ end -> False ] => destruct A end;
        [case => x;apply /negP|];done.
Admitted.

Lemma received_was_sent : forall (p: seq GState) g0 u d msg,
    path gtransition g0 p ->
    msg_received u d msg p ->
    let (msg_body,sender) := msg in
    (let: (_,exval,msg_r,msg_p) := msg_body in
     let (safe_p,safe_s) :=
        match exval with
        | val _ => (msg_p.+1,0)
        | step_val s => (msg_p,s)
        | repr_val _ _ s => (msg_p,s)
        | next_val _ s => (msg_p,s)
        end in
    honest_after msg_r safe_p safe_s (sender:UserId) p) ->
    exists ix g1 g2,
      step_in_path_at g1 g2 ix p
      /\ user_sent sender msg g1 g2
      /\ match g1.(users).[? sender] with
         | Some ustate => ~ustate.(corrupt)
         | None => False
         end.
Admitted.

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
Proof.
  move=> uid msg g1 g2.
  rewrite /user_sent.
  move => [sent [H_trans msg_in]] u H_u.
  change (msg \in sent:Prop) in msg_in.
  destruct msg as [[[[mtype v] r] p] uid_m].
  case: H_trans => [[d [body H_recv]]|H_step].
  * (* message delivery cases *)
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
  match goal with [x : UState |- _] =>
  match goal with [x' := context C [?f x] |- _] =>
  match goal with [H : context C [?g x'] |- _] =>
     destruct x;subst x';unfold f,g in H;simpl in H;
     decompose record H;clear H
  end
  end
  end;
  match goal with
  | [H : valid_rps _ _ _ _ |- _] => move:H;unfold valid_rps
  | [H : advancing_rp _ _ _ |- _] => move:H;unfold advancing_rp
  end;simpl;clear;
    by intuition;subst;intuition.
  * (* internal transition cases *)
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
    | [pre : UState |- _] =>
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
  (* The following does not generally hold since step 2 does no update the deadline *)
  (* It can be refined though to accommodate that *)
  (* us.(deadline) = next_deadline(us.(step) - 1) . *)


Definition sensible_gstate (gs : GState) : Prop :=
  (gs.(now) >= 0)%R /\
  ~ gs.(users) = [fmap] /\
  domf gs.(msg_in_transit) `<=` domf gs.(users) /\ (* needed? *)
  forall uid (k:uid \in gs.(users)), sensible_ustate gs.(users).[k].
  (* more constraints if we add corrupt users map and total message history *)


Lemma step_name_to_value: forall s n,
    step_name s = n ->
    match n with
    | None => s = 0
    | Some Proposing => s = 1
    | Some Softvoting => s = 2
    | Some Certvoting => s = 3
    | Some Nextvoting => s >= 4
    end.
Proof.
  intros;subst. do 4 (destruct s;try reflexivity).
Qed.

Lemma step_later_deadlines : forall s,
    s > 3 -> next_deadline s = (lambda + big_lambda + (INR s - 3) * L)%R.
Proof.
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
  let use_hyp H := (unfold valid_rps in H;simpl in H; decompose record H) in
  let tidy _ :=
  (match goal with
    | [H: step_name ?step = _ |- _] => apply step_name_to_value in H;subst step
    | [ |- context C [ next_deadline (?s + 1 - 1) ] ] =>
      replace (s + 1 - 1) with s by (rewrite addn1;rewrite subn1;symmetry;apply Nat.pred_succ)
    | [ H : is_true (3 < ?s) |- context C [next_deadline ?s] ] =>
      rewrite (step_later_deadlines H)
  end) in
  intros uid us us' m ms H_sensible Hstep;
  remember (us',ms) as ustep_output eqn:H_output;
  destruct Hstep; injection H_output; intros; subst;
  match goal with
  | [H_sensible : sensible_ustate ?s |- _] => is_var s;
     destruct s;unfold sensible_ustate in * |- *;
     decompose record H_sensible;clear H_sensible;simpl in * |- *
  end;
(*  match goal with
  | [H: ?deadline = next_deadline _ |- _] => subst deadline
  end;
*)
  try (
    match goal with
    | [H: propose_ok _ _ _ _ _ _ |- _] => unfold propose_ok in H; use_hyp H
    | [H: repropose_ok _ _ _ _ _ _ |- _] => unfold repropose_ok in H; use_hyp H
    | [H: no_propose_ok _ _ _ _ |- _] => unfold no_propose_ok in H; use_hyp H
    | [H: softvote_new_ok _ _ _ _ _ |- _] => unfold softvote_new_ok in H; use_hyp H
    | [H: softvote_repr_ok _ _ _ _ _ |- _] => unfold softvote_repr_ok in H; use_hyp H
    | [H: no_softvote_ok _ _ _ _ _ |- _] => unfold no_softvote_ok in H; use_hyp H
    | [H: certvote_ok _ _ _ _ _ _ |- _] => unfold certvote_ok in H; use_hyp H
    | [H: no_certvote_ok _ _ _ _ |- _] => unfold no_certvote_ok in H; use_hyp H
    | [H: nextvote_val_ok _ _ _ _ _ _ _ |- _] => unfold nextvote_val_ok in H; use_hyp H
    | [H: nextvote_open_ok _ _ _ _ _ _ |- _] => unfold nextvote_open_ok in H; use_hyp H
    | [H: nextvote_stv_ok _ _ _ _ _ _ |- _] => unfold nextvote_stv_ok in H; use_hyp H
    | [H: set_softvotes _ _ _ _ |- _] => unfold set_softvotes in H; use_hyp H
    | [H: timeout_ok _ |- _] => unfold timout_ok in H; use_hyp H
    | _ => idtac
    end;
    repeat (tidy ());intuition lra).
  (* deliver nonvote msg needs some custom steps *)
  destruct msg as [[[[mtype ex_val] ?] ?] ?];
    destruct ex_val;simpl;[destruct mtype;simpl|..];intuition lra.
  (* timeout - needs a lemma about next_deadline being monotone *)
(*  split; first by assumption.
  unfold timeout_ok in t. use_hyp t.

  unfold next_deadline. subst.
  intuition try lra.
  admit. (* timer montone *)
  replace (step + 1 - 1) with step by (rewrite addn1;rewrite subn1;symmetry;apply Nat.pred_succ).
  reflexivity.
Admitted. *)
Qed.

Lemma utr_nomsg_preserves_sensibility : forall uid us us' ms,
  sensible_ustate us -> uid # us ~> (us', ms) ->
  sensible_ustate us'.
Proof.
  let use_hyp H := (unfold valid_rps in H;simpl in H; decompose record H) in
  let tidy _ :=
  (match goal with
    | [H: step_name ?step = _ |- _] => apply step_name_to_value in H;subst step
    | [ |- context C [ next_deadline (?s + 1 - 1) ] ] =>
      replace (s + 1 - 1) with s by (rewrite addn1;rewrite subn1;symmetry;apply Nat.pred_succ)
    | [ H : is_true (3 < ?s) |- context C [next_deadline ?s] ] =>
      rewrite (step_later_deadlines H)
  end) in
  intros uid us us' ms H_sensible Hstep;
  remember (us',ms) as ustep_output eqn:H_output;
  destruct Hstep; injection H_output; intros; subst;
  match goal with
  | [H_sensible : sensible_ustate ?s |- _] => is_var s;
     destruct s;unfold sensible_ustate in * |- *;
     decompose record H_sensible;clear H_sensible;simpl in * |- *
  end;
(*  match goal with
  | [H: ?deadline = next_deadline _ |- _] => subst deadline
  end;
*)
  try (
    match goal with
    | [H: propose_ok _ _ _ _ _ _ |- _] => unfold propose_ok in H; use_hyp H
    | [H: repropose_ok _ _ _ _ _ _ |- _] => unfold repropose_ok in H; use_hyp H
    | [H: no_propose_ok _ _ _ _ |- _] => unfold no_propose_ok in H; use_hyp H
    | [H: softvote_new_ok _ _ _ _ _ |- _] => unfold softvote_new_ok in H; use_hyp H
    | [H: softvote_repr_ok _ _ _ _ _ |- _] => unfold softvote_repr_ok in H; use_hyp H
    | [H: no_softvote_ok _ _ _ _ _ |- _] => unfold no_softvote_ok in H; use_hyp H
    | [H: certvote_ok _ _ _ _ _ _ |- _] => unfold certvote_ok in H; use_hyp H
    | [H: no_certvote_ok _ _ _ _ |- _] => unfold no_certvote_ok in H; use_hyp H
    | [H: nextvote_val_ok _ _ _ _ _ _ _ |- _] => unfold nextvote_val_ok in H; use_hyp H
    | [H: nextvote_open_ok _ _ _ _ _ _ |- _] => unfold nextvote_open_ok in H; use_hyp H
    | [H: nextvote_stv_ok _ _ _ _ _ _ |- _] => unfold nextvote_stv_ok in H; use_hyp H
    | [H: set_softvotes _ _ _ _ |- _] => unfold set_softvotes in H; use_hyp H
    | [H: timeout_ok _ |- _] => unfold timout_ok in H; use_hyp H
    | _ => idtac
    end;
    repeat (tidy ());intuition lra).
Qed.

(* The global transition relation preserves sensibility of global states *)
Lemma gtr_preserves_sensibility : forall gs gs',
  sensible_gstate gs -> gs ~~> gs' ->
  sensible_gstate gs'.
Proof.
  let use_hyp H := (unfold valid_rps in H;simpl in H; decompose record H) in
  intros gs gs' H_sensible Hstep;
  destruct Hstep.

  * destruct pre. unfold tick_update, tick_users. simpl.
    admit.
  * apply utr_msg_preserves_sensibility in H1;
      [|unfold sensible_gstate in H_sensible;decompose record H_sensible;done].
    destruct pre;unfold sensible_gstate in * |- *.
    unfold delivery_result;simpl in * |- *.
    { intuition. clear -H6 H7. admit.
      admit.
      rewrite ffunE. simpl. admit.
    }
  * apply utr_nomsg_preserves_sensibility in H0;
      [|unfold sensible_gstate in H_sensible;decompose record H_sensible;done].
    destruct pre;unfold sensible_gstate in * |- *.
    unfold step_result;simpl in * |- *.
    { intuition. clear -H5 H6. admit.
      admit.
      rewrite ffunE. simpl. admit.
    }
  * (* recover from partition *)
    admit.
  * (* make partitioned *)
    admit.
  * (* corrupt user *)
    admit.
Admitted.

(* Generalization of preservation of sensibility to paths *)
Lemma greachable_preserves_sensibility : forall g0 g,
  greachable g0 g -> sensible_gstate g0 -> sensible_gstate g.
Proof.
move => g0 g [p Hp] Hg.
elim: p g0 g Hg Hp => /= [g g0 Hg|]; first by rewrite Hg.
move => g p IH g1 g0 Hl.
move/andP => [Ht Hp] Hs.
move/IH: Hp => Hp.
move/Hp: Hl; apply.
move: Ht.
move/asboolP.
exact: gtr_preserves_sensibility.
Qed.

(* SAFETY *)

Lemma path_prefix : forall T R p (x:T) n,
    path R x p -> path R x (take n p).
Proof.
  induction p;[done|].
  move => /= x n /andP [Hr Hpath].
  destruct n. done.
  simpl;apply /andP;by auto.
Qed.

(* Generates a condition on the step value corresponding to a step name *)
Definition step_condition step_name n : Prop :=
  match step_name with
  | None => n = 0
  | Some Proposing  => n = 1
  | Some Softvoting => n = 2
  | Some Certvoting => n = 3
  | _ => n >= 4
  end.

(* The generated condition is correct *)
Lemma step_value_name : forall n, step_condition (step_name n) n.
Proof.
clear.
do 4! [ case => /= ; first by [] ] ; by [].
Qed.

(* A proposing step must have the value 1 *)
Lemma proposing_is_step_1 : forall n, step_name n = Some Proposing -> n = 1 .
Proof.
do 4! [ case => /= ; first by [] ] ; by [].
Qed.

(* A softvoting step must have the value 2 *)
Lemma softvoting_is_step_2 : forall n, step_name n = Some Softvoting -> n = 2 .
Proof.
do 4! [ case => /= ; first by [] ] ; by [].
Qed.

(* A certvoting step must have the value 3 *)
Lemma certvoting_is_step_3 : forall n, step_name n = Some Certvoting -> n = 3 .
Proof.
do 4! [ case => /= ; first by [] ] ; by [].
Qed.

(* A nextvoting step must have a value >= 4 *)
Lemma nextvoting_is_step_ge4 : forall n, step_name n = Some Nextvoting -> n >= 4 .
Proof.
do 4! [ case => /= ; first by [] ] ; by [].
Qed.


(* An honest user may cert-vote only at step 3 of a period *)
(* Certvoting is enabled only at step 3 *)
Lemma certvote_only_in_step3 : forall us uid v b r p,
  certvote_ok us uid v b r p -> us.(step) = 3.
Proof.
move => us uid v b r p Hc.
elim: Hc => tH [vH oH].
elim: vH => rH [pH sH].
by apply certvoting_is_step_3 in sH.
Qed.
(*  (m, pre) ~> (post, (Certvote, v, r, p,id) :: ms) -> pre.(step) = 3. *)

(* An honest user may soft-vote only at step 2 of a period *)
(* Softvoting is enabled only at step 2 *)
Lemma softvote_only_in_step2 : forall us v b r p,
  softvote_new_ok us v b r p -> us.(step) = 2 /\
  softvote_repr_ok us v b r p -> us.(step) = 2 .
Proof.
move => us v b r p Hc.
elim: Hc => tH [vH oH].
elim: vH => rH [pH sH].
by apply softvoting_is_step_2 in sH.
Qed.

(* State us2 comes after state us1 in terms of round-period-step ordering *)
Definition ustate_after us1 us2 : Prop :=
  us1.(round) < us2.(round)
  \/ (us1.(round) = us2.(round) /\ us1.(period) < us2.(period))
  \/ (us1.(round) = us2.(round) /\ us1.(period) = us2.(period) /\ us1.(step) <= us2.(step)).

(* A one-step user-level transition never decreases round-period-step *)
Lemma utr_rps_non_decreasing_msg : forall uid m us1 us2 ms,
  uid # us1 ; m ~> (us2, ms) -> ustate_after us1 us2.
Proof.
move => uid m us1 us2 ms utrH.
inversion_clear utrH.
- rewrite /pre'.
  unfold ustate_after => /=.
  do 2! [right]. by do 2! [split; auto].
- case: H => tH [vH oH].
  case: vH => rH [pH sH].
  apply certvoting_is_step_3 in sH.
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
  apply nextvoting_is_step_ge4 in sH.
  unfold ustate_after => /=.
  right. left. split ; first by [].
  rewrite addn1. by [].
- rewrite /pre'.
  unfold ustate_after => /=.
  do 2! [right]. by do 2! [split; auto].
- unfold ustate_after => /=.
  left. rewrite addn1. by [].
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
Proof.
move => uid us1 us2 ms utrH.
inversion_clear utrH.
- case: H => tH [vH oH].
  case: vH => rH [pH sH].
  apply proposing_is_step_1 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
- case: H => tH [vH oH].
  case: vH => rH [pH sH].
  apply proposing_is_step_1 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
- case: H => tH [vH oH].
  case: vH => rH [pH sH].
  apply proposing_is_step_1 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
- case: H => tH [vH oH].
  case: vH => rH [pH sH].
  apply softvoting_is_step_2 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
- case: H  => tH [vH oH].
  case: vH => rH [pH sH].
  apply softvoting_is_step_2 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
- case: H => tH [vH oH].
  case: vH => rH [pH sH].
  apply softvoting_is_step_2 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
- case: H => tH [vH oH].
  case: vH => rH [pH sH].
  apply certvoting_is_step_3 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
- case: H => tH [vH oH].
  case: vH => rH [pH sH].
  apply certvoting_is_step_3 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
- elim: H => tH [vH [vbH [svH oH]]].
  elim: vH => rH [pH sH].
  apply nextvoting_is_step_ge4 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  rewrite addn1. by [].
- case: H => tH [vH [vbH [svH oH]]].
  case: vH => rH [pH sH].
  apply nextvoting_is_step_ge4 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  rewrite addn1. by [].
- case: H => tH [vH [vbH [svH oH]]].
  case: vH => rH [pH sH].
  apply nextvoting_is_step_ge4 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  rewrite addn1. by [].
- case: H => vH oH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  rewrite addn1. by [].
Qed.

(* A one-step global transition never decreases round-period-step of any user *)
Lemma gtr_rps_non_decreasing : forall g1 g2 uid us1 us2,
  g1 ~~> g2 ->
  g1.(users).[? uid] = Some us1 -> g2.(users).[? uid] = Some us2 ->
  ustate_after us1 us2.
Proof.
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
  by case =>-> => Hcorrupt; case =>->; right; right.
Qed.

(* Generalization of non-decreasing round-period-step results to paths *)
Lemma greachable_rps_non_decreasing : forall g1 g2 uid us1 us2,
  greachable g1 g2 ->
  g1.(users).[? uid] = Some us1 -> g2.(users).[? uid] = Some us2 ->
  ustate_after us1 us2.
Admitted.

(* A user has certvoted a value for a given period along a given path *)
Definition certvoted_in_path_at ix path uid r p v : Prop :=
  exists g1 g2, step_in_path_at g1 g2 ix path
   /\ user_sent uid (Certvote,val v,r,p,uid) g1 g2.

Definition certvoted_in_path path uid r p v : Prop :=
  exists ix, certvoted_in_path_at ix path uid r p v.

(* A user has certvoted for one value exactly once for a given period along a given path *)
Definition certvoted_once_in_path path r p uid : Prop :=
  exists ix v, certvoted_in_path_at ix path uid r p v
  /\ forall ix' v',
     certvoted_in_path_at ix' path uid r p v' -> ix = ix' /\ v = v'.

Definition certified_in_step trace r p s v :=
  exists (certvote_quorum:{fset UserId}), #| certvote_quorum | >= tau_c
  /\ forall (voter:UserId), voter \in certvote_quorum ->
     committee_cred (credential voter r p s)
     /\ certvoted_in_path trace voter r p v.

Lemma certvotes_at_step_3: forall path r p s v,
    certified_in_step path r p s v -> s = 3.
Admitted.

Definition certified_in_period trace r p v :=
  exists (certvote_quorum:{fset UserId}),
    certvote_quorum `<=` committee r p 3
  /\ #| certvote_quorum | >= tau_c
  /\ (forall (voter:UserId), voter \in certvote_quorum
      -> certvoted_in_path trace voter r p v).

(* L1: An honest user cert-votes for at most one value in a period *)
(* :: In any global state, an honest user either never certvotes in a period or certvotes once in step 3 and never certvotes after that during that period
   :: If an honest user certvotes in a period (step 3) then he will never certvote again in that period *)
Lemma no_two_certvotes_in_p : forall path uid r p,
  certvoted_once_in_path path r p uid \/
  forall v, ~ certvoted_in_path path uid r p v.
Admitted.


(* A user has softvoted a value for a given period along a given path *)
Definition softvoted_in_path_at ix path uid r p v : Prop :=
  exists g1 g2, step_in_path_at g1 g2 ix path
   /\ user_sent uid (Softvote,v,r,p,uid) g1 g2.

Definition softvoted_in_path path uid r p v : Prop :=
  exists ix, softvoted_in_path_at ix path uid r p v.

(* A user has softvoted for one value exactly once for a given period along a given path *)
Definition softvoted_once_in_path path r p uid : Prop :=
  exists ix v, softvoted_in_path_at ix path uid r p v
  /\ forall ix' v',
     softvoted_in_path_at ix' path uid r p v' -> ix = ix' /\ v = v'.

Lemma take_rcons T : forall (s : seq T) (x : T), take (size s) (rcons s x) = s.
Proof. elim => //=; last by move => a l IH x; rewrite IH. Qed.

(* L2: An honest user soft-votes for at most one value in a period *)
Lemma no_two_softvotes_in_p : forall path uid r p,
  softvoted_once_in_path path r p uid \/ forall v, ~ softvoted_in_path path uid r p v.
Proof.
(* once a user softvotes (certvotes) in step 2 (3), the user moves on to subsequent steps and never softvotes (certvotes) again in that period. *)
(* appeal to steps being nondecreasing *)
Admitted.

(* A user has nextvoted bottom for a given period along a given path *)
Definition nextvoted_open_in_path g0 g p uid : Prop :=
  exists g1 g2 us1 us2 v r id ms,
  greachable g0 g1 /\ g1.(users).[? uid] = Some us1 /\
  greachable g2 g  /\ g2.(users).[? uid] = Some us2 /\
  us1.(period) = p /\ us2.(period) = p /\
  uid # us1 ~> (us2, (Nextvote_Open, v, r, p, id) :: ms).

(* A user has nextvoted a value for a given period along a given path *)
Definition nextvoted_value_in_path g0 g p uid v : Prop :=
  exists g1 g2 us1 us2 r id ms,
  greachable g0 g1 /\ g1.(users).[? uid] = Some us1 /\
  greachable g2 g  /\ g2.(users).[? uid] = Some us2 /\
  us1.(period) = p /\ us2.(period) = p /\
  uid # us1 ~> (us2, (Nextvote_Val, v, r, p, id) :: ms).

(* L3: If an honest user cert-votes for a value in step 3, the user will NOT next-vote bottom in the same period
*)
Lemma certvote_excludes_nextvote_open_in_p : forall path g1 g2 uid r p v,
  certvoted_in_path path uid r p v -> ~ nextvoted_open_in_path g1 g2 p uid .
Admitted.

(* L3’: If an honest user cert-votes for a value in step 3, the user can only next-vote that value in the same period *)
Lemma certvote_nextvote_value_in_p : forall g1 g2 path uid r p v v',
  certvoted_in_path path uid r p v ->
  forall s, nextvoted_value_in_path g1 g2 p uid (next_val v' s) ->
  v = v'.
Admitted.

(* L5.0 A node enters period p > 0 only if it received t_H next-votes for
   the same value from some step s of period p-1 *)
Definition period_advance_at n path uid r p g1 g2 : Prop :=
  step_in_path_at g1 g2 n path /\
  {ukey_1: uid \in g1.(users) &
  {ukey_2: uid \in g2.(users) &
  let ustate1 := g1.(users).[ukey_1] in
  let ustate2 := g2.(users).[ukey_2] in
  (ustate1.(round) < r \/ ustate1.(round) = r /\ ustate1.(period) < p)
  /\ ustate2.(round) = r /\ ustate2.(period) = p}}.

Lemma period_advance_only_by_next_votes : forall path uid r p,
    forall n,
    (exists g1 g2, period_advance_at n path uid r p g1 g2) ->
    let path_prefix := take n.+2 path in
    exists (s:nat) (v:option Value) (next_voters:{fset UserId}),
      #| next_voters | >= tau_b
      /\ forall voter, voter \in next_voters ->
       committee_cred (credential voter r p.-1 s)
       /\ received_next_vote uid voter r p.-1 s v path_prefix.
Admitted.

(* L5.1 Any set of t_H committee  members must include at least one honest node *)
Hypothesis quorum_has_honest :
  forall (round period step:nat) path (voters: {fset UserId}),
  #|voters| >= tau_b ->
  (forall voter, voter \in voters -> committee_cred (credential voter round period step)) ->

  exists (honest_voter:UserId), honest_voter \in voters
     /\ honest_after round period step honest_voter path.

Definition honest_in_period (r p:nat) uid path :=
  exists n,
    match ohead (drop n path) with
    | None => False
    | Some gstate =>
      match gstate.(users).[? uid] with
      | None => False
      | Some ustate =>
        ~ustate.(corrupt) /\ ustate.(round) = r /\ ustate.(period) = p
      end
    end.

(* L5 An honest node can enter period p'>1 only if at least one
      honest node participated in period p'-1 *)
Lemma adv_period_from_honest_in_prev :
  forall n g0 trace uid r p,
    p > 0 ->
    path gtransition g0 trace ->
    (exists g1 g2, period_advance_at n trace uid r p g1 g2) ->
    exists uid', honest_in_period r (p.-1) uid' trace.
Proof.
  intros n g0 trace uid r p.
  intros H_p H_path H_adv.
  apply period_advance_only_by_next_votes in H_adv.
  destruct H_adv as (s & v & next_voters & next_voters_size & ?).
  destruct (@quorum_has_honest r p.-1 s (take n.+2 trace) next_voters next_voters_size)
    as (uid_honest & H_honest_voter & H_honest);
    [clear -H;intros;apply H;assumption|].
  exists uid_honest.
  specialize (H uid_honest H_honest_voter).
  destruct H.
  destruct H0 as [d H0].
  pose proof (@received_was_sent (take n.+2 trace) g0 uid d
              _ (path_prefix n.+2 H_path) H0).
  simpl in H1.
  lapply H1;[clear H1|destruct v;assumption].
  intros (ix & g1 & g2 & H_step & H_sent & H_honest_at_send).
  unfold honest_in_period;exists ix.
  assert (ohead (drop ix trace) = Some g1) as H_ohead;[|rewrite H_ohead].
  {
    clear -H_step. apply step_in_path_prefix in H_step.
    unfold step_in_path_at in H_step.
    destruct (drop ix trace);[destruct H_step|];
    destruct l;destruct H_step.
    simpl;apply f_equal;assumption.
  }
  match goal with [H : match ?G with _ => _ end |- match ?G with _ => _ end] =>
                  destruct G eqn:H_G;[|exfalso;assumption] end.
  rewrite H_G.
  split. assumption.
  pose proof (honest_users_label_correctly H_sent) as H_lbl.
  rewrite H_G in H_lbl.
  specialize (H_lbl H_honest_at_send).
  decompose record H_lbl.
  destruct v;intuition congruence.
Qed.

(* To show there is not a fork in a particular round,
   we will take a history that extends before any honest
   node has made a transition in that round *)
Definition user_before_round r (u : UState) : Prop :=
  (u.(round) < r \/
   (u.(round) = r /\
    u.(step) = 1 /\ u.(period) = 1 /\ u.(timer) = 0%R /\ u.(deadline) = 0%R))
  /\ (forall r' p, r <= r' -> nilp (u.(proposals) r' p))
  /\ (forall r' p, r <= r' -> nilp (u.(blocks) r' p))
  /\ (forall r' p, r <= r' -> nilp (u.(softvotes) r' p))
  /\ (forall r' p, r <= r' -> nilp (u.(certvotes) r' p))
  /\ (forall r' p s, r <= r' -> nilp (u.(nextvotes_open) r' p s))
  /\ (forall r' p s, r <= r' -> nilp (u.(nextvotes_val) r' p s)).

Definition honest_users_before_round (r:nat) (g : GState) : Prop :=
  forall i (Hi : i \in g.(users)),
    ~~ (g.(users).[Hi].(corrupt)) -> user_before_round r (g.(users).[Hi]).

Definition honest_messages_before_round (r:nat) (g : GState) : Prop :=
  forall (mailbox: {mset R * Msg}), mailbox \in codomf (g.(msg_in_transit)) ->
  forall deadline msg, (deadline,msg) \in mailbox ->
     let: (_,_,r',_,u) := msg in
     r' > r ->
     match g.(users).[? u] return Prop with
     | None => True
     | Some ustate => ustate.(corrupt)
     end.

Definition state_before_round r (g:GState) : Prop :=
  honest_users_before_round r g
  /\ honest_messages_before_round r g.

Definition user_honest (uid:UserId) (g:GState) : bool :=
  if g.(users).[? uid] is Some ustate then ~~ (ustate.(corrupt)) else false.

(* D1: an honest node enters a period exclusively for value v *)
(* if it enters the period with starting value $v$ *)
(* and has not observed t_H next-votes for $\bot$ from any single step of the previous period *)
Definition enters_exclusively_for_value (uid : UserId) (r p : nat) (v : Value) path :=
  exists g1 g2 n, period_advance_at n path uid r p g1 g2 /\
  exists ustate, g2.(users).[? uid] = Some ustate /\
  ~ ustate.(corrupt) /\ ustate.(stv) p = Some v /\
  forall s, size (ustate.(nextvotes_open) r p.-1 s) < tau_b.

(* L6: if all honest nodes that entered a period p >= 2 did so exclusively for value v *)
(* then an honest node cannot cert-vote for any value other than v in step 3 of period p'. *)
Lemma excl_enter_limits_cert_vote :
  forall (r p : nat) (v : Value) path,
    p >= 1 ->
    forall (uid : UserId),
      honest_in_period r p uid path ->
      enters_exclusively_for_value uid r p v path ->
      forall v', certvoted_in_path path uid r p v' -> v' = v.
Proof.
Admitted.

(* A message from an honest user was actually sent in the trace *)
(* Use this to relate an honest user having received a quorum of messages
   to some honest user having sent those messages *)
(* Hopefully the statement can be cleaned up *)
Lemma recved_honest_sent : forall r g0 g1 path_seq pending,
    state_before_round r g0 ->
    path gtransition g0 path_seq ->
    g1 = last g0 path_seq ->
    forall uid (key_msg : uid \in g1.(msg_in_transit)),
      pending \in g1.(msg_in_transit).[key_msg] ->
    let (_,pending_msg) := pending in
    let: (_,_,r',_,sender) := pending_msg in
    user_honest sender g1 ->
    r < r' ->
    exists prefix_len (gmid1 gmid2:GState),
      gmid1 = last g0 (take prefix_len path_seq) /\
      gmid2 = last g0 (take (prefix_len.+1) path_seq) /\
      exists key_msg pending ustate_post sent,
           gmid2 = delivery_result gmid1 sender key_msg pending ustate_post sent
        /\ pending_msg \in sent.
Admitted.

Lemma one_certificate_per_period: forall g0 trace r p,
    state_before_round r g0 ->
    path gtransition g0 trace ->
    forall v1, certified_in_period trace r p v1 ->
    forall v2, certified_in_period trace r p v2 ->
    v1 = v2.
Proof.
  intros g0 trace r p H_start H_path v1 H_cert1 v2 H_cert2.
  destruct H_cert1 as (quorum1 & H_q1 & H_size1 & H_cert1).
  destruct H_cert2 as (quorum2 & H_q2 & H_size2 & H_cert2).
  pose proof (quorums_c_honest_overlap trace H_q1 H_size1 H_q2 H_size2).
  destruct H as (honest_voter & H_common1 & H_common2 & H_honest).
  specialize (H_cert1 _ H_common1).
  specialize (H_cert2 _ H_common2).
  destruct (no_two_certvotes_in_p trace honest_voter r p);
  [|exfalso;eapply H;eassumption].
  unfold certvoted_once_in_path in H.
  decompose record H;clear H.
  destruct H_cert1 as [ix1 H_cert1], H_cert2 as [ix2 H_cert2].
  destruct (H2 _ _ H_cert1) as [_ <-].
  destruct (H2 _ _ H_cert2) as [_ <-].
  reflexivity.
Qed.

Lemma certificate_is_start_of_later_periods:
  forall trace r p v,
    certified_in_period trace r p v ->
  forall p', p' > p ->
    forall uid,
      honest_in_period r p' uid trace ->
      enters_exclusively_for_value uid r p' v trace.
Admitted.

Lemma honest_in_from_after_and_send: forall r p s uid trace,
      honest_after r p s uid trace ->
  forall mt v g1 g2,
    user_sent uid (mt,v,r,p,uid) g1 g2 ->
    honest_in_period r p uid trace.
Admitted.

Theorem safety: forall g0 trace (r:nat),
    state_before_round r g0 ->
    path gtransition g0 trace ->
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
  assert (0 < p2) as Hpos by (apply leq_trans with p1.+1;[rewrite ltnS|];done).

  pose proof H_cert2 as H_cert2'.
  destruct H_cert2' as (q2 & H_q2 & H_size2 & H_cert2').
  destruct (quorum_c_has_honest trace H_q2 H_size2)
     as (honest_voter & H_honest_q & H_honest_in).
  specialize (H_cert2' honest_voter H_honest_q).
  destruct H_cert2' as (ix & ga1 & ga2 & H_cert2').
  assert (honest_in_period r p2 honest_voter trace)
   by (eapply honest_in_from_after_and_send;[eassumption|eexact (proj2 H_cert2')]).

  pose proof (certificate_is_start_of_later_periods H_cert1 Hlt) as H_entry.
  pose proof (@excl_enter_limits_cert_vote r p2 v1 trace Hpos) as H_recert.
  specialize (H_entry honest_voter H).
  specialize (H_recert honest_voter H H_entry v2).
  symmetry. apply H_recert; clear H_recert.


  unfold certvoted_in_path.
  exists ix. exists ga1. exists ga2. assumption.
Qed.

(* LIVENESS *)

Definition cert_users (g : GState) v (r p:nat) :=
  [seq uid <- (domf g.(users)) | if g.(users).[? uid] is Some ustate
                                 then v \in certvals ustate r p
                                 else false].

Definition unique_stv_bot (g : GState) p :=
  all
    (fun uid => if g.(users).[? uid] is Some ustate
                then ustate.(stv) p == None
                else false)
    (domf g.(users)).

Definition all_honest_stv (g : GState) p v :=
  all
    (fun uid => if g.(users).[? uid] is Some ustate
                then if ustate.(corrupt) == false
                     then ustate.(stv) p == Some v
                     else true
                else false)
    (domf g.(users)).

Definition all_honest_stv_or_bot (g : GState) p v :=
  all
    (fun uid => if g.(users).[? uid] is Some ustate
                then if ustate.(corrupt) == false
                     then if ustate.(stv) p == None
                          then true else ustate.(stv) p == Some v
                     else true
                else false)
    (domf g.(users)).

Lemma prop_a : forall g0 g uid ustate c r v,
  greachable g0 g ->
  g.(users).[? uid] = Some ustate -> ustate.(corrupt) = false ->
  (uid, c, v, true) \in ustate.(proposals) r 1 ->
  size (cert_users g v r 1) > tau_c.
Proof.
Admitted.

Lemma prop_b : forall g0 g uid ustate c r b v,
  greachable g0 g ->
  g.(users).[? uid] = Some ustate -> ustate.(corrupt) = true ->
  ~ (valid_block_and_hash v b /\ b \in ustate.(blocks) r 1) ->
  (uid, c, v, true) \in ustate.(proposals) r 1 ->
  size (cert_users g v r 1) <= tau_c.
Proof.
Admitted.

Lemma prop_c : forall g0 g uid ustate r v p,
  greachable g0 g ->
  g.(users).[? uid] = Some ustate -> ustate.(corrupt) = false ->
  (* leader_cred_step ustate r p s -> *)
  unique_stv_bot g p ->
  (* (ustate.(id), c, v, true) \in ustate.(proposals) r 1 -> *)
  size (cert_users g v r 1) > tau_c.
Admitted.

Lemma prop_e : forall g0 g r b v p,
  greachable g0 g ->
  p >= 2 ->
  all_honest_stv g p v ->
  valid_block_and_hash b v ->
  (* TODO: need to filter by just honest users in cert_users? *)
  size (cert_users g v r p) > tau_c.
Admitted.

Lemma prop_g : forall g0 g r b v p,
  greachable g0 g ->
  p >= 2 ->
  all_honest_stv_or_bot g p v ->
  valid_block_and_hash b v ->
  (* TODO: need to filter by just honest users in cert_users? *)
  (* TODO: timely produced? *)
  size (cert_users g v r p) > tau_c.
Admitted.

(* L4: A vote message sent by t_H committee members in a step s>3 must have been sent by some honest nodes that decided to cert-vote for v during step 3. *)
(*
Definition from_cert_voter (v : Value) (r p s : nat) (m : Msg) (voters : {fset UserId}) path :=
  vote_msg m ->
  #|voters| >= tau_b ->
  (forall voter, voter \in voters -> committee_cred (credential voter round period step)) ->
  (forall voter, voter \in voters -> has_sent_vote_message_in r p s) ->
  s > 3 ->
*)

End AlgoModel.
