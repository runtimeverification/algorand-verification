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

Require Import Lra.

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

(* None means the value bottom *)
(* NOTE: No need to explicitly represent bottom, so this is removed.*)
(* Definition MaybeValue := option Value. *)

(* Similar to the strucutres used as values in messages in Victor's paper *)
Inductive ExValue :=
  | val      : Value -> ExValue
  | step_val : nat -> ExValue
  | repr_val : Value -> UserId -> nat -> ExValue
  | next_val : Value -> nat -> ExValue.

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

(* A proposal/preproposal record is a triple consisting of two
   values along with a boolean indicating whether this is
   a proposal (true) or a reproposal (false)
*)

Definition PropRecord := (UserId * credType * Value * bool)%type.

(* A vote is a pair of UserID and Value *)
Definition Vote := (UserId * Value)%type.

(* Constructors for the different steps in a period
*)
Inductive StepName :=
  | Proposing
  | Softvoting
  | Certvoting
  | Nextvoting.

Definition UState := local_state.UState UserId Value PropRecord Vote.

(* Notation id         := (local_state.id UserId Value PropRecord Vote). *)
Notation corrupt         := (local_state.corrupt UserId Value PropRecord Vote).
Notation round         := (local_state.round UserId Value PropRecord Vote).
Notation period        := (local_state.period UserId Value PropRecord Vote).
Notation step          := (local_state.step UserId Value PropRecord Vote).
Notation timer         := (local_state.timer UserId Value PropRecord Vote).
Notation deadline      := (local_state.deadline UserId Value PropRecord Vote).
Notation p_start       := (local_state.p_start UserId Value PropRecord Vote).
Notation stv           := (local_state.stv UserId Value PropRecord Vote).
Notation proposals     := (local_state.proposals UserId Value PropRecord Vote).
Notation blocks        := (local_state.blocks UserId Value PropRecord Vote).
Notation softvotes     := (local_state.softvotes UserId Value PropRecord Vote).
Notation certvotes     := (local_state.certvotes UserId Value PropRecord Vote).
Notation nextvotes_open := (local_state.nextvotes_open UserId Value PropRecord Vote).
Notation nextvotes_val := (local_state.nextvotes_val UserId Value PropRecord Vote).
Notation has_certvoted := (local_state.has_certvoted UserId Value PropRecord Vote).

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

Definition set_has_certvoted (u : UState) r' p' b' : UState :=
  {[ u with has_certvoted := fun r p => if (r, p) == (r', p') 
                                        then b' 
                                        else u.(has_certvoted) r p ]}.

Definition advance_period (u : UState) : UState :=
  {[ {[ {[ {[ {[ u with period := u.(period) + 1 ]}
                with step := 1 ]}
             with timer := 0%R ]}
          with deadline := 0%R ]}
       with p_start := u.(p_start) + u.(timer) ]}.

Definition advance_round (u : UState) : UState :=
  {[ {[ {[ {[ {[ {[ u with round := u.(round) + 1 ]}
                   with period := 1 ]}
                with step := 1 ]}
             with timer := 0%R ]}
          with deadline := 0%R ]}
       with p_start := u.(p_start) + u.(timer) ]}.

(* A proposition for whether a given credential qualifies its
   owner to be a committee member *)
(* Note: This abstract away how credential values are
   interpreted (which is a piece of detail that may not be
   relevant to the model at this stage) *)
Variable committee_cred : credType -> Prop.

Definition comm_cred_step uid r p s : Prop :=
  committee_cred (credential uid r p s) .

(*
(* Similarly, a proposition for whether a given credential qualifies its
   owner to be a potential leader *)
Variable leader_cred : credType -> Prop.


Definition leader_cred_step (u : UState) r p s : Prop :=
  leader_cred (credential u.(id) r p s) .


(* The basic requirement that a potential leader for a particular round-period-step
   must by defintion be a committee member as well for that round-period-step *)
Hypothesis leader_is_comm_member :
  forall cr : credType, leader_cred cr -> committee_cred cr .
*)

Notation now         := (global_state.now UserId UState [choiceType of Msg]).
Notation network_partition := (global_state.network_partition UserId UState [choiceType of Msg]).
Notation users         := (global_state.users UserId UState [choiceType of Msg]).
Notation msg_in_transit  := (global_state.msg_in_transit UserId UState [choiceType of Msg]).

Definition GState := global_state.GState UserId UState [choiceType of Msg].

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

(* additional time delay introduced by the adversary when the network is
   partitioned *)
Variable rho : R.

Hypothesis arbitrary_rho : (rho >= 0)%R .

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

(* Is the given message a vote (softvote, certvote or nextvote) message? *)
Definition vote_msg (msg : Msg) : Prop :=
  match msg.1.1.1.1 with
  | Softvote | Certvote | Nextvote_Open | Nextvote_Val => True
  | _ => False
  end.

(* Does the given round/period/step match the ones stored in the user state? *)
Definition valid_rps (u : UState) r p w : Prop :=
  u.(round) = r /\ u.(period) = p /\ step_name(u.(step)) = Some w .

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

(* Whether the user has already certified a value (based on enough nextvotes) in the previous period
   of the current round (for some step during that period) *)
(* This corresponds to cert_may_exist field in the automaton model *)
(* Notes: - modified based on Victor's comment
          - p > 1
*)
Definition cert_may_exist (u:UState) : Prop :=
  let p := u.(period) in
  let r := u.(round) in
  forall s, ~ nextvote_bottom_quorum u r (p - 1) s.
(* to be shown as an invariant (?): exists s, nextvote_val_quorum u r (p - 1) s *)


(* Returns the proposal record in a given sequence of records having the least
   credential (reproposal records are ignored) *)
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
  valid b /\ correct_hash v b /\
  (p > 1 -> ~ cert_may_exist pre) .

(* The reproposal step preconditions *)
(* Note that this is the proposal step when p > 1 and the previous-
   period's winning vote was for a value v *)
(* Note also that we do not distinguish values from their hashes (for now),
   and so the check that v = hash(B) is not used *)
Definition repropose_ok (pre : UState) uid v b r p : Prop :=
  pre.(timer) = 0%R /\
  valid_rps pre r p Proposing /\ p > 1 /\
  comm_cred_step uid r p 1 /\
  v \in prev_certvals pre /\
  valid b /\ correct_hash v b .

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
(* Notes: - the automaton model includes an additional condition that is not
            explicitly given in the description [TODO: investigate]  *)
Definition softvote_repr_ok (pre : UState) uid v r p : Prop :=
  pre.(timer) = (2 * lambda)%R /\
  valid_rps pre r p Softvoting /\ p > 1 /\
  comm_cred_step uid r p 2 /\
  v \in prev_certvals pre.

(* TODO: The Softvoting-conflict step preconditions *)
(* This seems to be related to the condition mentioned above in softvote_new_ok above *)

(* The softvoting step (new or reproposal) post-state *)
(* NOTE: We keep the current deadline at 2 * lambda and let certvoting rules do that
         (to avoid timing out while certvoting is already enabled) *)
(* NOTE: This assumes it is ok to certvote at time 2 * lambda *)
Definition softvote_result (pre : UState) : UState :=
  {[ pre with step := 3 ]}.
(*  update_step
    (update_deadline pre (next_deadline pre.(step))
    3.
*)

(** Step 3: Certvoting propositions and user state update **)

(* Certvoting step preconditions *)
(* The successful case *)
(* Notes: - Note that this applies for all period values *)
(*        - Corresponds (roughly) to transitions cert_softvotes and certvote in
            the automaton model
          - The condition comm_cred_step is checked outside of this proposition
            to allow distinguishing the two cases of has_certvoted when
            defining the transitions later *)
(* Note the time period is left-closed unlike the algorand paper to easily allow
    checking whether the action should fire at the beginning of the time period *)
Definition certvote_ok (pre : UState) (v b: Value) r p : Prop :=
  ((2 * lambda)%R <= pre.(timer) < lambda + big_lambda)%R /\
  valid_rps pre r p Certvoting /\
  (p > 1 -> ~ cert_may_exist pre) /\
  valid_block_and_hash pre b v r p /\
  v \in certvals pre r p .

(* Certvoting step preconditions *)
(* The unsuccessful case *)
(* Notes: - Corresponds (roughly) to no_certvote_nocred in the automaton model
          - The Algorand2 description does not explicitly specify what happens in this case
          - The timeout case is handled by a generic timeout transition given later
*)
(* Note the time period is left-closed unlike the algorand paper to easily allow
    checking whether the action should fire at the beginning of the time period *)
Definition no_certvote_ok (pre : UState) r p : Prop :=
  ((2 * lambda)%R <= pre.(timer) < lambda + big_lambda)%R /\
  valid_rps pre r p Certvoting /\
  nilp (certvals pre r p).

(* Certvoting step's resulting user state (both cases) *)
Definition certvote_result (pre : UState) b : UState :=
  {[ {[ (set_has_certvoted pre pre.(round) pre.(period) b)
             with step := 4 ]}
             with deadline := (lambda + big_lambda)%R ]}.

(** Steps >= 4: Nextvoting1 propositions and user state update **)

(* Nextvoting step preconditions *)
(* The proper-value case *)
(* Notes: - Corresponds (roughly) to transition nextvote_val in the automaton model (but not the same) *)
(*        - Corresponds more closely to the Algorand2 description (but with the committee membership constraint)
          - Updated to accommodate the 27March change
 *)
Definition nextvote_val_ok (pre : UState) uid (v b : Value) r p s : Prop :=
  pre.(timer) = (lambda + big_lambda + (INR s - 4) * L)%R /\
  valid_rps pre r p Nextvoting /\
  valid_block_and_hash pre b v r p /\
  (* Nat.Even s /\ *) s >= 4 /\
  comm_cred_step uid r p s /\
  (* pre.(has_certvoted) r p. *)
  v \in certvals pre r p.

(* Nextvoting step preconditions *)
(* The bottom-value case *)
(* Notes: - Corresponds (roughly) to transition nextvote_open in the automaton model (but not the same) *)
(*        - Corresponds more closely to the Algorand2 description (but with the committee membership constraint)
          - Updated to accommodate the 27March change
*)
Definition nextvote_open_ok (pre : UState) uid (v : Value) r p s : Prop :=
  pre.(timer) = (lambda + big_lambda + (INR s - 4) * L)%R /\
  valid_rps pre r p Nextvoting /\
  (* Nat.Even s /\ *) s >= 4 /\
  comm_cred_step uid r p s /\
  (* ~ pre.(has_certvoted) r p /\ *)
  (p > 1 -> nextvote_bottom_quorum pre r (p - 1) s ).

(* Nextvoting step preconditions *)
(* The aditional special case of using the starting value *)
(* Notes: - Not sure if this is captured in the automaton model *)
(*        - Corresponds more closely to the Algorand2 description (but with additional constraints given explicitly)
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
Definition certify_ok (pre : UState) (v : Value) r p : Prop :=
  (* valid_rps pre r p Nextvoting /\ *)
  exists b, valid_block_and_hash pre b v r p /\
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
(* Note: This captures the timeout transitions in the automaton model in addition
         to timing out in the repeated steps *)
(* Note: Updated to accommodate the 27March change *)
Definition timeout_ok (pre : UState) : Prop :=
  pre.(step) = 3 /\ (pre.(timer) >= pre.(deadline))%R.

(* On a timeout, move on to the next step and update the deadline *)
Definition timeout_result (pre : UState) : UState :=
  {[ pre with step := pre.(step) + 1 ]}.
(*  {[ {[ pre with deadline := next_deadline pre.(step) ]}
       with step := pre.(step) + 1 ]}. *)

(** Message delivery transitions **)

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

(** The inductive definition of the user state transition relation **)

(* The transition relation type *)
(* A user transitions from a state, possibly consuming a message, into a post-state
   while emitting a (possibly empty) sequence of outgoing messages *)
Definition u_transition_type := (option Msg * UState) -> (UState * seq Msg) -> Prop.

Reserved Notation "x ~> y" (at level 70).

Inductive UTransition : u_transition_type :=
  (** Internal actions **)
  (* Actions that are supposed to take place:
  	  - at a specific time instance (i.e. never triggered by a recevied message)
  	  - during a time duration, but the preconditions are already satisfied that
  	  	the action fires eagerly at the beginning of that time duration (again,
  	  	without consuming a message)
  	  *)

  (* Step 1: Block Proposal *)
  | propose : forall (pre : UState) uid v b r p,
      propose_ok pre uid v b r p ->
      (None, pre) ~> (propose_result pre,
          [:: (Proposal, val v, r, p, uid) ;
              (Block, val b, r, p, uid)])
  (* Step 1: Block Proposal [Reproposal] *)
  | repropose : forall (pre : UState) uid v b r p,
      repropose_ok pre uid v b r p ->
      (None, pre) ~> (propose_result pre,
          [:: (Reproposal, repr_val v uid p, r, p, uid) ;
              (Block, val b, r, p, uid)])
  (* Step 1: Block Proposal [failure] *)
  | no_propose : forall (pre : UState) uid r p,
      no_propose_ok pre uid r p ->
      (None, pre) ~> (propose_result pre, [::])

  (* Step 2: Filtering Step [new value] *)
  | softvote_new : forall (pre : UState) uid v r p,
      softvote_new_ok pre uid v r p ->
      (None, pre) ~> (softvote_result pre,
          [:: (Softvote, val v, r, p, uid)])
  (* Step 2: Filtering Step [old value] *)
  | softvote_repr : forall (pre : UState) uid v r p,
      softvote_repr_ok pre uid v r p ->
      (None, pre) ~> (softvote_result pre,
          [:: (Softvote, val v, r, p, uid)])

  (* Step 3: Certifying Step [success while being a committee member] *)
  | certvote1 : forall (pre : UState) uid v b r p,
      certvote_ok pre v b r p -> comm_cred_step uid r p 3 ->
        (None, pre) ~> (certvote_result pre true,
          [:: (Certvote, val v, r, p, uid)])
  (* Step 3: Certifying Step [success while NOT being a committee member] *)
  | certvote2 : forall (pre : UState) uid v b r p,
      certvote_ok pre v b r p -> ~ comm_cred_step uid r p 3 ->
        (None, pre) ~> (certvote_result pre true, [::])
  (* Step 3: Certifying Step [failure] *)
  | no_certvote : forall (pre : UState) r p,
      no_certvote_ok pre r p ->
      (None, pre) ~> (certvote_result pre false, [::])

  (* Steps >= 4: Finishing Step - i has cert-voted some v *)
  | nextvote_val : forall (pre : UState) uid v b r p,
      let s := pre.(step) in
      nextvote_val_ok pre uid v b r p s ->
      (None, pre) ~> (nextvote_result pre s, [:: (Nextvote_Val, next_val v s, r, p, uid)])

  (* Steps >= 4: Finishing Step - i has not cert-voted some v *)
  | nextvote_open : forall (pre : UState) uid v r p,
      let s := pre.(step) in
      nextvote_open_ok pre uid v r p s ->
      (None, pre) ~> (nextvote_result pre s, [:: (Nextvote_Open, step_val s, r, p, uid)])

  (* Steps >= 4: Finishing Step - special case of using stv *)
  | nextvote_stv : forall (pre : UState) uid v r p,
      let s := pre.(step) in
      nextvote_stv_ok pre uid v r p s ->
      (None, pre) ~> (nextvote_result pre s, [:: (Nextvote_Val, next_val v s, r, p, uid)])

  (** Deliver messages and possibly trigger actions urgently **)

  (* Deliver a softvote while not triggering any internal action *)
  | deliver_softvote : forall (pre : UState) r p i v b,
      let pre' := (set_softvotes pre r p (i, v)) in
        ~ certvote_ok pre' v b r p ->
        (* ~ nextvote_val_ok pre' v b r p s -> *)
        (Some (Softvote, val v, r, p, i), pre) ~> (pre', [::])

  (* Deliver a softvote and certvote for the value [committee member case] *)
  | deliver_softvote_certvote1 : forall (pre : UState) uid r p s i v b,
      let pre' := set_softvotes pre r p (i, v) in
        certvote_ok pre' v b r p -> comm_cred_step uid r p s ->
        (Some (Softvote, val v, r, p, i), pre) ~> (certvote_result pre' true, [:: (Certvote, val v, r, p, uid)])

  (* Deliver a softvote and certvote for the value [non-committee member case] *)
  | deliver_softvote_certvote2 : forall (pre : UState) uid r p s i v b,
      let pre' := set_softvotes pre r p (i, v) in
        certvote_ok pre' v b r p -> ~ comm_cred_step uid r p s ->
        (Some (Softvote, val v, r, p, i), pre) ~> (certvote_result pre' true, [::])

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
  | deliver_nextvote_open : forall (pre : UState) r p s i,
      let pre' := set_nextvotes_open pre r p s i in
        (* ~ nextvote_open_ok pre' v r p s -> *)
        ~ adv_period_open_ok pre' r p s ->
        (Some (Nextvote_Open, step_val s, r, p, i), pre) ~> (pre', [::])

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
  | deliver_nextvote_open_adv_prd : forall (pre : UState) r p s i,
      let pre' := set_nextvotes_open pre r p s i in
        adv_period_open_ok pre' r p s ->
        (Some (Nextvote_Open, step_val s, r, p, i), pre) ~> (adv_period_result pre', [::])

  (* Deliver a nextvote for value while not triggering any internal action *)
  | deliver_nextvote_val : forall (pre : UState) r p s i v,
      let pre' := set_nextvotes_val pre r p s (i, v) in
        ~ adv_period_val_ok pre' v r p s ->
        (Some (Nextvote_Val, next_val v s, r, p, i), pre) ~> (pre', [::])

  (* Deliver a nextvote for value and advance the period *)
  | deliver_nextvote_val_adv_prd : forall (pre : UState) r p s i v,
      let pre' := set_nextvotes_val pre r p s (i, v) in
        adv_period_val_ok pre' v r p s ->
        (Some (Nextvote_Val, next_val v s, r, p, i), pre) ~> (adv_period_result pre', [::])

  (* Deliver a certvote while not triggering any internal action *)
  | deliver_certvote : forall (pre : UState) v r p i,
      let pre' := set_certvotes pre r p (i, v) in
        ~ certify_ok pre' v r p ->
        (Some (Certvote, val v, r, p, i), pre) ~> (pre', [::])

  (* Deliver a certvote for value and advance the round *)
  | deliver_certvote_adv_rnd : forall (pre : UState) uid v r p i,
      let pre' := set_certvotes pre r p (i, v) in
        certify_ok pre' v r p ->
        (Some (Certvote, val v, r, p, i), pre) ~>
        (certify_result pre', [:: (Certvote, val v, r, p, uid)])

  (* Deliver a message other than vote messages (i.e. Block, Proposal or Reproposal) *)
  | deliver_nonvote_msg : forall (pre : UState) msg c r p,
      ~ vote_msg msg ->
      (Some msg, pre) ~> (deliver_nonvote_msg_result pre msg c r p, [::])

  (** Generic timeout action **)

  (* Timeout transitions -- Applicable only to step = 3 (after the 27March change) *)
  | timeout : forall (pre : UState),
      timeout_ok pre ->
      (None, pre) ~> (timeout_result pre, [::])

where "x ~> y" := (UTransition x y) : type_scope .

(* Global transition relation type *)
Definition g_transition_type := relation GState .

Definition user_can_advance_timer (increment : posreal) : pred UState :=
  fun u => Rleb (u.(timer) + pos increment) u.(deadline).

Definition user_advance_timer (increment : posreal) (u : UState) : UState :=
  {[ u with timer := (u.(timer) + pos increment)%R ]}.

Definition tick_ok_users increment (pre:GState) : bool :=
  allf (user_can_advance_timer increment) pre.(users).

Lemma tick_ok_usersP : forall increment (g : GState),
  reflect
    (forall (uid : UserId) (h : uid \in domf g.(users)), user_can_advance_timer increment g.(users).[h])
    (tick_ok_users increment g).
Proof.
move => increment g.
exact: allfP.
Qed.

Definition tick_ok_msgs (increment:posreal) (pre:GState) : bool :=
  let target_time := (pre.(now) + pos increment)%R in
  \big[andb/true]_(user_msgs <- codomf pre.(msg_in_transit))
   \big[andb/true]_(m <- (enum_mset user_msgs)) Rleb target_time (fst m).

Definition tick_ok (increment:posreal) (pre:GState) : bool :=
  tick_ok_users increment pre && tick_ok_msgs increment pre.

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
  msetU [mset (msg_deadline msg now, msg)] v.

Definition send_broadcast (now : R) (targets:{fset UserId}) (prev_msgs:MsgPool) (msg: Msg) : MsgPool :=
  updf prev_msgs targets (merge_msg_deadline now msg).

Definition send_broadcasts (deadline : R) (targets : {fset UserId}) (prev_msgs : MsgPool) (msgs : seq Msg) : MsgPool :=
  foldl (send_broadcast deadline targets) prev_msgs msgs.

(* Computes the global state after a message delivery,
   given the result of the user transition *)
Definition delivery_result pre uid (uid_has_mailbox : uid \in pre.(msg_in_transit)) delivered ustate_post (sent: seq Msg) : GState :=
  let users' := pre.(users).[uid <- ustate_post] in
  let user_msgs' := (pre.(msg_in_transit).[uid_has_mailbox] `\ delivered)%mset in
  let msgs' := send_broadcasts (pre.(now)+lambda)%R (domf (pre.(users)) `\ uid)
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

(* Resets the deadline of a message having an excessively high delay *)
Definition reset_deadline now (msgs : {mset R * Msg}) (msg : R * Msg) : {mset R * Msg} :=
  let cur_deadline := fst msg in
  let max_deadline := msg_deadline (snd msg) now in
  let new_deadline := (Rmin cur_deadline max_deadline) in
  (msgs `|` [mset (new_deadline, msg.2)])%mset.

(* Recursively resets message deadlines of all the messages given *)
Definition reset_user_msg_delays msgs now : {mset R * Msg} :=
  foldl (reset_deadline now) mset0 msgs .

(* Constructs a message pool with all deadlines of messages having excessively
   high delays reset appropriately based on the message type *)
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

(* Postpones the deadline of a message (extending its delivery delay) *)
Definition extend_deadline r (msgs : {mset R * Msg}) (msg : R * Msg) : {mset R * Msg} :=
  let ext_deadline := (fst msg + r)%R in
  (msgs `|` [mset (ext_deadline, msg.2)])%mset.

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

(* Is the network in a partitioned/unpartitioned state? *)
Definition is_partitioned pre : bool := pre.(network_partition).
Definition is_unpartitioned pre : bool := ~~ is_partitioned pre.

(* Computes the state resulting from getting partitioned *)
Definition make_partitioned (pre:GState) : GState :=
  let msgpool' := extend_msg_deadlines pre.(msg_in_transit) in
  {[ (flip_partition_flag pre) with msg_in_transit := msgpool' ]}.
(*  (flip_partition_flag pre). *)

(* Computes the state resulting from recovering from a partition *)
Definition recover_from_partitioned pre : GState :=
  let msgpool' := reset_msg_delays pre.(msg_in_transit) pre.(now) in
  {[ (flip_partition_flag pre) with msg_in_transit := msgpool' ]}.

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
      (Some (snd pending),ustate_pre) ~> (ustate_post,sent) ->
      pre ~~> delivery_result pre uid key_msg pending ustate_post sent
| step_internal : forall pre uid (H:uid \in pre.(users)),
    let ustate_pre := pre.(users).[H] in
    forall ustate_post sent,
      (None,ustate_pre) ~> (ustate_post,sent) ->
      pre ~~> step_result pre uid ustate_post sent
| enter_partition : forall pre,
    is_unpartitioned pre ->
    pre ~~> make_partitioned pre
| exit_partition : forall pre,
    is_partitioned pre ->
    pre ~~> recover_from_partitioned pre
where "x ~~> y" := (GTransition x y) : type_scope.

Inductive GLabel : Type :=
| lbl_tick :  posreal -> GLabel
| lbl_deliver : UserId -> R -> Msg -> seq Msg -> GLabel
| lbl_step_internal : UserId -> seq Msg -> GLabel
| lbl_enter_partition : GLabel
| lbl_exit_partition : GLabel.

Definition related_by (label : GLabel) (pre post : GState) : Prop :=
  match label with
  | lbl_tick increment => tick_ok increment pre /\ post = tick_update increment pre
  | lbl_deliver user deadline msg sent =>
    exists (key_mailbox : user \in pre.(msg_in_transit)),
    (deadline,msg) \in pre.(msg_in_transit).[key_mailbox]
    /\ exists (key_ustate : user \in pre.(users)) ustate_post,
       let ustate_pre := pre.(users).[key_ustate] in
       (Some msg,ustate_pre) ~> (ustate_post,sent)
       /\ post = delivery_result pre user key_mailbox (deadline,msg) ustate_post sent
  | lbl_step_internal user sent =>
    exists (key_user : user \in pre.(users)) ustate_post,
    (None,pre.(users).[key_user]) ~> (ustate_post,sent)
    /\ post = step_result pre user ustate_post sent
  | lbl_enter_partition =>
    is_unpartitioned pre /\ post = make_partitioned pre
  | lbl_exit_partition =>
    is_partitioned pre /\ post = recover_from_partitioned pre
  end.

Definition msg_list_includes (m : Msg) (ms : seq Msg) : Prop :=
  m \in ms.

Definition user_sent uid (m : Msg) (pre post : GState) : Prop :=
  exists ms,
  ((exists d incoming, related_by (lbl_deliver uid d incoming ms) pre post)
  \/ (related_by (lbl_step_internal uid ms) pre post))
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
    exists (lbl_enter_partition);finish_case.
    exists (lbl_exit_partition);finish_case.
  + (* reverse - find transition from label *)
    destruct 1 as [[] Hrel];simpl in Hrel;decompose record Hrel;subst;econstructor;solve[eauto].
Qed.

Definition step_in_path_at (g1 g2 : GState) n (path : seq GState) : Prop :=
  match drop n path with
  | (g1'::g2'::_) => g1' = g1 /\ g2' = g2
  | _ => False
  end.

(** Now we have lemmas showing that transitions preserve various invariants *)

Definition user_timers_valid : pred UState :=
  fun u =>
    (Rleb 0 u.(p_start) &&
     Rleb u.(timer) u.(deadline) ).

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

(* This predicate says a particular step on the path
   is consistent with the given transition label *)
Definition step_at path ix lbl :=
  match drop ix path with
  | pre :: post :: _ => related_by lbl pre post
  | _ => False
  end.

(* Sensible states *)
(* This notion specifiies what states can be considered valid states. The idea
   is that we only consider execution traces that begin at sensible states,
   since sensibility is preserved by the transition system (to be shown), the
   set of reachable states will also be sensible (to be shown). This means that
   it is not important which specific state is assumed as the initial state as
   long as the state is sensible.
   Note: the transditional operational notion of an initial state is a now a
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
Lemma utr_preserves_sensibility : forall us us' m ms,
  sensible_ustate us -> (m, us) ~> (us', ms) ->
  sensible_ustate us'.
Proof.
  Ltac use_hyp H := unfold valid_rps in H;simpl in H; decompose record H.
  Ltac tidy :=
  match goal with
    | [H: step_name ?step = _ |- _] => apply step_name_to_value in H;subst step
    | [ |- context C [ next_deadline (?s + 1 - 1) ] ] =>
      replace (s + 1 - 1) with s by (rewrite addn1;rewrite subn1;symmetry;apply Nat.pred_succ)
    | [ H : is_true (3 < ?s) |- context C [next_deadline ?s] ] =>
      rewrite (step_later_deadlines H)
  end.
  intros us us' m ms H_sensible Hstep.
  remember (m,us) as ustep_input eqn:H_input.
  remember (us',ms) as ustep_output eqn:H_output.
  destruct Hstep eqn:Hstep_record;
    injection H_input;clear H_input;injection H_output;clear H_output;intros;subst us m us' ms;
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
    | [H: certvote_ok _ _ _ _ _ |- _] => unfold certvote_ok in H; use_hyp H
    | [H: no_certvote_ok _ _ _ |- _] => unfold no_certvote_ok in H; use_hyp H
    | [H: nextvote_val_ok _ _ _ _ _ _ _ |- _] => unfold nextvote_val_ok in H; use_hyp H
    | [H: nextvote_open_ok _ _ _ _ _ _ |- _] => unfold nextvote_open_ok in H; use_hyp H
    | [H: nextvote_stv_ok _ _ _ _ _ _ |- _] => unfold nextvote_stv_ok in H; use_hyp H
    | [H: set_softvotes _ _ _ _ |- _] => unfold set_softvotes in H; use_hyp H
    | [H: timeout_ok _ |- _] => unfold timout_ok in H; use_hyp H
    | _ => idtac
    end;
    repeat tidy;intuition lra).
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


(* The global transition relation preserves sensibility of global states *)
Lemma gtr_preserves_sensibility : forall gs gs',
  sensible_gstate gs -> gs ~~> gs' ->
  sensible_gstate gs'.
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
Lemma certvote_only_in_step3 : forall us v b r p,
  certvote_ok us v b r p -> us.(step) = 3.
Proof.
move => us v b r p Hc.
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
Lemma utr_rps_non_decreasing : forall m us1 us2 ms,
  (m, us1) ~> (us2, ms) -> ustate_after us1 us2.
Proof.
move => m us1 us2 ms utrH.
inversion_clear utrH.
  elim: H => tH [vH oH].
  elim: vH => rH [pH sH].
  apply proposing_is_step_1 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.

  elim: H => tH [vH oH].
  elim: vH => rH [pH sH].
  apply proposing_is_step_1 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.

  elim: H => tH [vH oH].
  elim: vH => rH [pH sH].
  apply proposing_is_step_1 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.

  elim: H => tH [vH oH].
  elim: vH => rH [pH sH].
  apply softvoting_is_step_2 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.

  elim: H => tH [vH oH].
  elim: vH => rH [pH sH].
  apply softvoting_is_step_2 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.

  elim: H => tH [vH oH].
  elim: vH => rH [pH sH].
  apply certvoting_is_step_3 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.


  elim: H => tH [vH oH].
  elim: vH => rH [pH sH].
  apply certvoting_is_step_3 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.


  elim: H => tH [vH oH].
  elim: vH => rH [pH sH].
  apply certvoting_is_step_3 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.


  elim: H => tH [vH [vbH [svH oH]]].
  elim: vH => rH [pH sH].
  apply nextvoting_is_step_ge4 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  replace (local_state.step UserId Value PropRecord Vote us1) with s ; last by [].
  rewrite addn1. by [].

  elim: H => tH [vH [vbH [svH oH]]].
  elim: vH => rH [pH sH].
  apply nextvoting_is_step_ge4 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  replace (local_state.step UserId Value PropRecord Vote us1) with s ; last by [].
  rewrite addn1. by [].

  elim: H => tH [vH [vbH [svH oH]]].
  elim: vH => rH [pH sH].
  apply nextvoting_is_step_ge4 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  replace (local_state.step UserId Value PropRecord Vote us1) with s ; last by [].
  rewrite addn1. by [].

  replace pre' with (set_softvotes us1 r p (i, v)); last by [].
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].

  elim: H => tH [vH oH].
  elim: vH => rH [pH sH].
  apply certvoting_is_step_3 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.

  elim: H => tH [vH oH].
  elim: vH => rH [pH sH].
  apply certvoting_is_step_3 in sH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.

  replace pre' with (set_nextvotes_open us1 r p s i); last by [].
  unfold set_softvotes => /=. unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].

  elim: H => vH oH.
  elim: vH => rH [pH sH].
  apply nextvoting_is_step_ge4 in sH.
  unfold ustate_after => /=.
  right. left. split ; first by [].
  rewrite addn1. by [].

  replace pre' with (set_nextvotes_val us1 r p s (i, v)); last by [].
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].

  elim: H => vH oH.
  elim: vH => rH [pH sH].
  apply nextvoting_is_step_ge4 in sH.
  unfold ustate_after => /=.
  right. left. split ; first by [].
  rewrite addn1. by [].

  replace pre' with (set_certvotes us1 r p (i, v)); last by [].
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].

  unfold ustate_after => /=.
  left. rewrite addn1. by [].
  destruct msg.1.1.1.2 eqn:E.
  destruct msg.1.1.1.1 eqn:E'.
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
  do 2! [right]. do 2! [split; auto].

  elim: H => vH oH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  rewrite addn1. by [].
Qed.


(* A one-step global transition never decreases round-period-step of any user *)
Lemma gtr_rps_non_decreasing : forall g1 g2 uid us1 us2,
  g1 ~~> g2 ->
  g1.(users).[? uid] = Some us1 -> g2.(users).[? uid] = Some us2 ->
  ustate_after us1 us2.
Admitted.

(* Generalization of non-decreasing round-period-step results to paths *)
Lemma greachable_rps_non_decreasing : forall g1 g2 uid us1 us2,
  greachable g1 g2 ->
  g1.(users).[? uid] = Some us1 -> g2.(users).[? uid] = Some us2 ->
  ustate_after us1 us2.
Admitted.

(* A user has certvoted a value for a given period along a given path *)
Definition certvoted_in_path_at ix path uid r p v : Prop :=
  exists g1 g2, step_in_path_at g1 g2 ix path
   /\ user_sent uid (Certvote,v,r,p,uid) g1 g2.

Definition certvoted_in_path path uid r p v : Prop :=
  exists ix, certvoted_in_path_at ix path uid r p v.

(* A user has certvoted for one value exactly once for a given period along a given path *)
Definition certvoted_once_in_path path r p uid : Prop :=
  exists ix v, certvoted_in_path_at ix path uid r p v
  /\ forall ix' v',
     certvoted_in_path_at ix path uid r p v -> ix = ix' /\ v = v'.

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
     softvoted_in_path_at ix path uid r p v -> ix = ix' /\ v = v'.

(* L2: An honest user soft-votes for at most one value in a period *)
Lemma no_two_softvotes_in_p : forall path uid r p,
  softvoted_once_in_path path r p uid \/
  forall v, ~ softvoted_in_path path uid r p v.
Admitted.

(* A user has nextvoted bottom for a given period along a given path *)
Definition nextvoted_open_in_path g0 g p uid : Prop :=
  exists g1 g2 us1 us2 m v r id ms,
  greachable g0 g1 /\ g1.(users).[? uid] = Some us1 /\
  greachable g2 g  /\ g2.(users).[? uid] = Some us2 /\
  us1.(period) = p /\ us2.(period) = p /\
  (m, us1) ~> (us2, (Nextvote_Open, v, r, p, id) :: ms).

(* A user has nextvoted a value for a given period along a given path *)
Definition nextvoted_value_in_path g0 g p uid v : Prop :=
  exists g1 g2 us1 us2 m r id ms,
  greachable g0 g1 /\ g1.(users).[? uid] = Some us1 /\
  greachable g2 g  /\ g2.(users).[? uid] = Some us2 /\
  us1.(period) = p /\ us2.(period) = p /\
  (m, us1) ~> (us2, (Nextvote_Val, v, r, p, id) :: ms).

(* L3: If an honest user cert-votes for a value in step 3, the user will NOT next-vote bottom in the same period
*)
Lemma certvote_excludes_nextvote_open_in_p : forall path g1 g2 uid r p v,
  certvoted_in_path path uid r p v -> ~ nextvoted_open_in_path g1 g2 p uid .
Admitted.

(* L3’: If an honest user cert-votes for a value in step 3, the user can only next-vote that value in the same period *)

Lemma certvote_nextvote_value_in_p : forall g1 g2 path uid r p v v',
  certvoted_in_path path uid r p v -> nextvoted_value_in_path g1 g2 p uid v' ->
  v = v'.
Admitted.

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

Definition received_was_sent : forall (p: seq GState) g0 u d msg,
    path gtransition g0 p ->
    msg_received u d msg p ->
    let: (_,exval,msg_r,msg_p,sender) := msg in
    let (safe_p,safe_s) :=
        match exval with
        | val _ => (msg_p.+1,0)
        | step_val s => (msg_p,s)
        | repr_val _ _ s => (msg_p,s)
        | next_val _ s => (msg_p,s)
        end in
    honest_after msg_r safe_p safe_s (sender:UserId) p ->
    exists ix g1 g2,
      step_in_path_at g1 g2 ix p
      /\ user_sent sender msg g1 g2
      /\ match g1.(users).[? sender] with
         | Some ustate => ~ustate.(corrupt)
         | None => False
         end.

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
       committee_cred (credential voter r p s)
       /\ received_next_vote uid voter r p s v path_prefix.
Admitted.

(* L5.1 Any set of t_H committee  members must include at least one honest node *)
Hypothesis quorum_has_honest :
  forall (round period step:nat) path (voters: {fset UserId}),
  #|voters| >= tau_b ->
  (forall voter, voter \in voters -> committee_cred (credential voter round period step)) ->

  exists (honest_voter:UserId), honest_voter \in voters
     /\ honest_after round period step honest_voter path.

(* L5 An honest node can enter period p'>1 only if at least one honest
      note entered period p'-1 *)
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

Lemma adv_period_from_honest_in_prev :
  forall (g0 g1 g2: GState) (path:seq GState) uid r p
         (u_key1:uid \in g1.(users)) (u_key2:uid \in g2.(users)),
    p > 0 ->
    g1.(users).[u_key1].(period) < p ->
    g2.(users).[u_key2].(period) = p ->
    g2.(users).[u_key2].(round) = r ->
    gtransition g1 g2 ->
    step_in_path g1 g2 path ->
    exists honest_prev,
      honest_in_period r (p.-1) honest_prev path.
Proof.
Admitted.

(* To show there is not a fork in a particular round,
   we will take a history that extends before any honest
   node started that round *)
Definition user_before_round r (u : UState) : Prop :=
  u.(round) < r
  /\ (forall r' p, r <= r' -> nilp (u.(proposals) r' p))
  /\ (forall r' p, r <= r' -> nilp (u.(blocks) r' p))
  /\ (forall r' p, r <= r' -> nilp (u.(softvotes) r' p))
  /\ (forall r' p, r <= r' -> nilp (u.(certvotes) r' p))
  /\ (forall r' p s, r <= r' -> nilp (u.(nextvotes_open) r' p s))
  /\ (forall r' p s, r <= r' -> nilp (u.(nextvotes_val) r' p s))
  /\ (forall r' p, r <= r' -> ~~ (u.(has_certvoted) r' p)).

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

(* LIVENESS *)

Definition cert_users (g : GState) v r p :=
  [seq uid <- (domf g.(users)) | if g.(users).[? uid] is Some ustate
                                 then v \in certvals ustate r p
                                 else false
  ].

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
  ~ valid_block_and_hash ustate b v r 1 ->
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
  valid b /\ correct_hash v b ->
  (* TODO: need to filter by just honest users in cert_users? *)
  size (cert_users g v r p) > tau_c.
Admitted.

Lemma prop_g : forall g0 g r b v p,
  greachable g0 g ->
  p >= 2 ->
  all_honest_stv_or_bot g p v ->
  valid b /\ correct_hash v b ->
  (* TODO: need to filter by just honest users in cert_users? *)
  (* TODO: timely produced? *)
  size (cert_users g v r p) > tau_c.
Admitted.

End AlgoModel.
