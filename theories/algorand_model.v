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
Require Import Interval.Interval_tactic.

Require Import Relation_Operators.

From Algorand
Require Import boolp Rstruct R_util fmap_ext.

From Algorand
Require Import local_state global_state.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section AlgoModel.

(* We assume a finite set of users *)
Variable UserId : finType.

(* And a finite set of values (blocks and block hashes) *)
Variable Value : finType .

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
Proof using. by case;rewrite /o2mtype /= inordK. Qed.

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
Proof using. case;reflexivity. Qed.

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
Notation msg_history       := (global_state.msg_history UserId UState [choiceType of Msg]).

(* State with empty maps, unpartitioned, at global time 0 *)
Definition null_state : GState := mkGState _ _ _ 0%R false [fmap] [fmap] mset0.

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
Hypothesis delays_order : (3 * lambda <= big_lambda < L)%R .  (* As per the note from Victor *)

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

Definition step_of_ustate (u:UState) :=
  (u.(round), u.(period), u.(step)).
Arguments step_of_ustate u /.

Definition step_le (step1 step2: nat * nat * nat) :=
  let: (r1,p1,s1) := step1 in
  let: (r2,p2,s2) := step2 in
  r1 < r2 \/ r1 = r2 /\ (p1 < p2 \/ p1 = p2 /\ s1 <= s2).

Definition step_lt (step1 step2: nat * nat * nat) :=
  let: (r1,p1,s1) := step1 in
  let: (r2,p2,s2) := step2 in
  r1 < r2 \/ r1 = r2 /\ (p1 < p2 \/ p1 = p2 /\ s1 < s2).

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

Lemma step_lt_irrefl r p s: ~step_lt (r,p,s) (r,p,s).
Proof using.
  clear.
  unfold step_lt;intuition;by rewrite -> ltnn in * |- .
Qed.

Lemma step_le_refl step: step_le step step.
Proof using.
  clear;unfold step_le;intuition.
Qed.

Definition ustate_after_strict us1 us2 : Prop :=
  step_lt (step_of_ustate us1) (step_of_ustate us2).

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

(* Whether the user has seen enough nextvotes for a given value in the given round/period/step *)
Definition nextvote_value_quorum (u:UState) v r p s : Prop :=
  size [seq x <- u.(nextvotes_val) r p s | matchValue x v] >= tau_v.

(* Whether the user has seen enough nextvotes for some value in the given round/period/step *)
Definition nextvote_quorum_for_some_value (u:UState) r p s : Prop :=
  exists v, size [seq x <- u.(nextvotes_val) r p s | matchValue x v] >= tau_v.

(* Whether a quorum for bottom was seen in the last period
   of the current round (for some step during that period) *)
(* This corresponds roughly to cert_may_exist field in the automaton model *)
(* Notes: - modified based on Victor's comment
 *)
Definition cert_may_exist (u:UState) : Prop :=
  let p := u.(period) in
  let r := u.(round) in
  p > 1 /\ forall s, ~ nextvote_bottom_quorum u r (p - 1) s.
(* to be shown as an invariant (?): exists s, nextvote_quorum_for_some_value u r (p - 1) s *)

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


(** Step 1: Proposing propositions and user state update **)

(* The proposal step preconditions *)
(* Note that this covers both: (a) the case when p = 1, and (b)
   the case when p > 1 with the previous period voting for bottom.
   Just as in Victor's model, the fact that the last period's quorum
   was not for bottom is captured by the predicate cert_may_exist *)
Definition propose_ok (pre : UState) uid v b r p : Prop :=
  pre.(timer) = 0%R /\
  valid_rps pre r p 1 /\
  comm_cred_step uid r p 1 /\
  valid_block_and_hash b v /\
  ~ cert_may_exist pre.

(* The reproposal step preconditions *)
(* Note that this is the proposal step when p > 1 and the previous-
   period's winning vote was for a value v *)
Definition repropose_ok (pre : UState) uid v b r p : Prop :=
  pre.(timer) = 0%R /\
  valid_rps pre r p 1 /\ p > 1 /\
  comm_cred_step uid r p 1 /\
  valid_block_and_hash b v /\
  v \in prev_certvals pre.

(* The no-propose step preconditions *)
(* Note that this applies regardless of whether p = 1 *)
Definition no_propose_ok (pre : UState) uid v b r p : Prop :=
  pre.(timer) = 0%R /\
  valid_rps pre r p 1 /\
  (comm_cred_step uid r p 1 /\ valid_block_and_hash b v ->
    cert_may_exist pre \/ ~ v \in prev_certvals pre).

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
(* Victor: Technically, I think it would be correct to vote for your (non-bottom)
   starting value even if `~ cert_may_exist pre` *)

(* The no-softvoting step preconditions *)
(* Three reasons a user may not be able to soft-vote:
   - Not being in the soft-voting committee, or
   - Not being able to identify a potential leader value to soft-vote for
   - Not seeing enough next-votes for a value reproposed when the previous period
     had a quorum for bottom
 *)
(* Note that this may apply regardless of whether p = 1*)
Definition no_softvote_ok (pre : UState) uid v r p : Prop :=
  pre.(timer) = (2 * lambda)%R /\
  valid_rps pre r p 2 /\
  (comm_cred_step uid r p 2 ->
    ((cert_may_exist pre \/ ~ leader_prop_value v (pre.(proposals) r p))
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
  valid_rps pre r p 3 /\
  comm_cred_step uid r p 3 /\
  (p > 1 -> ~ cert_may_exist pre) /\
  valid_block_and_hash b v /\
  b \in pre.(blocks) r /\
  v \in certvals pre r p .

(* Certvoting step preconditions *)
(* The unsuccessful case *)
(* Notes: - The Algorand2 description does not explicitly specify what happens in this case
          - The timeout case is handled by a generic timeout transition given later
*)
(* Note the time period is left-closed unlike the algorand paper to easily allow
    checking whether the action should fire at the beginning of the time period *)
Definition no_certvote_ok (pre : UState) uid v b r p : Prop :=
  ((2 * lambda)%R <= pre.(timer) < lambda + big_lambda)%R /\
  valid_rps pre r p 3 /\
  (~ comm_cred_step uid r p 3 \/
   cert_may_exist pre \/
   ~ valid_block_and_hash b v \/
   ~ b \in pre.(blocks) r \/
   ~ v \in certvals pre r p).

(* Certvoting step's resulting user state (successful case) *)
(* The user has certvoted successfully, so move on to the next step and
   update the deadline *)
Definition certvote_result (pre : UState) : UState :=
  {[ {[ pre with step := 4 ]}
            with deadline := (lambda + big_lambda)%R ]}.

(* Certvoting step's resulting user state (unsuccessful case) *)
(* The user failed to certvote (at the beginning of the certvoting period)
   so update the deadline only (the step remains at 3 since the user may
   actually receive a message that would allow him to certvote then -- before
   the deadline *)
Definition no_certvote_result (pre : UState) : UState :=
  {[ pre with deadline := (lambda + big_lambda)%R ]}.

(** Steps >= 4: Nextvoting propositions and user state update **)

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
  valid_rps pre r p s /\
  comm_cred_step uid r p s /\
  valid_block_and_hash b v /\
  b \in pre.(blocks) r /\
  v \in certvals pre r p.

(* Nextvoting step preconditions *)
(* The bottom-value case *)
(* Notes: - Corresponds (roughly) to transition nextvote_open in the automaton
            model (but not the same) *)
(*        - Corresponds more closely to the Algorand2 description (but with the
            committee membership constraint)
          - Updated to accommodate the 27March change
 *)
Definition nextvote_open_ok (pre : UState) uid (v b : Value) r p s : Prop :=
  pre.(timer) = (lambda + big_lambda + (INR s - 4) * L)%R /\
  valid_rps pre r p s /\
  comm_cred_step uid r p s /\
  (~ b \in pre.(blocks) r \/
   ~ valid_block_and_hash b v \/
   ~ v \in certvals pre r p) /\
  (p > 1 -> nextvote_bottom_quorum pre r (p - 1) s ).

(* Nextvoting step preconditions *)
(* The aditional special case of using the starting value *)
(* Notes: - Not sure if this is captured in the automaton model *)
(*        - Corresponds more closely to the Algorand2 description (but with
            additional constraints given explicitly)
          - Updated to accommodate the 27March change
 *)
Definition nextvote_stv_ok (pre : UState) uid (v b : Value) r p s : Prop :=
  pre.(timer) = (lambda + big_lambda + (INR s - 4) * L)%R /\
  valid_rps pre r p s /\
  comm_cred_step uid r p s /\
  (~ b \in pre.(blocks) r \/
   ~ valid_block_and_hash b v \/
   ~ v \in certvals pre r p) /\
  p > 1 /\ ~ nextvote_bottom_quorum pre r (p - 1) s.

(* Nextvoting step preconditions *)
(* The no-voting case *)
Definition no_nextvote_ok (pre : UState) uid r p s : Prop :=
  pre.(timer) = (lambda + big_lambda + (INR s - 4) * L)%R /\
  valid_rps pre r p s /\
  ~ comm_cred_step uid r p s.

(* Nextvoting step state update for steps s >= 4 (all cases) *)
(* Note: Updated to accommodate the 27March change *)
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
  size [seq x <- (pre.(nextvotes_val) r p s) | matchValue x v]  >= tau_v.

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
  size [seq x <- pre.(certvotes) r p | matchValue x v] >= tau_c .

(* State update *)
Definition certify_result r (pre : UState) : UState := advance_round {[pre with round := r]}.

(** Timeout transitions **)

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
  | repropose : forall uid (pre : UState) v b r p,
      repropose_ok pre uid v b r p ->
      uid # pre ~> (propose_result pre, [:: (Reproposal, repr_val v uid p, r, p, uid)])

  (* Step 1: Block Proposal [failure] *)
  | no_propose : forall uid (pre : UState) v b r p,
      no_propose_ok pre uid v b r p ->
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

  (* Step 3: Certifying Step [failure] *)
  | no_certvote : forall uid (pre : UState) v b r p,
      no_certvote_ok pre uid v b r p ->
      uid # pre ~> (no_certvote_result pre, [::])

  (* Steps >= 4: Finishing Step - i has cert-voted some v *)
  | nextvote_val : forall uid (pre : UState) v b r p s,
      nextvote_val_ok pre uid v b r p s ->
      uid # pre ~> (nextvote_result pre s, [:: (Nextvote_Val, next_val v s, r, p, uid)])

  (* Steps >= 4: Finishing Step - i has not cert-voted some v *)
  | nextvote_open : forall uid (pre : UState) v b r p s,
      nextvote_open_ok pre uid v b r p s ->
      uid # pre ~> (nextvote_result pre s, [:: (Nextvote_Open, step_val s, r, p, uid)])

  (* Steps >= 4: Finishing Step - special case of using stv *)
  | nextvote_stv : forall uid (pre : UState) v v' b r p s,
      nextvote_stv_ok pre uid v b r p s /\ pre.(stv) p = Some v' ->
        uid # pre ~> (nextvote_result pre s, [:: (Nextvote_Val, next_val  v' s, r, p, uid)])

  (* Steps >= 4: Finishing Step - no next-voting *)
  | no_nextvote : forall uid (pre : UState) r p s,
      no_nextvote_ok pre uid r p s ->
      uid # pre ~> (nextvote_result pre s, [::])

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
     set_nextvotes_val adv_period_val_ok advance_period
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
Proof using.
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
Proof using.
move => increment pre.
by rewrite -updf_domf.
Qed.

Lemma tick_users_upd : forall increment pre uid (h : uid \in domf pre.(users)),
  (tick_users increment pre).[? uid] = Some (user_advance_timer increment pre.(users).[h]).
Proof using.
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

Definition send_broadcasts (now : R) (targets : {fset UserId}) (prev_msgs : MsgPool) (msgs : seq Msg) : MsgPool :=
  foldl (send_broadcast now targets) prev_msgs msgs.

(* Priority:LOW. may be a technical lemma for reasoning about broadcasts *)
Lemma send_broadcasts_domf : forall deadline targets prev_msgs msgs uids,
    domf prev_msgs `<=` uids ->
    targets `<=` uids ->
    domf (send_broadcasts deadline targets prev_msgs msgs) `<=` uids.
Admitted.

Definition onth {T : Type} (s : seq T) (n : nat) : option T :=
  ohead (drop n s).

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

Definition at_step n (path : seq GState) (P : pred GState) : bool :=
  match drop n path with
  | (g::_) => P g
  | [::] => false
  end.

Lemma at_step_onth n (path : seq GState) (P : pred GState):
  at_step n path P ->
  forall g, onth path n = Some g ->
  P g.
Proof using.
  unfold at_step, onth.
  destruct (drop n path);simpl;congruence.
Qed.

Lemma onth_at_step n (path : seq GState) g:
  onth path n = Some g ->
  forall (P : pred GState), P g -> at_step n path P.
Proof using.
  unfold at_step, onth.
  destruct (drop n path);simpl;congruence.
Qed.

(* Returns true if the given user id is found in the map and the user state
   corresponding to that id is for a corrupt user *)
Definition is_user_corrupt (uid : UserId) (users : {fmap UserId -> UState}) : bool :=
  if users.[? uid] is Some u then u.(corrupt) else false.

Definition is_user_corrupt_gstate (uid : UserId) (g : GState) : bool :=
  is_user_corrupt uid (g.(users)).

Definition user_honest (uid:UserId) (g:GState) : bool :=
  if g.(users).[? uid] is Some ustate then ~~ (ustate.(corrupt)) else false.

Definition user_honest_at ix path (uid : UserId) : bool :=
  at_step ix path (user_honest uid).

(* Returns the given users map restricted to honest users only *)
Definition honest_users (users : {fmap UserId -> UState}) :=
  let corrupt_ids :=
    [fset x in domf users | is_user_corrupt x users] in
    users.[\ corrupt_ids] .

Fixpoint seq2mset (T : choiceType) (msgs : seq T) : {mset T} :=
  match msgs with
  | [::]    => mset0
  | x :: xs => (x |` (seq2mset xs))%mset
  end.

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
  let msgh' := (pre.(msg_history)  `|` (seq2mset sent))%mset in
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
  let msgh' := (pre.(msg_history)  `|` (seq2mset sent))%mset in
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
  foldl (fun m x => f x +` m) mset0 m.

Lemma map_mset_count_inj {A B :choiceType} (f: A -> B) (m : {mset A}) :
  injective f -> forall (a :A), m a = (map_mset f m) (f a).
Proof using.
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
Proof using.
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

(* Constructs a message pool with all messages having missed delivery deadlines
   updated appropriately based on the message type *)
Definition reset_msg_delays (msgpool : MsgPool) now : MsgPool :=
  updf msgpool (domf msgpool) (fun _ msgs => reset_user_msg_delays msgs now).

Lemma reset_msg_delays_domf : forall (msgpool : MsgPool) now,
   domf msgpool = domf (reset_msg_delays msgpool now).
Proof using. by move => msgpool pre; rewrite -updf_domf. Qed.

Lemma reset_msg_delays_upd : forall (msgpool : MsgPool) now uid (h : uid \in domf msgpool),
  (reset_msg_delays msgpool now).[? uid] = Some (reset_user_msg_delays msgpool.[h] now).
Proof using.
move => msgpool now uid h.
have Hu := updf_update _ h.
have Hu' := Hu (domf msgpool) _ h.
by rewrite Hu'.
Qed.

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
Definition replay_msg_result (pre : GState) (uid : UserId) (msg : Msg) : GState :=
  let msgs' := send_broadcasts pre.(now) [fset uid] (* (domf (honest_users pre.(users))) *)
                 pre.(msg_in_transit) [:: msg] in
  {[ pre with msg_in_transit := msgs' ]}.

(* Does the adversary have the keys of the user for the given r-p-s? *)
(* The adversary will have the keys if the user is corrupt and the given
   r-p-s comes after (or is equal to) the r-p-s of the user *)
Definition have_keys ustate r p s : Prop :=
  ustate.(corrupt) /\
  (r > ustate.(round) \/
   r = ustate.(round) /\ p > ustate.(period) \/
   r = ustate.(round) /\ p = ustate.(period) /\ s >= ustate.(step)).

Definition mtype_matches_step mtype s : Prop :=
  match mtype with
  | Block | Proposal | Reproposal => s = 1
  | Softvote => s = 2
  | Certvote => s = 3
  | _ => s > 3
  end.

(* Computes the state resulting from forging a message to a user *)
(* The message is first created and then queued at the target user's mailbox *)
Definition forge_msg_result (pre : GState) (uid : UserId) r p mtype mval target : GState :=
  let msg := (mtype, mval, r, p, uid) in
  let msgs' := send_broadcasts pre.(now) [fset target] (* (domf (honest_users pre.(users))) *)
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
                          r p s mtype mval
                          target (target_key : target \in pre.(users)),
    ~ pre.(users).[target_key].(corrupt) ->
    have_keys pre.(users).[sender_key] r p s ->
    comm_cred_step sender r p s ->
    mtype_matches_step mtype s ->
    pre ~~> forge_msg_result pre sender r p mtype mval target

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

Lemma step_in_path_onth_pre {g1 g2 n path} (H_step : step_in_path_at g1 g2 n path)
  : onth path n = Some g1.
Proof using.
  unfold step_in_path_at in H_step.
  unfold onth. destruct (drop n path) as [|? []];destruct H_step.
  rewrite H;reflexivity.
Qed.

Lemma step_in_path_onth_post {g1 g2 n path} (H_step : step_in_path_at g1 g2 n path)
  : onth path n.+1 = Some g2.
Proof using.
  unfold step_in_path_at in H_step.
  unfold onth. rewrite -add1n -drop_drop.
  destruct (drop n path) as [|? []];destruct H_step.
  rewrite H0;reflexivity.
Qed.

(* definition of reachable global state via paths *)
Definition gtransition : rel GState := [rel x y | `[<GTransition x y>] ].

Definition greachable (g0 g : GState) : Prop := exists2 p, path gtransition g0 p & g = last g0 p.

(* classic definition of reachable global state *)

Definition GReachable (g0 g : GState) : Prop := clos_refl_trans_1n _ GTransition g0 g.

(* definitions are equivalent in our setting *)

Lemma greachable_GReachable : forall g0 g, greachable g0 g -> GReachable g0 g.
Proof using.
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
Proof using.
move => g0 g.
elim; first by move => x; exists [::].
move => x y z Hxy Hc.
case => p Hp Hl.
exists (y :: p) => //=.
apply/andP.
by split => //; apply/asboolP.
Qed.

Definition is_trace (path : seq GState) : Prop :=
  match path with
  | [::] => False
  | [:: g0 & rest] => path.path gtransition g0 rest
  end.

(* More definitions for stating that a state or transition exists along a path *)
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

Inductive GLabel : Type :=
| lbl_tick :  posreal -> GLabel
| lbl_deliver : UserId -> R -> Msg -> seq Msg -> GLabel
| lbl_step_internal : UserId -> seq Msg -> GLabel
| lbl_exit_partition : GLabel
| lbl_enter_partition : GLabel
| lbl_corrupt_user : UserId -> GLabel
| lbl_replay_msg : UserId -> GLabel
| lbl_forge_msg : UserId -> nat -> nat -> MType -> ExValue -> UserId -> GLabel.

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
  | lbl_forge_msg sender r p mtype mval target =>
      exists (sender_key : sender \in pre.(users)) (target_key : target \in pre.(users)) s,
      ~ pre.(users).[target_key].(corrupt)
      /\ have_keys pre.(users).[sender_key] r p s
      /\ comm_cred_step sender r p s
      /\ mtype_matches_step mtype s
      /\ post = forge_msg_result pre sender r p mtype mval target
  end.

Lemma utransition_internal_preserves_corrupt uid pre post sent:
  uid # pre ~> (post,sent) -> pre.(corrupt) = post.(corrupt).
Proof using.
  set result:=(post,sent). change post with (result.1). clearbody result.
  destruct 1;reflexivity.
Qed.

Lemma utransition_msg_preserves_corrupt uid msg pre post sent:
  uid # pre ; msg ~> (post,sent) -> pre.(corrupt) = post.(corrupt).
Proof using.
  set result:=(post,sent). change post with (result.1). clearbody result.
  destruct 1;try reflexivity.
  + unfold deliver_nonvote_msg_result;simpl.
    destruct msg as [[[[? ?] ?] ?] ?];simpl.
    destruct e;[destruct m|..];reflexivity.
Qed.

Definition msg_list_includes (m : Msg) (ms : seq Msg) : Prop :=
  m \in ms.

Definition user_sent sender (m : Msg) (pre post : GState) : Prop :=
  exists (ms : seq Msg), m \in ms
  /\ ((exists d incoming, related_by (lbl_deliver sender d incoming ms) pre post)
      \/ (related_by (lbl_step_internal sender ms) pre post)).

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

Lemma transitions_labeled: forall g1 g2,
    g1 ~~> g2 <-> exists lbl, related_by lbl g1 g2.
Proof using.
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
    exists (lbl_replay_msg uid);finish_case.
    exists (lbl_forge_msg sender r p mtype mval target);finish_case.
  + (* reverse - find transition from label *)
    destruct 1 as [[] Hrel];simpl in Hrel;decompose record Hrel;subst;econstructor;solve[eauto].
Qed.

(* Priority:MED This lemma is necessary for technical reasons to rule out
   the possibility that a step that counts as one user sending a message
   can't also count as a send from a different user or different message *)
Lemma transition_label_unique : forall lbl lbl2 g1 g2,
    related_by lbl g1 g2 ->
    related_by lbl2 g1 g2 ->
    lbl2 = lbl.
Proof using.
  move => lbl lbl2 g1 g2.
  destruct lbl eqn:H_lbl.
  * (* tick *)
    simpl.
    move => [H_ok1 ->].
    by destruct lbl2 eqn:H_lbl2;
      [ (* tick / tick *)
        move => [H_ok2 H_results];
        assert (pos p = pos p0)
          by (destruct g1;injection H_results;eauto using Rplus_eq_reg_l);
        clear -H;
        destruct p,p0;simpl in H;subst;
        repeat f_equal;
        apply Prop_irrelevance
      | (* Other cases can be refuted uniformly because no other action advances now *)
        by (simpl;intro H;decompose record H;
        match goal with [H : @eq GState _ _ |- _] =>
                        apply (f_equal now) in H;contradict H
        end;
        destruct g1;simpl;clear;destruct p;simpl;
        contradict cond_pos;apply Rplus_0_r_uniq in cond_pos;subst pos;apply Rlt_irrefl)
        ..
      ].
  + (* deliver *)
    simpl. (* one user changed, with a message removed from their mailbox *)
    admit.
  + (* step internal *)
    simpl. (* one user changed, no message removed *)
    admit.
  + (* exit partition *)
    move => [H_partitioned H_g2].
    assert (g1.(network_partition) <> g2.(network_partition))
      by (subst g2;destruct g1;simpl;clear;destruct network_partition;simpl;congruence).
    clear -H_partitioned H.
    unfold is_partitioned, is_true in H_partitioned.

    destruct lbl2;simpl;intro H_g2;try reflexivity; (* handles the exit/exit case *)
      decompose record H_g2;clear H_g2;subst g2;
        exfalso;destruct H;destruct g1;simpl in * |- *;try reflexivity. (* handles all but exit/enter *)
    destruct notF;subst;assumption.
  + (* enter *)
    move => [H_unpartitioned H_g2].
    assert (g1.(network_partition) <> g2.(network_partition))
      by (subst g2;destruct g1;simpl;clear;destruct network_partition;simpl;congruence).
    clear -H_unpartitioned H.
    apply Bool.negb_true_iff in H_unpartitioned.

    destruct lbl2;simpl;intro H_g2;try reflexivity; (* handles the exit/exit case *)
      decompose record H_g2;clear H_g2;subst g2;
        exfalso;destruct H;destruct g1;simpl in * |- *;try reflexivity. (* handles all but enter/exit *)
    destruct notF;subst;assumption.
  + (* corrupt user *)
    simpl.
    move => [ustate_key [H_honest ->]].
    {
      destruct lbl2;simpl;intro H;decompose record H;clear H.
      (* corrupt/tick *)
      apply (f_equal (fun g => g.(users).[? s])) in H1.
      destruct g1;unfold tick_update, tick_users in H1;cbn -[in_mem mem] in * |- *.
      rewrite fnd_set eq_refl updf_update in H1.
      exfalso. injection H1. revert H_honest. generalize (users.[ustate_key]). clear.
      unfold make_corrupt, user_advance_timer. destruct u, corrupt;simpl;done.
      assumption.
      (* corrupt /deliver *)
      {
        exfalso.
        match goal with
          [H_results : @eq GState _ _ |- _] => move/(f_equal (fun g => g.(users).[? s])): H_results
        end.
        destruct g1;autounfold with gtransition_unfold;cbn -[in_mem mem] in * |- *.
        rewrite fnd_set eq_refl.
        rewrite fnd_set.
        case (_ == _) eqn:H_eq.
        + move/eqP in H_eq. subst s0.
          injection 1 as <-.
          apply utransition_msg_preserves_corrupt in H0.
          exact (H1 H0).
        + rewrite in_fnd.
          injection 1. revert H_honest. generalize (users.[ustate_key]).
          clear. move => u H_honest. move/(f_equal corrupt).
          destruct u;simpl in * |- *. congruence.
      }
      (* corrupt / internal *)
      {
        match goal with
          [H_results : @eq GState _ _ |- _] => move/(f_equal (fun g => g.(users).[? s])): H_results
        end.
        destruct g1;autounfold with gtransition_unfold;cbn -[in_mem mem] in * |- *.
        rewrite fnd_set eq_refl.
        rewrite fnd_set.
        case (_ == _) eqn:H_eq.
        + move/eqP in H_eq. subst s0.
          injection 1 as <-.
          apply utransition_internal_preserves_corrupt in H1.
          exfalso;exact (H0 H1).
        + rewrite in_fnd.
          injection 1. revert H_honest. generalize (users.[ustate_key]).
          clear. move => u H_honest. move/(f_equal corrupt).
          destruct u;simpl in * |- *. congruence.
      }
      (* corrupt/exit *)
      {
        match goal with
          [H_results : @eq GState _ _ |- _] => move/(f_equal (fun g => g.(users).[? s])): H_results
        end.
        destruct g1;autounfold with gtransition_unfold;cbn -[in_mem mem] in * |- *.
        rewrite fnd_set eq_refl.
        rewrite in_fnd.
        injection 1. revert H_honest. generalize (users.[ustate_key]).
        clear. move => u H_honest. move/(f_equal corrupt).
        destruct u;simpl in * |- *;congruence.
      }
      (* corrupt/enter *)
      {
        match goal with
          [H_results : @eq GState _ _ |- _] => move/(f_equal (fun g => g.(users).[? s])): H_results
        end.
        destruct g1;autounfold with gtransition_unfold;cbn -[in_mem mem] in * |- *.
        rewrite fnd_set eq_refl.
        rewrite in_fnd.
        injection 1. revert H_honest. generalize (users.[ustate_key]).
        clear. move => u H_honest. move/(f_equal corrupt).
        destruct u;simpl in * |- *. congruence.
      }
      (* corrupt/corrupt *)
      { f_equal.
        match goal with
          [H_results : @eq GState _ _ |- _] => move/(f_equal (fun g => g.(users).[? s])): H_results
        end.
        destruct g1;autounfold with gtransition_unfold;cbn -[in_mem mem] in * |- *.
        rewrite fnd_set eq_refl.
        rewrite fnd_set.
        case (_ == _) eqn:H_eq.
        + clear 1. move/eqP: H_eq. clear;congruence.
        + rewrite in_fnd.
          injection 1. revert H_honest. generalize (users.[ustate_key]).
          clear. move => u H_honest. move/(f_equal corrupt).
          destruct u;simpl in * |- *. congruence.
      }
      (* corrupt/replay *)
      admit.
      (* corrupt/forge *)
      admit.
    }
  + (* replay *)
    admit.
  + (* forge *)
Admitted.

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

Definition honest_after_step (step:nat * nat * nat) uid (path : seq GState) :=
  exists n,
    match onth path n with
    | None => False
    | Some gstate =>
      match gstate.(users).[? uid] with
      | None => False
      | Some ustate => ~ustate.(corrupt)
       /\ step_lt step (step_of_ustate ustate)
      end
    end.

Lemma honest_after_le s1 s2 uid trace:
  step_le s1 s2 ->
  honest_after_step s2 uid trace ->
  honest_after_step s1 uid trace.
Proof.
  move => H_le.
  unfold honest_after_step.
  move => [n H_s2]. exists n.
  case:(onth trace n) H_s2 => [g|//].
  case:(g.(users).[?uid]) => [u [H_honest H_lt2]|//].
  apply (step_le_lt_trans H_le) in H_lt2.
  done.
Qed.

(* Priority:MED basic lemma for propagating honest backwards *)
Lemma user_honest_from_after g0 trace (H_path: path gtransition g0 trace):
  forall ix g1,
    onth trace ix = Some g1 ->
  forall uid (H_in : uid \in g1.(users)),
    honest_after_step (step_of_ustate (g1.(users)[`H_in])) uid trace ->
  user_honest uid g1.
Proof using.
Admitted.

Definition committee (r p s:nat) : {fset UserId} :=
  [fset uid : UserId | `[<committee_cred (credential uid r p s)>] ].

Definition quroum_honest_overlap_statement tau : Prop :=
  forall trace r p s (quorum1 quorum2 : {fset UserId}),
    quorum1 `<=` committee r p s ->
    #| quorum1 | >= tau ->
    quorum2 `<=` committee r p s ->
    #| quorum2 | >= tau ->
    exists honest_voter,
      honest_voter \in quorum1
      /\ honest_voter \in quorum2
      /\ honest_after_step (r,p,s) honest_voter trace.

Definition quorum_has_honest_statement tau : Prop :=
  forall trace r p s (quorum : {fset UserId}),
    quorum `<=` committee r p s ->
    #| quorum | >= tau ->
   exists honest_voter, honest_voter \in quorum /\
     honest_after_step (r,p,s) honest_voter trace.

Lemma quorum_has_honest_from_overlap_stmt tau:
  quroum_honest_overlap_statement tau ->
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
    #| quorum1 | >= tau1 ->
    (forall uid, uid \in quorum1 ->
     honest_after_step (r1,p1,s1) uid trace ->
     P uid) ->
  forall r2 p2 s2 (quorum2 : {fset UserId}),
    quorum2 `<=` committee r2 p2 s2 ->
    #| quorum2 | >= tau2 ->
    (exists honest_P_uid, honest_P_uid \in quorum2
     /\ P honest_P_uid
     /\ honest_after_step (r2,p2,s2) honest_P_uid trace).

Hypothesis quorums_b_honest_overlap : quroum_honest_overlap_statement tau_b.
Definition quorum_b_has_honest : quorum_has_honest_statement tau_b
  := quorum_has_honest_from_overlap_stmt quorums_b_honest_overlap.

Hypothesis quorums_c_honest_overlap : quroum_honest_overlap_statement tau_c.
Definition quorum_c_has_honest : quorum_has_honest_statement tau_c
  := quorum_has_honest_from_overlap_stmt quorums_c_honest_overlap.

Ltac unfold_step_result :=
  unfold tick_update, tick_users.

Lemma corrupt_preserved_ustep_msg : forall uid upre msg upost,
    uid # upre ; msg ~> upost ->
    upre.(corrupt) -> upost.1.(corrupt).
Proof using.
  destruct 1;simpl;try done.
  * (* Only one case remains *)
  unfold deliver_nonvote_msg_result;simpl.
  destruct msg as [[[[? ?] ?] ?] ?];simpl.
  destruct e;[destruct m|..];unfold set_blocks,set_proposals;simpl;done.
Qed.

Lemma corrupt_preserved_ustep_internal : forall uid upre upost,
    uid # upre ~> upost ->
    upre.(corrupt) -> upost.1.(corrupt).
Proof using.
  by destruct 1.
Qed.

Lemma honest_backwards_gstep : forall (g1 g2 : GState),
    GTransition g1 g2 ->
    forall uid, user_honest uid g2 ->
                user_honest uid g1.
Proof using.
  move => g1 g2 Hstep uid.
  destruct Hstep;unfold user_honest;destruct pre;
    unfold_step_result;simpl global_state.users in * |- *;try done.
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

Lemma honest_last_all uid g0 p (H_path : path gtransition g0 p):
    user_honest uid (last g0 p) ->
    all (user_honest uid) (g0::p).
Proof using.
  revert p H_path.
  induction p using last_ind;[by simpl;move => _ ->|].
  simpl. rewrite rcons_path last_rcons all_rcons.
  move => /andP [Hpath Hstep] H_x.
  specialize (IHp Hpath).
  rewrite H_x.
  apply IHp. by apply/honest_backwards_gstep /asboolP: H_x.
Qed.
Arguments honest_last_all uid [g0] [p].

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

Lemma path_drop T (R:rel T) x p (H:path R x p) n:
  match drop n p with
  | List.nil => true
  | List.cons x' p' => path R x' p'
  end.
Proof using.
  by elim: n x p H=> [|n IHn] x [|a l /andP [] H_path];last apply IHn.
Qed.


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

(* Priority:MED A structural lemma saying that if a message appears in a mailbox
   during a step and the sender is honest at the time then
   this step counts as "user_sent" for that message.

   However, this is invalidated by replay. Probably need to
   make the overall conclusion say that there was a send by the
   user at an earlier point in the trace.
 *)
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
    user_honest sender g0 ->
    user_sent sender msg g0 g1 \/ msg \in g0.(msg_history).
Proof using.
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

    left.
    unfold user_sent.
    exists sent.
    split;[assumption|].
    left.
    exists (pending.1). exists (pending.2).

    rewrite H2 in H_honest |- *.
    simpl.
    rewrite <- surjective_pairing.

    by repeat (esplit||eassumption).
  * (* internal step *)
    assert (msg \in sent). admit.
    assert (msg.2 = uid). admit.
    rewrite (surjective_pairing msg).
    rewrite <- surjective_pairing.
    intro H_honest.

    left.
    unfold user_sent.
    exists sent.
    split;[assumption|].
    right.

    rewrite H2 in H_honest |- *.
    simpl.

    by repeat (esplit||eassumption).
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
  * (* replay message *)
    admit.
  * (* forge message result *)
    admit.
Admitted.

Definition msg_step (msg:Msg) : nat * nat * nat :=
    let: (mtype,v,r_m,p_m,uid_m) := msg in
    (r_m,p_m,
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
     | Nextvote_Opem =>
       match v with
       | step_val s => s
       | _ => 111
       end
     end).

(* Priority:HIGH
   This lemma connects message receipt to the sending of a message,
   used to reach back to an earlier honest transition.
 *)
Lemma received_was_sent : forall (p: seq GState) g0 u d msg,
    path gtransition g0 p ->
    msg_received u d msg p ->
    let (_,sender) := msg in
    honest_after_step (msg_step msg) (sender:UserId) p ->
    exists ix g1 g2,
      step_in_path_at g1 g2 ix p
      /\ user_sent sender msg g1 g2.
Admitted.

Definition ustate_after us1 us2 : Prop :=
  us1.(round) < us2.(round)
  \/ (us1.(round) = us2.(round) /\ us1.(period) < us2.(period))
  \/ (us1.(round) = us2.(round) /\ us1.(period) = us2.(period) /\ us1.(step) <= us2.(step)).

Lemma ustate_after_iff_step_le u1 u2:
  step_le (step_of_ustate u1) (step_of_ustate u2)
  <-> ustate_after u1 u2.
Proof using.
  unfold ustate_after;destruct u1, u2;simpl.
  clear;tauto.
Qed.

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
  rewrite in_fnd in H_u. injection H_u;clear H_u. intros <-.

  remember (ustate_post,sent) as ustep_out in H_step.
  destruct H_step;injection Hequstep_out;clear Hequstep_out;intros <- <-;
    try (exfalso;exact (notF msg_in)).

  (* Only one delivery transition actually sends a message *)
  move/Iter.In_mem in msg_in;case: msg_in => [[*]|[]];subst.
  unfold certvote_ok in H;decompose record H;clear H.
  revert H0.
  clear;unfold pre',valid_rps;autounfold with utransition_unfold;simpl;clear.
  destruct pre;simpl;clear.
  move => [-> [->  ->]];reflexivity.
  }
  * { (* internal transition cases *)
    destruct H_step as (key_user & ustate_post & H_honest & H_step & ->).
    destruct g1;simpl in * |- *.
    rewrite in_fnd in H_u;injection H_u;clear H_u.
    intro H. rewrite -> H in * |- *. clear key_user users H.
    move/Iter.In_mem in msg_in.
    clear -msg_in H_step.

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
    end;clear;destruct pre;simpl;move=> [-> [-> ->]];reflexivity.
  }
Qed.

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
Proof using.
  move=> uid msg g1 g2.
  rewrite /user_sent.
  move => [sent [msg_in H_trans]] u H_u.
  change (msg \in sent:Prop) in msg_in.
  destruct msg as [[[[mtype v] r] p] uid_m].
  case: H_trans => [[d [body H_recv]]|H_step].
  * { (* message delivery cases *)
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
  end;simpl;
  match goal with
  | [H : valid_rps _ _ _ _ |- _] => move:H;unfold valid_rps;
      simpl;clear;
    by intuition;subst;intuition
  | _ => idtac
  end.
  }
  * { (* internal transition cases *)
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
    }
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

Definition sensible_gstate (gs : GState) : Prop :=
  (gs.(now) >= 0)%R /\
  ~ gs.(users) = [fmap] /\
  domf gs.(msg_in_transit) `<=` domf gs.(users) /\ (* needed? *)
  forall uid (k:uid \in gs.(users)), sensible_ustate gs.(users).[k].
  (* more constraints if we add corrupt users map and total message history *)

Lemma step_later_deadlines : forall s,
    s > 3 -> next_deadline s = (lambda + big_lambda + (INR s - 3) * L)%R.
Proof using.
  intros s H_s; clear -H_s.
  unfold next_deadline.
  do 3 (destruct s;[exfalso;apply not_false_is_true;assumption|]).
  reflexivity.
Qed.

(* The user transition relation preserves sensibility of user states *)
Lemma utr_msg_preserves_sensibility : forall uid us us' m ms,
  sensible_ustate us -> uid # us ; m ~> (us', ms) ->
  sensible_ustate us'.
Proof using delays_order.
  intros uid us us' m ms H_sensible Hstep;
  remember (us',ms) as ustep_output eqn:H_output;
  destruct Hstep; injection H_output; intros; subst;
  match goal with
  | [H_sensible : sensible_ustate ?s |- _] => is_var s;
     destruct s;unfold sensible_ustate in * |- *;
     decompose record H_sensible;clear H_sensible;simpl in * |- *
  end;
  autounfold with utransition_unfold in * |- *;
  match goal with
  | [H : context C [valid_rps] |- _] => unfold valid_rps in H;simpl in H;decompose record H
  | _ => idtac
  end;
  try by intuition lra.
  (* deliver nonvote msg needs some custom steps *)
  clear H_output.
  destruct msg as [[[[mtype ex_val] ?] ?] ?];
    destruct ex_val;simpl;[destruct mtype;simpl|..];intuition lra.
Qed.

(* Priority:LIVENESS *)
Lemma utr_nomsg_preserves_sensibility : forall uid us us' ms,
  sensible_ustate us -> uid # us ~> (us', ms) ->
  sensible_ustate us'.
Proof using delays_order delays_positive.
  let use_hyp H := (unfold valid_rps in H;simpl in H; decompose record H) in
  let tidy _ :=
  (match goal with
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
  try (
    match goal with
    | [H: propose_ok _ _ _ _ _ _ |- _] => unfold propose_ok in H; use_hyp H
    | [H: repropose_ok _ _ _ _ _ _ |- _] => unfold repropose_ok in H; use_hyp H
    | [H: no_propose_ok _ _ _ _ _ _ |- _] => unfold no_propose_ok in H; use_hyp H
    | [H: softvote_new_ok _ _ _ _ _ |- _] => unfold softvote_new_ok in H; use_hyp H
    | [H: softvote_repr_ok _ _ _ _ _ |- _] => unfold softvote_repr_ok in H; use_hyp H
    | [H: no_softvote_ok _ _ _ _ _ |- _] => unfold no_softvote_ok in H; use_hyp H
    | [H: certvote_ok _ _ _ _ _ _ |- _] => unfold certvote_ok in H; use_hyp H
    | [H: no_certvote_ok _ _ _ _ _ _ |- _] => unfold no_certvote_ok in H; use_hyp H
    | [H: nextvote_val_ok _ _ _ _ _ _ _ |- _] => unfold nextvote_val_ok in H; use_hyp H
    | [H: nextvote_open_ok _ _ _ _ _ _ _ |- _] => unfold nextvote_open_ok in H; use_hyp H
    | [H: nextvote_stv_ok _ _ _ _ _ _ _ /\ _ |- _] => destruct H as [H Hs]; unfold nextvote_stv_ok in H; use_hyp H
    | [H: no_nextvote_ok _ _ _ _ _ |- _] => unfold no_nextvote_ok in H; use_hyp H
    | [H: set_softvotes _ _ _ _ |- _] => unfold set_softvotes in H; use_hyp H
    | [H: timeout_ok _ |- _] => unfold timout_ok in H; use_hyp H
    | _ => idtac
    end;
    repeat (tidy ());intuition lra).
   - split => //; split => //.
     by admit.
   - split => //; split => //.
     by admit.
   - split => //; split => //.
     by admit.
   - split => //; split => //.
     by admit.
Admitted.

(* Priority:LIVENESS *)
(* The global transition relation preserves sensibility of global states *)
Lemma gtr_preserves_sensibility : forall gs gs',
  sensible_gstate gs -> gs ~~> gs' ->
  sensible_gstate gs'.
Proof using.
  let use_hyp H := (unfold valid_rps in H;simpl in H; decompose record H) in
  intros gs gs' H_sensible Hstep;
  destruct Hstep.

  * destruct pre. unfold tick_update, tick_users. simpl.
    admit.
  * apply utr_msg_preserves_sensibility in H1;
      [|unfold sensible_gstate in H_sensible;decompose record H_sensible;done].
    destruct pre;unfold sensible_gstate in * |- *.
    unfold delivery_result;simpl in * |- *.
    { intuition.
      * move :H7. clear.
        move/(f_equal (fun f => uid \in f)).
        change (uid \in ?f) with (uid \in domf f).
          by rewrite dom_setf fset1U1 in_fset0.
      * admit.
      * rewrite ffunE. simpl.
        set test := (uid0 == uid);destruct test eqn:H_eq;subst test.
        assumption.
        change (uid0 \in ?f) with (uid0 \in domf f) in k.
        rewrite dom_setf in_fset1U H_eq /= in k.
        by rewrite in_fnd;apply H8.
    }
  * apply utr_nomsg_preserves_sensibility in H0;
      [|unfold sensible_gstate in H_sensible;decompose record H_sensible;done].
    destruct pre;unfold sensible_gstate in * |- *.
    unfold step_result;simpl in * |- *.
    { intuition.
      * move:H6; clear.
        move/(f_equal (fun f => uid \in f)).
        change (uid \in ?f) with (uid \in domf f).
          by rewrite dom_setf fset1U1 in_fset0.
      * admit.
      * rewrite ffunE. simpl.
        set test := (uid0 == uid);destruct test eqn:H_eq;subst test.
        assumption.
        change (uid0 \in ?f) with (uid0 \in domf f) in k.
        rewrite dom_setf in_fset1U H_eq /= in k.
        by rewrite in_fnd;apply H7.
    }
  * (* recover from partition *)
    admit.
  * (* make partitioned *)
    admit.
  * (* corrupt user *)
    admit.
  * (* replay message *)
    admit.
  * (* forge message *)
Admitted.

(* Generalization of preservation of sensibility to paths *)
Lemma greachable_preserves_sensibility : forall g0 g,
  greachable g0 g -> sensible_gstate g0 -> sensible_gstate g.
Proof using.
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
Proof using.
  induction p;[done|].
  move => /= x n /andP [Hr Hpath].
  destruct n. done.
  simpl;apply /andP;by auto.
Qed.

(* An honest user may cert-vote only at step 3 of a period *)
(* Certvoting is enabled only at step 3 *)
Lemma certvote_only_in_step3 : forall us uid v b r p,
  certvote_ok us uid v b r p -> us.(step) = 3.
Proof using.
move => us uid v b r p Hc.
elim: Hc => tH [vH oH].
elim: vH => rH [pH sH].
by [].
Qed.

(* An honest user may soft-vote only at step 2 of a period *)
(* Softvoting is enabled only at step 2 *)
Lemma softvote_only_in_step2 : forall us v b r p,
  softvote_new_ok us v b r p -> us.(step) = 2 /\
  softvote_repr_ok us v b r p -> us.(step) = 2 .
Proof using.
move => us v b r p Hc.
elim: Hc => tH [vH oH].
elim: vH => rH [pH sH].
by [].
Qed.

(* State us2 is no earlier than state us1 in terms of round-period-step ordering *)

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
  do 2! [right]. do 2! [split; auto].
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
- case: H => vH oH.
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto].
  rewrite addn1. by subst.
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
  move => sender_key r p s mtype mval target target_key Hc Hhave Hcomm Hmatch.
  rewrite /= =>->; case =>->.
  by right; right.
Qed.

Lemma gtr_users_non_decreasing g1 g2 (H_step: GTransition g1 g2):
  forall uid, uid \in g1.(users) -> uid \in g2.(users).
Proof using.
  intro uid.
  repeat match goal with | [|- context C [uid \in ?f]] => change (uid \in f) with (uid \in domf f) end.
  destruct H_step;destruct pre;autounfold with gtransition_unfold;cbn;
    [rewrite -updf_domf| try (rewrite dom_setf;apply fset1Ur)..];done.
Qed.

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

Lemma gtrans_domf_users : forall gs1 gs2,
  gs1 ~~> gs2 -> domf gs1.(users) `<=` domf gs2.(users).
Proof using.
move => gs1 gs2.
elim => //.
- move => increment pre Htick.
  apply/fsubsetP => x Hd.
  by rewrite -tick_users_domf.
- move => pre uid msg_key pending Hpending key_ustate ustate_post sent Hcorrupt Huser /=.
  by apply/fsubsetP => x Hd; apply: fset1Ur.
- move => pre uid ustate_key Hcorrupt ustate_post sent Huser /=.
  by apply/fsubsetP => x Hd; apply: fset1Ur.
- move => pre uid ustate_key Hcorrupt /=.
  by apply/fsubsetP => x Hd; apply: fset1Ur.
Qed.

(* Generalization of non-decreasing round-period-step results to paths *)
Lemma greachable_rps_non_decreasing : forall g1 g2 uid us1 us2,
  greachable g1 g2 ->
  g1.(users).[? uid] = Some us1 -> g2.(users).[? uid] = Some us2 ->
  ustate_after us1 us2.
Proof using.
move => g1 g2 uid us1 us2.
case => gtrace Hpath Hlast.
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

Definition user_sent_at ix path uid msg :=
  exists g1 g2, step_in_path_at g1 g2 ix path
                /\ user_sent uid msg g1 g2.

(* A user has certvoted a value for a given period along a given path *)
Definition certvoted_in_path_at ix path uid r p v : Prop :=
  user_sent_at ix path uid (Certvote,val v,r,p,uid).

Definition certvoted_in_path path uid r p v : Prop :=
  exists ix, certvoted_in_path_at ix path uid r p v.

Definition certified_in_period trace r p v :=
  exists (certvote_quorum:{fset UserId}),
     certvote_quorum `<=` committee r p 3
  /\ #| certvote_quorum | >= tau_c
  /\ forall (voter:UserId), voter \in certvote_quorum ->
       certvoted_in_path trace voter r p v.

Definition softvoted_in_path_at ix path uid r p v : Prop :=
  exists g1 g2, step_in_path_at g1 g2 ix path
   /\ user_sent uid (Softvote,val v,r,p,uid) g1 g2.

Definition softvoted_in_path path uid r p v : Prop :=
  exists ix, softvoted_in_path_at ix path uid r p v.

Definition enough_softvotes_in_period trace r p v :=
  exists (softvote_quorum:{fset UserId}),
     softvote_quorum `<=` committee r p 2
  /\ #| softvote_quorum | >= tau_s
  /\ forall (voter:UserId), voter \in softvote_quorum ->
       softvoted_in_path trace voter r p v.

Definition nextvoted_bot_in_path_at ix path uid (r p s:nat) : Prop :=
  exists g1 g2, step_in_path_at g1 g2 ix path
   /\ user_sent uid (Nextvote_Open, step_val s,r,p,uid) g1 g2.

Definition nextvoted_bot_in_path path uid r p s : Prop :=
  exists ix, nextvoted_bot_in_path_at ix path uid r p s.

Definition enough_nextvotes_bot_in_step trace r p s :=
  exists (nextvote_quorum:{fset UserId}),
     nextvote_quorum `<=` committee r p s
  /\ #| nextvote_quorum | >= tau_b
  /\ forall (voter:UserId), voter \in nextvote_quorum ->
       nextvoted_bot_in_path trace voter r p s.

Definition nextvoted_val_in_path_at ix path uid r p s v : Prop :=
  exists g1 g2, step_in_path_at g1 g2 ix path
   /\ user_sent uid (Nextvote_Val,next_val v s,r,p,uid) g1 g2.

Definition nextvoted_val_in_path path uid r p s v : Prop :=
  exists ix, nextvoted_val_in_path_at ix path uid r p s v.

Definition enough_nextvotes_val_in_step trace r p s v :=
  exists (nextvote_quorum:{fset UserId}),
     nextvote_quorum `<=` committee r p s
  /\ #| nextvote_quorum | >= tau_b
  /\ forall (voter:UserId), voter \in nextvote_quorum ->
       nextvoted_val_in_path trace voter r p s v.

Lemma vote_value_unique uid r p g1 g2 v:
  user_sent uid (Certvote,val v,r,p,uid) g1 g2 ->
  user_honest uid g1 ->
  forall v2, user_sent uid (Certvote,val v2,r,p,uid) g1 g2 -> v2 = v.
Proof using.
  move => H_sent H_honest v2 H_sent2.
  unfold user_sent in H_sent, H_sent2.
  destruct H_sent as [ms [H_msg [[d1 [in1 H_step]]|H_step]]];
  destruct H_sent2 as [ms2 [H_msg2 [[d2 [in2 H_step2]]|H_step2]]];
  pose proof (transition_label_unique H_step H_step2) as H;
  try (discriminate H);[injection H as -> -> ->|injection H as ->];clear H_step2;
    revert H_msg H_msg2;simpl in H_step;decompose record H_step;
    let H:=  match goal with
    | [H : _ # _ ; _ ~> _ |- _] => H
    | [H : _ # _ ~> _ |- _] => H
    end
    in clear -H;set result := (x0,ms) in H;change ms with result.2;clearbody result;revert H;
  destruct 1;simpl;clear;move/Iter.In_mem => H_msg;try (exfalso;exact H_msg);
     move/Iter.In_mem => H_msg2;simpl in H_msg, H_msg2;intuition congruence.
Qed.

Lemma step_at_nth_pre pre post ix path:
  step_in_path_at pre post ix path ->
  forall x0, nth x0 path ix = pre.
Proof using.
  clear.
  unfold step_in_path_at.
  elim: ix path => [|n IHn] [] //= a [];tauto.
Qed.

Lemma step_at_nth_post pre post ix path:
  step_in_path_at pre post ix path ->
  forall x0, nth x0 path (ix.+1) = post.
Proof using.
  clear.
  unfold step_in_path_at.
  elim: ix path => [|n IHn] [] //= a [];tauto.
Qed.

Lemma onth_nth T (s:seq T) ix x:
  onth s ix = Some x -> (forall x0, nth x0 s ix = x).
Proof using.
  unfold onth.
  unfold ohead.
  move => H_drop x0.
  rewrite -[ix]addn0 -nth_drop.
  destruct (drop ix s);simpl;congruence.
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


Lemma at_greachable
      g0 states (H_path: path gtransition g0 states)
      ix1 ix2 (H_le : ix1 <= ix2)
      g1 (H_g1 : onth states ix1 = Some g1)
      g2 (H_g2 : onth states ix2 = Some g2):
  greachable g1 g2.
Proof using.
  assert (ix2 < size states) by
  (rewrite -subn_gt0 -size_drop;
   move: H_g2;clear;unfold onth;
   by destruct (drop ix2 states)).

  exists (drop ix1.+1 (take ix2.+1 states)).
  {
    apply (path_prefix ix2.+1) in H_path.
    have:= (path_drop H_path ix1).
    simpl.
    rewrite {1}(drop_nth g2);[|by rewrite size_takel].
    rewrite nth_take //.
    rewrite (onth_nth H_g1).
    done.
  }
  {
     rewrite (last_nth g1) size_drop size_takel //.
     move:(H_le). rewrite leq_eqVlt.
     move/orP => [H_eq | H_lt].
     by move/eqP in H_eq;subst;rewrite subnn;simpl;congruence.
     by rewrite subSn //= nth_drop subnKC // nth_take ?ltnS // (onth_nth H_g2).
  }
Qed.

Lemma order_ix_from_steps g0 trace (H_path: path gtransition g0 trace):
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

Lemma steps_greachable
      g0 path (H_path : path.path gtransition g0 path)
      ix ix2 (H_lt : ix < ix2)
      pre post (H_step : step_in_path_at pre post ix path)
      pre2 post2 (H_step2 : step_in_path_at pre2 post2 ix2 path):
  greachable post pre2.
Proof using.
  apply step_in_path_onth_post in H_step.
  apply step_in_path_onth_pre in H_step2.
  eapply at_greachable;eassumption.
Qed.

Lemma order_state_from_step g0 states (H_path: path gtransition g0 states) uid
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

Lemma order_sends g0 trace (H_path: path gtransition g0 trace) uid
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

Lemma step_ix_same trace ix g1 g2:
    step_in_path_at g1 g2 ix trace ->
    forall g3 g4,
    step_in_path_at g3 g4 ix trace ->
      g3 = g1 /\ g4 = g2.
Proof using.
  clear.
  unfold step_in_path_at.
  destruct (drop ix trace) as [|? [|]];(tauto || intuition congruence).
Qed.

(* L1: An honest user cert-votes for at most one value in a period *)
(* :: In any global state, an honest user either never certvotes in a period or certvotes once in step 3 and never certvotes after that during that period
   :: If an honest user certvotes in a period (step 3) then he will never certvote again in that period *)
Lemma no_two_certvotes_in_p : forall g0 trace (H_path : path gtransition g0 trace) uid r p,
    forall ix1 v1, certvoted_in_path_at ix1 trace uid r p v1 ->
                   user_honest_at ix1 trace uid ->
    forall ix2 v2, certvoted_in_path_at ix2 trace uid r p v2 ->
                   user_honest_at ix2 trace uid ->
                   ix1 = ix2 /\ v1 = v2.
Proof using.
  move => g0 trace H_path uid r p.
  move => ix1 v1 H_send1 H_honest1.
  move => ix2 v2 H_send2 H_honest2.

  have: ix1 <= ix2 by
  eapply (order_sends H_path H_send1 H_send2 (step_le_refl _)).
  have: ix2 <= ix1 by
  eapply (order_sends H_path H_send2 H_send1 (step_le_refl _)).

  move => H_le1 H_le2.
  have: ix1 = ix2.
  apply/eqP. rewrite eqn_leq. apply/andP. split;assumption.
  intro;subst ix2;clear H_le1 H_le2.
  split;[reflexivity|].

  unfold certvoted_in_path_at in H_send1, H_send2.
  destruct H_send1 as [pre1 [post1 [H_step1 H_send1]]].
  destruct H_send2 as [pre2 [post2 [H_step2 H_send2]]].

  destruct (step_ix_same H_step1 H_step2) as [-> ->].
  symmetry.
  refine (vote_value_unique H_send1 _ H_send2).
  exact (at_step_onth H_honest1 (step_in_path_onth_pre H_step1)).
Qed.

(* A user has softvoted for one value exactly once for a given period along a given path *)
Definition softvoted_once_in_path path r p uid : Prop :=
  exists ix v, softvoted_in_path_at ix path uid r p v
  /\ forall ix' v',
     softvoted_in_path_at ix' path uid r p v' -> ix = ix' /\ v = v'.

Lemma take_rcons T : forall (s : seq T) (x : T), take (size s) (rcons s x) = s.
Proof using. elim => //=; last by move => a l IH x; rewrite IH. Qed.

(* Priority:HIGH
   Proof should be very similar to no_two_certvotes_in_p *)
(* L2: An honest user soft-votes for at most one value in a period *)
Lemma no_two_softvotes_in_p : forall path uid r p,
  softvoted_once_in_path path r p uid \/ forall v, ~ softvoted_in_path path uid r p v.
Proof using.
(* once a user softvotes (certvotes) in step 2 (3), the user moves on to subsequent steps and never softvotes (certvotes) again in that period. *)
(* appeal to steps being nondecreasing *)
Admitted.

(* A user has nextvoted bottom for a given period along a given path *)
Definition nextvoted_open_in_path trace r p s uid : Prop :=
  exists ix g1 g2,
  step_in_path_at g1 g2 ix trace
  /\ user_sent uid (Nextvote_Open, step_val s, r, p, uid) g1 g2.

(* A user has nextvoted a value for a given period along a given path *)
Definition nextvoted_value_in_path trace r p s uid v : Prop :=
  exists ix g1 g2,
  step_in_path_at g1 g2 ix trace
  /\ user_sent uid (Nextvote_Val, next_val v s, r, p, uid) g1 g2.

(* Priority:HIGH
   Top-level result,
   just need to compare message steps to show any nextvote must have come
   after certvote,
   examine user state at/after certvote to note it saw softvotes,
   examine state before nextvote to show open nextvote means not enough
   softvotes, and appeal to monotonicity of the observations.
 *)
(* L3: If an honest user cert-votes for a value in step 3, the user will NOT next-vote bottom in the same period
*)
Lemma certvote_excludes_nextvote_open_in_p path uid r p s v:
  honest_after_step (r,p,s) uid path ->
  certvoted_in_path path uid r p v -> ~ nextvoted_open_in_path path r p s uid .
Proof using.
  move => H_honest [ix_cv [g1_cv [g2_cv [H_step_cv H_vote_cv]]]]
                   [ix_nv [g1_nv [g2_nv [H_step_nv H_vote_nv]]]].
Admitted.

(* Priority:HIGH
   Top-level result,
   much structure can be shared with nextvoted_value_in_path
 *)
(* L3’: If an honest user cert-votes for a value in step 3, the user can only next-vote that value in the same period *)
Lemma certvote_nextvote_value_in_p : forall path uid r p v v',
  certvoted_in_path path uid r p v ->
  forall s, nextvoted_value_in_path path r p s uid v' ->
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
  step_lt (step_of_ustate ustate1) (r,p,1)
  /\ step_of_ustate ustate2 = (r,p,1)}}.

(* Priority:MED
   Structural lemma about advancement
 *)
Lemma period_advance_only_by_next_votes : forall path uid r p,
    forall n,
    (exists g1 g2, period_advance_at n path uid r p g1 g2) ->
    let path_prefix := take n.+2 path in
    exists (s:nat) (v:option Value) (next_voters:{fset UserId}),
      next_voters `<=` committee r p.-1 s
      /\ tau_b <= #| next_voters |
      /\ forall voter, voter \in next_voters ->
         received_next_vote uid voter r p.-1 s v path_prefix.
Admitted.

(* L5.1 Any set of tau_b committee  members must include at least one honest node,
        defined earlier as quorum_b_has_honest *)
Definition honest_in_period (r p:nat) uid path :=
  exists n,
    match @onth GState path n with
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
  destruct H_adv as (s & v & next_voters & H_voters_cred & H_voters_size & ?).
  pose proof (path_prefix n.+2 H_path) as H_path_prefix.
  destruct (@quorum_b_has_honest (take n.+2 trace) r p.-1 s next_voters H_voters_cred H_voters_size)
    as (uid_honest & H_honest_voter & H_honest).
  exists uid_honest.
  specialize (H uid_honest H_honest_voter).
  unfold received_next_vote in H.
  destruct H as [d H].
  pose proof (received_was_sent H_path_prefix H) as H1.
  cbn -[user_sent step_in_path_at msg_step] in H1.
  lapply H1;[clear H1|destruct v;assumption].
  intros (ix & g1 & g2 & H_step & H_sent).
  unfold honest_in_period;exists ix.
  have H_onth:= step_in_path_onth_pre H_step.
  rewrite (onth_from_prefix H_onth).
  have H_user_in := user_sent_in_pre H_sent.
  rewrite (in_fnd H_user_in).
  have H_start_label := utransition_label_start H_sent (in_fnd H_user_in).

  split.
  { (* Honest at ix *)
  suff: (user_honest uid_honest g1)
      by unfold user_honest;rewrite in_fnd;move/negP.
  apply (user_honest_from_after H_path_prefix H_onth (H_in:=H_user_in)).
  rewrite H_start_label.
  revert H_honest.
  apply honest_after_le .
  destruct v;apply step_le_refl.
  }
  {
    move: (g1.(users)[`H_user_in]) H_start_label => u. clear.
    destruct u;simpl. clear. case. by destruct v;case.
  }
Qed.

(* To show there is not a fork in a particular round,
   we will take a history that extends before any honest
   node has made a transition in that round *)
Definition user_before_round r (u : UState) : Prop :=
  (u.(round) < r \/
   (u.(round) = r /\
    u.(step) = 1 /\ u.(period) = 1 /\ u.(timer) = 0%R /\ u.(deadline) = 0%R))
  /\ (forall r' p, r <= r' -> nilp (u.(proposals) r' p))
  /\ (forall r', r <= r' -> nilp (u.(blocks) r'))
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

Definition users_at ix path : {fmap UserId -> UState} :=
  match drop ix path with
  | g1 :: _ => g1.(users)
  | _ => [fmap]
  end.

Definition user_stv_val (uid:UserId) (g:GState) (p:nat) (stv':option Value) : bool :=
  if g.(users).[? uid] is Some ustate then ustate.(stv) p == stv' else false.

Definition user_stv_val_at ix path uid p stv : bool :=
  match drop ix path with
  | g1 :: _ => user_stv_val uid g1 p stv
  | _ => false
  end.

(* D1: an honest node enters a period exclusively for value v *)
(* if it enters the period with starting value $v$ *)
(* and has not observed t_H next-votes for $\bot$ from any single step of the previous period *)
Definition enters_exclusively_for_value (uid : UserId) (r p : nat) (v : Value) path :=
  exists g1 g2 n, period_advance_at n path uid r p g1 g2 /\
  exists ustate, g2.(users).[? uid] = Some ustate /\
  ~ ustate.(corrupt) /\ ustate.(stv) p = Some v /\
  forall s, size (ustate.(nextvotes_open) r p.-1 s) < tau_b.

Lemma stv_forward
      g1 g2 (H_reach : greachable g1 g2)
      uid u1 u2 p v:
  g1.(users).[?uid] = Some u1 ->
  u1.(stv) p = Some v ->
  g2.(users).[?uid] = Some u2 ->
  u1.(round) = u2.(round) ->
  u2.(stv) p = Some v.
Proof using.
Admitted.

(* main subargument for excl_enter_limits_cert_vote *)
Lemma honest_certvote_respects_stv uid g1 g2 v v' r p u:
  g1.(users).[?uid] = Some u ->
  u.(stv) p = Some v ->
  user_honest uid g1 ->
  user_sent uid (Certvote, val v', r, p, uid) g1 g2 ->
  v' = v.
Proof using.
Admitted.

(* L6: if all honest nodes that entered a period p >= 2 did so exclusively for value v *)
(* then an honest node cannot cert-vote for any value other than v in step 3 of period p'. *)
Lemma excl_enter_limits_cert_vote :
  forall g0 trace (H_path: path gtransition g0 trace),
  forall (r p : nat) (v : Value),
    p >= 1 ->
    forall (uid : UserId),
      honest_after_step (r,p,3) uid trace ->
      enters_exclusively_for_value uid r p v trace ->
      forall v', certvoted_in_path trace uid r p v' -> v' = v.
Proof using.
  clear.
  move => g0 trace H_path r p v H_p uid H_honest H_excl v' H_vote.
  destruct H_vote as [ix_vote H_vote].
  unfold certvoted_in_path_at in H_vote.

  destruct H_excl as (g1 & g2 & ix_enter & H_enter & ustate_enter &
                      H_lookup_enter & H_honest_enter & H_stv & H_not_open).
  move:H_enter => [H_enter_step H_enter].
  destruct H_vote as (g1_v & g2_v & H_vote_step & H_vote_send).

  assert (ix_enter < ix_vote) as H_order.
  {
    clear -H_path H_enter_step H_enter H_vote_step H_vote_send.

    rewrite ltnNge leq_eqVlt. apply/negP => /orP [/eqP H_eq | H_lt].
    * (* Exclude equality *)
      rename ix_vote into ix;subst ix_enter.
      replace g1_v with g1 in * |- *
        by rewrite -(step_at_nth_pre H_enter_step g0) -(step_at_nth_pre H_vote_step g0) //.
      replace g2_v with g2 in * |- *
        by rewrite -(step_at_nth_post H_enter_step g0) -(step_at_nth_post H_vote_step g0) //.
      move: H_enter => [ekey1 [_ [H_pre _]]].
      pose proof (utransition_label_start H_vote_send (in_fnd ekey1)).
      move:H_pre; rewrite H /msg_step /step_lt; clear.
      rewrite !ltnn.
      by intuition.
    * move: H_enter => [ukey_1 [ukey_2 [H_enter_lt H_enter_eq]]].
      set ustate1: UState := g1.(users)[`ukey_1] in H_enter_lt.
      set ustate2: UState := g2.(users)[`ukey_2] in H_enter_eq.
      move: H_lt. apply/negP. rewrite -leqNgt.
      clear ukey_2 ustate2 H_enter_eq.
      (* Deduce this by looking at the step order *)
      apply ltnW.
      have H_uv := (in_fnd (user_sent_in_pre H_vote_send)).
      eapply (order_state_from_step H_path
                                    (step_in_path_onth_pre H_enter_step) (in_fnd ukey_1)
                                    (step_in_path_onth_pre H_vote_step) H_uv).
      rewrite -/ustate1 (utransition_label_start H_vote_send H_uv).
      apply (step_lt_le_trans H_enter_lt).
      simpl;clear. by intuition.
  }
  have H_reach: greachable g2 g1_v
    := steps_greachable H_path H_order H_enter_step H_vote_step.

  have H_in := user_sent_in_pre H_vote_send.

  assert ((g1_v.(users)[`H_in]).(stv) p = Some v) as H_stv_send.
  {
  move: H_enter => [_ [ukey_2 [_ H_step_g2]]].

  refine (stv_forward H_path H_reach H_lookup_enter (in_fnd H_in) _ H_stv).

  rewrite (in_fnd ukey_2) in H_lookup_enter.
  move: H_lookup_enter => [] <-.
  have := utransition_label_start H_vote_send (in_fnd H_in).

  case: H_step_g2 => -> _ _. case => -> _ _.
  reflexivity.
  }

  (* analyze certvote step precondition *)
  assert (H_honest_send: user_honest uid g1_v).
  {
    rewrite -[(r,p,3)](utransition_label_start H_vote_send (in_fnd H_in)) in H_honest.
    exact (user_honest_from_after H_path (step_in_path_onth_pre H_vote_step) H_honest).
  }
  clear -H_vote_send H_stv_send H_honest_send.
  exact (honest_certvote_respects_stv (in_fnd H_in) H_stv_send H_honest_send H_vote_send).
Qed.

(* A message from an honest user was actually sent in the trace *)
(* Use this to relate an honest user having received a quorum of messages
   to some honest user having sent those messages *)
(* Hopefully the statement can be cleaned up *)
Lemma pending_honest_sent : forall g0 trace (H_path: path gtransition g0 trace),
    forall r, state_before_round r g0 ->
    forall g_pending pending_ix,
      onth trace pending_ix = Some g_pending ->
    forall uid (key_msg : uid \in g_pending.(msg_in_transit)) pending,
      pending \in g_pending.(msg_in_transit).[key_msg] ->
    let (_,pending_msg) := pending in
    let: (_,_,r',_,sender) := pending_msg in
    honest_after_step (msg_step pending_msg) sender trace ->
    r <= r' ->
    exists send_ix g1 g2,
      step_in_path_at g1 g2 send_ix trace
      /\ user_sent sender pending_msg g1 g2.
Admitted.

Lemma honest_at_from_at_step r p s uid trace:
      honest_at_step r p s uid trace ->
      forall g0 (H_path: path gtransition g0 trace),
      forall n g, onth trace n = Some g ->
      forall u, g.(users).[? uid] = Some u ->
      step_lt (step_of_ustate u) (r,p,s) ->
      user_honest_at n trace uid.
Proof using.
  move => H_honest g0 H_path n g H_at u H_lookup H_lt.

  move: H_honest.
  unfold honest_after_step.
  move => [n_honest].
  destruct (onth trace n_honest) as [g2|] eqn:H_g2;[|done].
  destruct (g2.(users).[?uid]) as [ustate|] eqn:H_ustate;[|done].
  move => [H_honest_later H_step_eq].

  pose proof H_lt as H_step_before. rewrite H_step_eq in H_step_before.

  assert (n < n_honest) by (eapply order_state_from_step;eassumption).

  apply (path_prefix n_honest.+1) in H_path.

  pose proof (onth_size H_g2).
  have H_size_take:= size_takel H0.
  lapply (honest_last_all uid H_path).
  simpl. move/andP => [_].
  * {
    unfold user_honest_at.
    move/all_nthP => H_all.
    specialize (H_all g n).
    rewrite H_size_take ltnS in H_all.
    specialize (H_all (ltnW H)).

    apply (onth_at_step H_at). simpl.

    revert H_all.
    pose proof (ltnW H).
    by rewrite nth_take // (onth_nth H_at).
  }
  * {
    rewrite (last_nth g0).
    rewrite size_takel //= nth_take // (onth_nth H_g2).
    rewrite /user_honest H_ustate. by apply/negP.
  }
Qed.

Lemma honest_at_from_after r p s uid trace:
      honest_after_step (r,p,s) uid trace ->
      forall g0 (H_path: path gtransition g0 trace),
      forall n g, onth trace n = Some g ->
      forall u, g.(users).[? uid] = Some u ->
      step_le (step_of_ustate u) (r,p,s) ->
      user_honest_at n trace uid.
Proof using.
  move => H_honest g0 H_path n g H_at u H_lookup H_le.

  move: H_honest.
  unfold honest_after_step.
  move => [n_honest].
  destruct (onth trace n_honest) as [g2|] eqn:H_g2;[|done].
  destruct (g2.(users).[?uid]) as [ustate|] eqn:H_ustate;[|done].
  move => [H_honest_later H_le2].

  have H_step_before := step_le_lt_trans H_le H_le2.
  assert (n < n_honest) by (eapply order_state_from_step;eassumption).

  apply (path_prefix n_honest.+1) in H_path.

  pose proof (onth_size H_g2).
  have H_size_take:= size_takel H0.
  lapply (honest_last_all uid H_path).
  simpl. move/andP => [_].
  * {
    unfold user_honest_at.
    move/all_nthP => H_all.
    specialize (H_all g n).
    rewrite H_size_take ltnS in H_all.
    specialize (H_all (ltnW H)).

    apply (onth_at_step H_at). simpl.

    revert H_all.
    pose proof (ltnW H).
    by rewrite nth_take // (onth_nth H_at).
  }
  * {
    rewrite (last_nth g0).
    rewrite size_takel //= nth_take // (onth_nth H_g2).
    rewrite /user_honest H_ustate. by apply/negP.
  }
Qed.

Lemma one_certificate_per_period: forall g0 trace r p,
    state_before_round r g0 ->
    path gtransition g0 trace ->
    forall v1, certified_in_period trace r p v1 ->
    forall v2, certified_in_period trace r p v2 ->
    v1 = v2.
Proof using quorums_c_honest_overlap.
  clear -quorums_c_honest_overlap.
  intros g0 trace r p H_start H_path v1 H_cert1 v2 H_cert2.
  destruct H_cert1 as (quorum1 & H_q1 & H_size1 & H_cert1).
  destruct H_cert2 as (quorum2 & H_q2 & H_size2 & H_cert2).
  pose proof (quorums_c_honest_overlap trace H_q1 H_size1 H_q2 H_size2).
  destruct H as (voter & H_common1 & H_common2 & H_honest).
  specialize (H_cert1 _ H_common1).
  specialize (H_cert2 _ H_common2).
  destruct H_cert1 as [ix1 H_cert1].
  destruct H_cert2 as [ix2 H_cert2].

  assert (user_honest_at ix1 trace voter) as H_honest1. {
  move: H_cert1.
  unfold certvoted_in_path_at. move => [g1 [g2 [H_step H_vote]]].

  pose proof (in_fnd (user_sent_in_pre H_vote)) as H0.
  set ustate := g1.(users)[`user_sent_in_pre H_vote] in H0.
  clearbody ustate.
  have H1: (step_of_ustate ustate) = (r,p,3) := utransition_label_start H_vote H0.

  pose proof (honest_at_from_after H_honest H_path) as H.
  specialize (H _ _ (step_in_path_onth_pre H_step)).
  specialize (H _ H0).
  apply H.
  rewrite H1.
  apply step_le_refl.
  }

  assert (user_honest_at ix2 trace voter) as H_honest2. {
  move: H_cert2.
  unfold certvoted_in_path_at. move => [g1 [g2 [H_step H_vote]]].
  pose proof (honest_at_from_after H_honest H_path) as H.
  specialize (H _ _ (step_in_path_onth_pre H_step)).
  pose proof (in_fnd (user_sent_in_pre H_vote)).
  set ustate := g1.(users)[`user_sent_in_pre H_vote] in H0.
  clearbody ustate.
  specialize (H _ H0).
  apply H.
  rewrite (utransition_label_start H_vote H0);apply step_le_refl.
  }

  by destruct (no_two_certvotes_in_p H_path H_cert1 H_honest1 H_cert2 H_honest2).
Qed.

Lemma certificate_is_start_of_later_periods:
  forall trace r p v,
    certified_in_period trace r p v ->
  forall p', p' > p ->
    forall uid g1 g2 n,
      period_advance_at n trace uid r p' g1 g2 ->
      user_honest uid g1 ->
      enters_exclusively_for_value uid r p' v trace.
Proof using.
  move => trace r p v H_cert p' H_p_lt.
  move => uid g1 g2 n H_advance.
Admitted.

Lemma honest_in_from_after_and_send: forall r p s uid trace,
      honest_after_step (r,p,s) uid trace ->
  forall g0 (H_path : path gtransition g0 trace),
  forall ix g1 g2,
    step_in_path_at g1 g2 ix trace ->
  forall mt v,
    user_sent uid (mt,v,r,p,uid) g1 g2 ->
  step_le (msg_step (mt,v,r,p,uid)) (r,p,s) ->
    honest_in_period r p uid trace.
Proof using.
  move => r p s uid trace H_honest g0 H_path ix g1 g2 H_step mt v H_sent H_msg_step.
  move/honest_at_from_after in H_honest.
  specialize (H_honest _ H_path).

  have H_g2 := step_in_path_onth_post H_step.
  exists ix.+1. rewrite H_g2.
  specialize (H_honest _ _ H_g2).

  have key := user_sent_in_post H_sent.
  have H_ustate := in_fnd key.
  set ustate := g2.(users)[` key] in H_ustate.
  clearbody ustate.
  rewrite H_ustate.
  specialize (H_honest _ H_ustate).

  lapply H_honest.

  (* is this true as stated? *)
Admitted.

Lemma onth_last_take: forall T (s:seq T) n x,
    onth s n = Some x ->
    forall x0,
    last x0 (take n.+1 s) = x.
Proof using.
  clear.
  move => T s n x H_nth x0.
  have H_size := onth_size H_nth.
  move: H_nth.
  unfold onth, ohead.

  have ?: n < n.+1 by rewrite ltnS.
  rewrite -nth_last size_takel //= nth_take // (drop_nth x0) //.
  by case.
Qed.

Definition reached_round uid r p: pred GState :=
  fun g =>
    match g.(users).[? uid] with
    | None => false
    | Some u => (r < u.(round)) || (r == u.(round)) && (p <= u.(period))
    end.

Lemma honest_in_period_entered g0 trace (H_path : path gtransition g0 trace):
  forall r p uid, honest_in_period r p uid trace ->
  forall u0, g0.(users).[? uid] = Some u0 ->
  step_lt (step_of_ustate u0) (r,p,0) ->
  exists n g1 g2, period_advance_at n trace uid r p g1 g2.
Proof using.
  clear -H_path.
  move => r p uid [] ix_h.
  destruct (onth trace ix_h) as [g_h|] eqn:H_ix_h;[|done].
  destruct (g_h.(users).[? uid]) as [u_h|] eqn:H_u_h;[|done].
  move => [H_honest [H_r H_p]].
  move => u0 H_u0 H_lt_u0.

  apply (path_prefix ix_h.+1) in H_path.
  pose proof (path_steps H_path).
  specialize (H (reached_round uid r p)).
  rewrite (onth_last_take H_ix_h) in H.
  lapply H;[move => {H}H|];[lapply H;[move => {H}H|]|];first last.
  {
    unfold reached_round.
    rewrite H_u0. revert H_lt_u0. clear;destruct u0;simpl;clear.
    move => H_step_lt.
    rewrite ltn0 falseE in H_step_lt.

    destruct H_step_lt as [H|[-> H]];
      [by rewrite (gtn_eqF H) negb_or ltnNge (ltnW H)
      |rewrite ltnn eq_refl].
    destruct H as [H|[_ []]].
    by rewrite -ltnNge.
  }
  {
    unfold reached_round.
    rewrite H_u_h.
    rewrite H_r H_p.
    apply/orP. right.
    rewrite eq_refl leqnn.
    done.
  }

  (* Needs some stuff about lists and lengths now *)
(*
  destruct H as [n H].
  destruct n. admit. (* zero index into (g0::trace) not yet supported *)
  simpl in H.
  exists n.

  destruct (drop n (take ix_h.+1 trace)) as [|g1 l] eqn:H_l;[by destruct (notF H)|exists g1].
  destruct l as [|g2 l];[by destruct (notF H)|exists g2].
  unfold period_advance_at.
    split. unfold step_in_path_at.
  rewrite -[trace](cat_take_drop ix_h.+1) drop_cat.

  replace (n < size (take ix_h.+1 trace)) with true.
  rewrite H_l. split;reflexivity.

  apply (f_equal size) in H_l;change (size [:: g1, g2 & l]) with (size l).+2 in H_l.
  rewrite size_drop in H_l.
  symmetry. rewrite -subn_gt0 H_l. reflexivity.

  move/andP: H => [H_g1 H_g2].
  unfold reached_round in H_g2.
  destruct (uid \in g2.(users)) eqn:key2 at 0.
  rewrite in_fnd in H_g2.
  *)
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

  destruct (nosimpl H_cert2) as (q2 & H_q2 & H_size2 & H_cert2_voted).
  destruct (quorum_c_has_honest trace H_q2 H_size2)
     as (honest_voter & H_honest_q & H_honest_in).

  (* honest_at_step r p2 3 honest_voter trace *)
  specialize (H_cert2_voted honest_voter H_honest_q).
  destruct (nosimpl H_cert2_voted) as (ix & ga1 & ga2 & [H_step2 H_send_vote2]).
  assert (honest_in_period r p2 honest_voter trace)
   by (eapply honest_in_from_after_and_send;[eassumption..|apply step_le_refl]).

  pose proof (certificate_is_start_of_later_periods H_cert1 Hlt) as H_entry.
  specialize (H_entry honest_voter).

  pose proof (@excl_enter_limits_cert_vote _ _ H_path r p2 v1 Hpos) as H_recert.
  pose proof (honest_in_period_entered H_path H).

  assert (honest_voter \in g0.(users)) by admit.
  (*
  {
    assert (exists ix, user_honest_at ix trace honest_voter). {
    destruct H_honest_in as [x H_honest_in]. exists x.
    unfold user_honest_at.
    destruct (onth trace x) eqn:H_x;[|done].
    apply (onth_at_step H_x).
    unfold predC, is_user_corrupt_gstate, is_user_corrupt. simpl.
    revert H_honest_in.
    destruct (g.(users).[?honest_voter]) eqn:H_in;[|done].
    rewrite H_in.
    by move => [] /negP.
    }
    assert (~~ is_user_corrupt_gstate honest_voter g0).
    admit.
    unfold is_user_corrupt_gstate, is_user_corrupt in H2.
    destruct (g0.(users).[? honest_voter]) eqn:H_lookup.
  *)

  specialize (H0 _ (in_fnd H1)).

  lapply H0.
  move => [n [g1 [g2 H_advance]]].
  specialize (H_entry g1 g2 n H_advance).

  symmetry.
  eapply H_recert;try eassumption.

  apply H_entry.
  revert H H_advance. admit.

  revert H_start.
  unfold state_before_round, honest_users_before_round.
  case => [H_users_g0 _].
  specialize (H_users_g0 _ H1).
  lapply H_users_g0.

  move:(g0.(users)[` H1]) => u.
  unfold user_before_round;destruct u;simpl;clear -Hlt.
  move => [] H_fields _. clear -H_fields Hlt.
  destruct H_fields;[left;assumption|right].
  destruct H as [Hr H];split;[assumption|clear Hr].
  left. destruct H as [_ [-> _]].
  apply (@leq_ltn_trans p1). (* Need to exclude period p1 being 0 *) admit.
  assumption.

  suff: user_honest honest_voter g0 by rewrite /user_honest in_fnd.
  clear -H_honest_in H_path.

  move: H_honest_in => [ix H_honest].
  destruct (onth trace ix) eqn:H_onth;[|done].
  suff: user_honest honest_voter g
    by apply honest_monotone;exists (take ix.+1 trace);[by apply path_prefix|by symmetry;apply onth_last_take].

  unfold user_honest.
  destruct g.(users).[?honest_voter];[|done].
  by move: H_honest => [] /negP.
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


(** LIVENESS **)

(* A user has (re-)proposed a value/block for a given round/period along a
   given path *)
Definition proposed_in_path_at ix path uid r p v b : Prop :=
  exists g1 g2, step_in_path_at g1 g2 ix path /\
    (user_sent uid (Proposal, val v, r, p, uid) g1 g2 /\
     user_sent uid (Block, val b, r, p, uid) g1 g2 \/
     user_sent uid (Reproposal, repr_val v uid p, r, p, uid) g1 g2).

(* A block proposer (potential leader) for a given round/period along a path*)
Definition block_proposer_in_path_at ix path uid r p v b : Prop :=
  uid \in committee r p 1 /\
  valid_block_and_hash b v /\
  proposed_in_path_at ix path uid r p v b.

(* The block proposer (the leader) for a given round/period along a path*)
Definition leader_in_path_at ix path uid r p v b : Prop :=
  block_proposer_in_path_at ix path uid r p v b /\
  forall id, id \in committee r p 1 /\ id <> uid ->
    (credential uid r p 1 < credential id r p 1)%O.

(* a trace is partition-free if it's either empty or it's a valid trace that
   starts at an unparitioned state and does not involve a partitioning
   transition -- Note: not compatible with is_trace above *)
Definition partition_free trace : Prop :=
  if ohead trace is Some g0 then
    is_unpartitioned g0 /\
    path gtransition g0 (drop 1 trace) /\
    forall n, ~ step_at trace n lbl_enter_partition
  else True.

Lemma partition_state : forall g,
  is_unpartitioned g ->
  is_partitioned (make_partitioned g).
Proof.
  intros g unp_H.
  unfold is_unpartitioned,is_partitioned in unp_H.
  unfold is_partitioned, make_partitioned, flip_partition_flag.
  simpl. assumption.
Qed.

(* is_partitioned as a proposition *)
Lemma is_partitionedP : forall g : GState,
  reflect
    (g.(network_partition) = true)
    (is_partitioned g).
Admitted.

Lemma partition_free_step : forall g0 g1,
  is_unpartitioned g0 -> g0 ~~> g1 ->
  ~ related_by lbl_enter_partition g0 g1 ->
  is_unpartitioned g1.
Proof.
intros g0 g1 g0unp_H g0g1step_H notpstep_H.
unfold related_by in notpstep_H. intuition.
unfold make_partitioned in H2. unfold flip_partition_flag in H2. simpl in * |- *.
(* almost all cases are straightforward *)
destruct g0g1step_H ; auto.
(* except recover_from_partitioned, which is handled separately *)
  unfold is_unpartitioned in g0unp_H. rewrite H1 in g0unp_H. auto.
Qed.

Lemma partition_free_prefix : forall n trace,
  partition_free trace ->
  partition_free (take n trace).
Proof.
intros n trace prfree_H.
generalize dependent n.
induction n.
  rewrite take0. unfold partition_free. simpl. exact I.
  unfold partition_free in * |- *. destruct trace. auto.
simpl in * |- *. decompose record prfree_H. rewrite drop0 in H1.
split; auto. rewrite drop0. split; auto.
Admitted.

Lemma partition_free_suffix : forall n trace,
  partition_free trace ->
  partition_free (drop n trace).
Proof.
intros n trace prfree_H.
generalize dependent n.
induction n. rewrite drop0. assumption.
unfold partition_free in * |- *.
Admitted.

(* Whether the effect of a message is recored in the user state *)
Definition message_recorded ustate msg : Prop :=
  match msg with
  | (Block, val b, r,_,_) =>
       b \in ustate.(blocks) r
  | (Proposal, val v, r, p, uid) =>
       exists c, (uid, c, v, true) \in ustate.(proposals) r p
  | (Reproposal, repr_val v uid' p', r, p, uid) =>
       exists c, (uid, c, v, false) \in ustate.(proposals) r p
  | (Softvote, val v, r, p, uid) =>
       (uid, v) \in ustate.(softvotes) r p
  | (Certvote, val v, r, p, uid) =>
       (uid, v) \in ustate.(certvotes) r p
  | (Nextvote_Open, step_val s, r, p, uid) =>
       uid \in ustate.(nextvotes_open) r p s
  | (Nextvote_Val, next_val v s, r, p, uid) =>
       (uid, v) \in ustate.(nextvotes_val) r p s
  | _ => True
  end.

(* The effect of the message is recorded in the state of the target user on or
   before the message's deadline *)
Definition msg_timely_delivered msg deadline gstate target : Prop :=
  Rle gstate.(now) deadline /\
  exists ustate, gstate.(users).[? target] = Some ustate /\
  message_recorded ustate msg.

(* If a message is sent along a partition-free trace, and the trace is long enough,
   then the message is received by all honest users in a timely fashion
 *)
(* Note: this probably needs revision *)
Lemma sent_msg_timely_received : forall sender msg g0 g1 trace,
  let deadline := msg_deadline msg g0.(now) in
    user_sent sender msg g0 g1 ->
    path gtransition g0 (g1 :: trace) ->
    partition_free (g1 :: trace) ->
    Rle deadline (last g0 (g1 :: trace)).(now) ->
    exists ix g, ohead (drop ix (g1 :: trace)) = Some g
      /\ (forall target, target \in honest_users g.(users) ->
            msg_timely_delivered msg deadline g target).
Admitted.


(* If the block proposer of period r.1 is honest, then a certificate for round r
is produced at period r.1 *)
(* Need the assumption of no partition?? *)
Lemma prop_a : forall g0 g1 trace uid r v b,
  path gtransition g0 (g1 :: trace) ->
  partition_free (g0 :: g1 :: trace) ->
  leader_in_path_at 0 (g0 :: g1 :: trace) uid r 1 v b ->
  user_honest_at 0 (g0 :: g1 :: trace) uid ->
  certified_in_period trace r 1 v.
Proof.
intros g0 g1 trace sender r v b tr_H pfree_tr_H leader_H honest_H.
destruct leader_H as [proposer_H crommitte_H].
destruct proposer_H as [poleader_H [vb_H proposed_H]].
destruct proposed_H as [g' prop_sent_H].
destruct prop_sent_H as [g'' [prop_step_H prop_sent_H]]. destruct prop_step_H. subst.
  (* Need to identify: - the step and state at which the message is received
                      - the user who is receiving the message *)
destruct prop_sent_H as [propsent_H | repropsent_H].
  destruct propsent_H as [propsent_H blocksent_H].
  pose proof (@sent_msg_timely_received sender (Proposal, val v, r, 1, sender) g' g'' trace). simpl in * |- *.
Admitted.


(* If some period r.p, p >= 2 is reached with unique starting value bot and the
   leader is honest, then the leader’s proposal is certified. *)
(* TODO: all users need starting value bot or just leader? *)
Lemma prop_c : forall ix path uid r p v b,
  p >= 2 ->
  all (fun u => user_stv_val_at ix path u p None) (domf (users_at ix path)) ->
  leader_in_path_at ix path uid r 1 v b ->
  user_honest_at ix path uid ->
  certified_in_period path r p v.
Admitted.

(* softvote quorum of all honest users implies certvote quorum *)
Lemma honest_softvote_quorum_implies_certvote : forall (softvote_quorum : {fset UserId}) ix path r p v,
  (forall voter : UserId, voter \in softvote_quorum ->
                                    voter \in domf (honest_users (users_at ix path))) ->
  softvote_quorum `<=` committee r p 3 ->
  tau_c <= #|softvote_quorum| ->
  (forall voter : UserId, voter \in softvote_quorum
                                    -> softvoted_in_path_at ix path voter r p v) ->
  (forall voter : UserId, voter \in softvote_quorum
                                    -> certvoted_in_path path voter r p v).
Proof.
Admitted.

Lemma all_def : forall (s : seq UserId) p x,
  all p s -> x \in s -> p x.
Proof.
Admitted.

(* Honest user softvotes starting value *)
Lemma stv_not_bot_softvote : forall ix path r p v uid,
  uid \in domf (honest_users (users_at ix path)) ->
  user_stv_val_at ix path uid p (Some v) ->
  softvoted_in_path_at ix path uid r p v.
Admitted.

(* If some period r.p with p >= 2 is reached, and all honest users have starting
   value H(B), then a certificate for H(B) that period is produced by the honest
   users. *)
(* TODO: need to say quorum for certificate is only *honest* users? *)
Lemma prop_e : forall ix path r p v b,
  p >= 2 ->
  all (fun u => user_stv_val_at ix path u p (Some v))
      (domf (honest_users (users_at ix path))) ->
  valid_block_and_hash b v ->
  certified_in_period path r p v.
Proof.
  intros.
  exists (domf (honest_users (users_at ix path))).
  (* quorum subset of committee at step 3 *)
  assert (domf (honest_users (users_at ix path)) `<=` committee r p 3) by admit.
  (* at least t_H honest users *)
  assert (tau_c <= #|domf (honest_users (users_at ix path))|) by admit.
  repeat split; try assumption.
  eapply honest_softvote_quorum_implies_certvote with ix; try assumption.
  trivial.
  intros. apply stv_not_bot_softvote.
  assumption.
  eapply all_def in H0; try eassumption.
Admitted.

(* If any honest user is in period r.p with starting value bottom, then within
time (2*lambda+Lambda), every honest user in period r.p will either certify a
value (i.e., will get a certificate) or move to the next period *)
Lemma prop_f : forall r p g0 g1 g2 path_seq uid,
    path gtransition g0 path_seq ->
    g2 = last g0 path_seq ->
    g1 = last g0 (drop 1 path_seq) ->
    user_honest uid g1 ->
    user_stv_val uid g1 p None ->
    (exists v, certvoted_in_path path_seq uid r p v
               \/ period_advance_at 1 path_seq uid r p g1 g2) .
Admitted.

End AlgoModel.
