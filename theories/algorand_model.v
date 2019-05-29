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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Generic lemmas *)
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

Inductive Unused : Prop := .
Ltac unused := by apply Unused_rect.
Ltac admit_unused := by apply Unused_rect.

(* Algorand Proofs *)
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

Definition MType_eq (a b:MType) : bool :=
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
Lemma MType_eq_good: Equality.axiom MType_eq.
Proof using.
  move => a b;apply Bool.iff_reflect;split.
    by move <-;destruct a.
    by move/(ifT (a=b) True) => <-;destruct a, b.
Qed.

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

Canonical mtype_eqType     := EqType     MType (Equality.Mixin MType_eq_good).
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
Definition msg_sender (m:Msg): UserId := m.2.
Definition msg_round (m:Msg): nat := m.1.1.2.

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

Hypothesis credentials_valid_period:
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

Definition step_leb (step1 step2: nat * nat * nat) : bool :=
  let: (r1,p1,s1) := step1 in
  let: (r2,p2,s2) := step2 in
  (r1 < r2) || (r1 == r2) && ((p1 < p2) || (p1 == p2) && (s1 <= s2)).

Lemma step_leP: forall s1 s2, reflect (step_le s1 s2) (step_leb s1 s2).
Proof using.
  clear.
  move => [[r1 p1] s1] [[r2 p2] s2].
  case H:(step_leb _ _);constructor;[|move/negP in H];
    by rewrite /step_le !(reflect_eq eqP, reflect_eq andP, reflect_eq orP).
Qed.

Definition step_lt (step1 step2: nat * nat * nat) :=
  let: (r1,p1,s1) := step1 in
  let: (r2,p2,s2) := step2 in
  r1 < r2 \/ r1 = r2 /\ (p1 < p2 \/ p1 = p2 /\ s1 < s2).

Definition step_ltb (step1 step2: nat * nat * nat) : bool :=
  let: (r1,p1,s1) := step1 in
  let: (r2,p2,s2) := step2 in
  (r1 < r2) || (r1 == r2) && ((p1 < p2) || (p1 == p2) && (s1 < s2)).

Lemma step_ltP: forall s1 s2, reflect (step_lt s1 s2) (step_ltb s1 s2).
Proof using.
  clear.
  move => [[r1 p1] s1] [[r2 p2] s2].
  case H:(step_ltb _ _);constructor;[|move/negP in H];
    by rewrite /step_lt !(reflect_eq eqP, reflect_eq andP, reflect_eq orP).
Qed.

Lemma step_ltW a b:
  step_lt a b -> step_le a b.
Proof using.
  clear.
  destruct a as [[? ?] ?],b as [[? ?]?].
  unfold step_lt,step_le;intuition.
Qed.

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
          - Updated to accommodate the 27March change
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
          - Updated to accommodate the 27March change
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
          - Updated to accommodate the 27March change
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

(* Gather all the unfoldings we might want for working with transitions into
   a hint database for use with autounfold *)
Create HintDb utransition_unfold discriminated.
Hint Unfold
     (* UTransitionInternal *)
     propose_result      propose_ok repropose_ok no_propose_ok
     softvote_result     softvote_new_ok softvote_repr_ok no_softvote_ok
     certvote_result     certvote_ok no_certvote_ok
     nextvote_result     nextvote_val_ok nextvote_open_ok nextvote_stv_ok no_nextvote_ok
     certvote_timeout_ok
     (* UTransitionMsg *)
     set_softvotes       certvote_ok         certvote_result
     set_nextvotes_open  adv_period_open_ok  adv_period_open_result
     set_nextvotes_val   adv_period_val_ok   adv_period_val_result
     set_certvotes       certify_ok          certify_result
     vote_msg deliver_nonvote_msg_result : utransition_unfold.

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

Lemma tick_users_notin : forall increment pre uid (h : uid \notin domf pre.(users)),
  (tick_users increment pre).[? uid] = None.
Proof using.
  move => increment pre uid h.
  apply not_fnd.
  change (uid \notin domf (tick_users increment pre)); by rewrite -updf_domf.
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

Definition merge_msgs_deadline (now : R) (msgs : seq Msg) (v : {mset R * Msg}) : {mset R * Msg} :=
  seq_mset [seq (msg_deadline msg now,msg) | msg <- msgs] `+` v.

Lemma in_merge_msgs : forall d (msg:Msg) now msgs mailbox,
    (d,msg) \in merge_msgs_deadline now msgs mailbox ->
    msg \in msgs \/ (d,msg) \in mailbox.
Proof.
  move=> d msg now msgs mb.
  move=> /msetDP [|];[|right;done].
  by rewrite (perm_eq_mem (perm_eq_seq_mset _)) => /mapP [x H_x [_ ->]];left.
Qed.

Definition send_broadcasts_def (now : R) (targets : {fset UserId}) (prev_msgs : MsgPool) (msgs : seq Msg) : MsgPool :=
  updf prev_msgs targets (fun _ => merge_msgs_deadline now msgs).
Fact send_broadcasts_key: unit. Proof using. exact tt. Qed.
Definition send_broadcasts
  := locked_with send_broadcasts_key send_broadcasts_def.
Canonical send_broadcasts_unlockable := [unlockable fun send_broadcasts].

Lemma send_broadcastsE now targets prev_msgs msgs:
  send_broadcasts now targets prev_msgs msgs = updf prev_msgs targets (fun _ => merge_msgs_deadline now msgs).
Proof using.
  by rewrite unlock.
Qed.

Lemma send_broadcasts_in : forall (msgpool : MsgPool) now uid msgs targets
                                 (h : uid \in msgpool) (h' : uid \in targets),
  (send_broadcasts now targets msgpool msgs).[? uid] = Some (merge_msgs_deadline now msgs msgpool.[h]).
Proof using.
  by move => *;rewrite send_broadcastsE updf_update.
Qed.

Lemma send_broadcast_notin : forall (msgpool : MsgPool) now uid msgs targets
                                    (h : uid \notin domf msgpool),
  (send_broadcasts now targets msgpool msgs).[? uid] = None.
Proof using.
  move => *;apply not_fnd.
  change (?k \notin ?f) with (k \notin domf f).
  by rewrite send_broadcastsE -updf_domf.
Qed.

Lemma send_broadcast_notin_targets : forall (msgpool : MsgPool) now uid msgs targets
                                            (h : uid \in msgpool) (h' : uid \notin targets),
  (send_broadcasts now targets msgpool msgs).[? uid] = msgpool.[? uid].
Proof using.
  move => msgpool now uid msg targets h h'.
  by rewrite send_broadcastsE updf_update' // in_fnd.
Qed.

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

Lemma onth_nth T (s:seq T) ix x:
  onth s ix = Some x -> (forall x0, nth x0 s ix = x).
Proof using.
  unfold onth.
  unfold ohead.
  move => H_drop x0.
  rewrite -[ix]addn0 -nth_drop.
  destruct (drop ix s);simpl;congruence.
Qed.

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

Lemma all_onth T P s: @all T P s -> forall ix x, onth s ix = Some x -> P x.
Proof.
  move/all_nthP => H ix x H_g. rewrite -(onth_nth H_g x).
  apply H, (onth_size H_g).
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

Lemma in_seq_mset (T : choiceType) (x : T) (s : seq T):
  (x \in seq_mset s) = (x \in s).
Proof using.
  apply perm_eq_mem, perm_eq_seq_mset.
Qed.

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

Definition is_trace (g0 : GState) (path : seq GState) : Prop :=
  nosimpl match path with
          | [::] => False
          | [:: g' & rest] => g0 = g' /\ path.path gtransition g0 rest
          end.

Definition greachable (g0 g : GState) : Prop := exists2 p, is_trace g0 p & g = last g0 p.

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

(* classic definition of reachable global state *)

Definition GReachable (g0 g : GState) : Prop := clos_refl_trans_1n _ GTransition g0 g.

(* definitions are equivalent in our setting *)

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

Inductive GLabel : Type :=
| lbl_tick :  posreal -> GLabel
| lbl_deliver : UserId -> R -> Msg -> seq Msg -> GLabel
| lbl_step_internal : UserId -> seq Msg -> GLabel
| lbl_exit_partition : GLabel
| lbl_enter_partition : GLabel
| lbl_corrupt_user : UserId -> GLabel
| lbl_replay_msg : UserId -> GLabel
| lbl_forge_msg : UserId -> nat -> nat -> MType -> ExValue -> GLabel.

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

Definition user_sent_at ix path uid msg :=
  exists g1 g2, step_in_path_at g1 g2 ix path
                /\ user_sent uid msg g1 g2.

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
    exists (lbl_forge_msg sender r p mtype mval);finish_case.
  + (* reverse - find transition from label *)
    destruct 1 as [[] Hrel];simpl in Hrel;decompose record Hrel;clear Hrel;subst g2;
      [eapply step_tick
      |eapply step_deliver_msg
      |eapply step_internal
      |eapply step_exit_partition
      |eapply step_enter_partition
      |eapply step_corrupt_user
      |eapply step_replay_msg
      |eapply step_forge_msg];eassumption.
    (* econstructor takes a very long time being confused between
       different steps that build the result with send_broadcasts *)
Qed.

Lemma internal_not_noop :
  forall s pre post l,
    s # pre ~> (post, l) ->
    pre <> post.
Proof.
  move => s pre post l Hst;inversion Hst;subst;
  autounfold with utransition_unfold in H2;decompose record H2;clear H2;
    match goal with [H : valid_rps _ _ _ _ |- _] =>
      destruct H as [_ [_ H_s]];contradict H_s;rewrite H_s;simpl;clear
    end;try discriminate; by rewrite addn1 => /esym /n_Sn.
Qed.

Lemma finsupp_mset_uniq (T:choiceType) (A:{mset T}):
  uniq (finsupp A).
Proof using.
  by rewrite -(perm_eq_uniq (perm_undup_mset A));apply undup_uniq.
Qed.

Lemma msubset_finsupp (T:choiceType) (A B: {mset T}):
  (A `<=` B)%mset ->
  perm_eq (finsupp A) [seq i <- finsupp B | i \in A].
Proof using.
  move=>H_sub.
  apply uniq_perm_eq.
    by apply finsupp_mset_uniq.
    by apply filter_uniq;apply finsupp_mset_uniq.
  move=>x.
  rewrite mem_filter.
  rewrite !msuppE.
  rewrite andb_idr //.
  move:H_sub => /msubset_subset. apply.
Qed.

Lemma msubset_size_sum (T:choiceType) (A B: {mset T}):
  (A `<=` B)%mset ->
  \sum_(i <- finsupp B) A i = size A.
Proof using.
  move=>H_sub.
  rewrite (bigID (fun i => i \in A)) /= -big_filter.
  rewrite -(eq_big_perm _ (msubset_finsupp H_sub)) -size_mset big1.
    by rewrite addn0.
    by move=>i /mset_eq0P.
Qed.


Lemma mset_add_size (T:choiceType) (A B : {mset T}):
  size (A `+` B) = (size A + size B)%nat.
Proof using.
  rewrite size_mset (eq_bigr (fun a => A a + B a)%nat);[|by move => ? _;rewrite msetE2].
  rewrite big_split !msubset_size_sum //.
  rewrite -{1}[B]mset0D. apply msetSD, msub0set.
  rewrite -{1}[A]msetD0. apply msetDS, msub0set.
Qed.

Lemma msetn_size (T:choiceType) n (x:T):
  size (msetn n x) = n.
Proof using.
  rewrite size_mset finsupp_msetn.
  case:n=>[|n] /=.
  exact: big_nil.
  by rewrite big_seq_fset1 msetnxx.
Qed.

Lemma msubset_size (T:choiceType) (A B : {mset T}):
  (A `<=` B)%mset -> size A <= size B.
Proof using.
  move=>H_sub.
  by rewrite -(msetBDK H_sub) mset_add_size leq_addl.
Qed.

(* used in transition_label_unique *)
Lemma deliver_analysis1:
  forall g uid upost r m l
         (key_mbox : uid \in g.(msg_in_transit)),
    (r, m) \in g.(msg_in_transit).[key_mbox] ->
    let g2 := delivery_result g uid key_mbox (r, m) upost l in
    (forall uid2,
      ( size (odflt mset0 (g2.(msg_in_transit).[?uid2]))
      < size (odflt mset0 (g.(msg_in_transit).[?uid2]))) <->
      uid = uid2)
    /\ [mset (r,m)] =( odflt mset0 (g.(msg_in_transit).[?uid])
       `\` odflt mset0 (g2.(msg_in_transit).[?uid]))%mset.
Proof using.
  clear.
  move=> g uid upost r m l key_mbox H_pending g2.

  set mb1: {mset R*Msg} := odflt mset0 (g.(msg_in_transit).[?uid]).
  set mb2: {mset R*Msg} := odflt mset0 (g2.(msg_in_transit).[?uid]).
  assert (H_singleton: mb1 = (r,m) +` mb2).
  {
    subst mb1 mb2.
    rewrite /g2 /delivery_result send_broadcastsE.
  rewrite updf_update'.
  simpl. by rewrite in_fset1U; apply/orP; left.
  intro H_uid.
  rewrite in_fnd.
  repeat match goal with
           [|- context C[odflt mset0 (Some ?x)]] =>
           assert (H :odflt mset0 (Some x) = x) by done; rewrite H; clear H
         end.
  rewrite setfNK; rewrite eq_refl.
  by rewrite msetBDKC;[|rewrite msub1set].
  by rewrite fsetD11.
  }
  split;[|by move:H_singleton => /(f_equal (msetB^~mb2)) ->;rewrite msetDC msetDKB].

  move => uid2.
  split; last first.
  intros <-.
  fold mb1 mb2.
  by rewrite H_singleton mset_add_size msetn_size leqnn.

  intro H_size.
  case H_neq:(uid2 == uid);[by move/eqP: H_neq|exfalso].

  subst g2.
  unfold delivery_result in *.
  cbn [global_state.msg_in_transit
         set_GState_users
         set_GState_msg_history
         set_GState_msg_in_transit] in *.

  remember (global_state.msg_in_transit UserId UState [choiceType of Msg] g) as mailboxes.
  remember (mailboxes.[uid <- (mailboxes.[key_mbox] `\ (r, m))%mset]) as mailboxes'.
  case:mailboxes'.[?uid2]/fndP => H_mb.
  2: {
    assert (H_mb' := H_mb).
    move/not_fnd in H_mb'.
    subst mailboxes'. rewrite fnd_set in H_mb'.
    rewrite H_neq in H_mb'.
    rewrite H_mb' in H_size.
    rewrite size_mset0 in H_size.
    inversion H_size.
  }

  assert (H_uid2 : uid2 \in domf mailboxes).
  rewrite -fndSome.
  assert (mailboxes'.[? uid2] = Some mailboxes'.[H_mb]). by rewrite in_fnd.
  subst mailboxes'.
  rewrite fnd_set in H.
  rewrite H_neq in H. rewrite H.
  done.

  rewrite send_broadcastsE in H_size.
  destruct (uid2 \in domf (honest_users (g.(users)))) eqn:H_honest; last first.
  {
    rewrite updf_update' in H_size.
    rewrite in_fnd in H_size.
    simpl in H_size.
    subst.
    rewrite setfNK in H_size.
    rewrite H_neq in H_size.
    rewrite ltnn in H_size; discriminate.

    rewrite in_fsetD1.
    apply/andP. move => [_ H_honest'].
      by rewrite H_honest in H_honest'.
  }

  {
    rewrite updf_update in H_size.
    rewrite in_fnd in H_size.
    simpl in H_size.
    subst.
    rewrite setfNK in H_size.
    rewrite H_neq in H_size.
    simpl in H_size.
    move: H_size. rewrite ltnNge.
    apply/negP/negPn.
    apply/msubset_size.
    move: (g.(msg_in_transit)[`H_uid2]) => mb.
    rewrite -{1}[mb]mset0D.
    by apply msetSD, msub0set.

    rewrite in_fsetD1.
    apply/andP. split.
      by move/eqP in H_neq; move/eqP: H_neq.
      by apply/negP; move/negP in H_honest.
  }
Qed.

Lemma utransition_msg_result_analysis uid upre m upost l l'
      (H_step: uid # upre; m ~> (upost, l))
      (H_step': uid # upre; m ~> (upost, l')):
  l = l'.
Proof.
  clear -H_step H_step'.
  remember (upost,l) as ustate_out.
  destruct H_step eqn:H_trans; case: Hequstate_out;
    intros <- <-; inversion H_step'; subst; try (by []); exfalso.
  subst pre'; subst pre'0; clear -H2 H6.
  unfold set_softvotes, certvote_ok, valid_rps in H2; simpl in H2.
    by rewrite <- H6 in H2; intuition.
  subst pre'; subst pre'0; clear -c H6.
  unfold set_softvotes, certvote_ok, valid_rps in c; simpl in c.
    by rewrite H6 in c; intuition.
  unfold vote_msg in H3; simpl in H3.
    by intuition.
  subst pre'; subst pre'0.
  unfold deliver_nonvote_msg_result, certvote_result in H.
  destruct pre; simpl in *.
  case: H; intros <-; intro; clear -H3.
  unfold certvote_ok, set_softvotes, valid_rps in H3; simpl in H3.
    by intuition.
Qed.

(* used in transition_label_unique *)
Lemma deliver_deliver_lbl_unique :
  forall g uid uid' upost upost' r r' m m' l l'
    (key_state : uid \in g.(users)) (key_mbox : uid \in g.(msg_in_transit))
    (key_state' : uid' \in g.(users)) (key_mbox' : uid' \in g.(msg_in_transit)),
    ~ g.(users).[key_state].(corrupt) ->
    (r, m) \in g.(msg_in_transit).[key_mbox] ->
    uid # g.(users).[key_state] ; m ~> (upost, l) ->
    ~ g.(users).[key_state'].(corrupt) ->
    (r', m') \in g.(msg_in_transit).[key_mbox'] ->
    uid' # g.(users).[key_state'] ; m' ~> (upost', l') ->
    delivery_result g uid key_mbox (r, m) upost l = delivery_result g uid' key_mbox' (r', m') upost' l' ->
    uid = uid' /\ r = r' /\ m = m' /\ l = l'.
Proof using.
  clear.
  move => g uid uid' upost upost' r r' m m' l l' key_state key_mbox key_state' key_mbox'
          H_honest H_pending H_step H_honest' H_pending' H_step' H_results.
  have Fact1 :=
    deliver_analysis1 upost l H_pending.
  have Fact1' :=
    deliver_analysis1 upost' l' H_pending'.
  have {Fact1 Fact1'}[H_uids H_pendings] : uid = uid' /\ [mset (r,m)] = [mset (r',m')].
  {
  move: H_results Fact1 Fact1' => <-.
  set g2 := delivery_result g uid key_mbox (r, m) upost l.
  cbv zeta. clearbody g2. clear.
  move => [H_uid H_pending] [H_uid' H_pending'].
  have H: uid = uid by reflexivity.
  rewrite <-H_uid, H_uid' in H;subst uid'.
  by split;[|rewrite H_pending -H_pending'].
  }
  subst uid'.
  have {H_pendings}[H_r H_m]: (r,m) = (r',m') by apply/mset1P;rewrite -H_pendings mset11.
  subst r' m'.
  repeat (split;[reflexivity|]).

  have H: upost = upost'
    by move: (f_equal (fun g => g.(users).[?uid]) H_results);
       rewrite !fnd_set eq_refl;clear;congruence.
  subst upost'.

  rewrite (bool_irrelevance key_state' key_state) in H_step'.
  move: (g.(users)[`key_state]) H_step H_step' => upre.
  clear.

  apply utransition_msg_result_analysis.
Qed.

(* used in transition_label_unique *)
Lemma deliver_internal_False :
  forall g uid uid' upost upost' r m l l'
    (key_state : uid \in g.(users)) (key_mbox : uid \in g.(msg_in_transit))
    (key_state' : uid' \in g.(users)),
    ~ g.(users).[key_state].(corrupt) ->
    (r, m) \in g.(msg_in_transit).[key_mbox] ->
    uid # g.(users).[key_state] ; m ~> (upost, l) ->
    ~ g.(users).[key_state'].(corrupt) ->
    uid' # g.(users).[key_state'] ~> (upost', l') ->
    delivery_result g uid key_mbox (r, m) upost l = step_result g uid' upost' l' ->
    False.
Proof using.
clear.
move => g uid uid' upost upost' r m l l' key_state key_mbox key_state'.
move => H_honest H_msg H_step H_honest' H_step'.
rewrite/delivery_result /= /step_result /=.
set us1 := _.[uid <- _].
set us2 := _.[uid' <- _].
set sb1 := send_broadcasts _ _ _ _.
set sb2 := send_broadcasts _ _ _ _.
move => Heq.
have Hus: us2 = us1 by move: Heq; move: (us1) (us2) => us3 us4; case.
have Hsb: sb1 = sb2 by case: Heq.
clear Heq.
case Hueq: (uid' == uid); last first.
  move/eqP: Hueq => Hueq.
  have Hus1c: us2.[? uid'] = us1.[? uid'] by rewrite Hus.
  move: Hus1c.
  rewrite 2!fnd_set.
  case: ifP; case: ifP.
  - by move/eqP.
  - move => _ _ Hpost.
    suff Hsuff: (global_state.users UserId UState [choiceType of Msg] g) [` key_state'] = upost'.
      move: H_step'.
      by move/internal_not_noop.
    apply sym_eq in Hpost.
    move: Hpost.
    rewrite in_fnd.
    by case.
  - by move /eqP.
  - by move => _ /eqP.
move/eqP: Hueq => Hueq.
move: Hsb.
rewrite /sb1 /sb2 Hueq.
move: H_msg.
clear.
set fs := [fset _ | _ in _].
set sb1 := send_broadcasts _ _ _ _.
set sb2 := send_broadcasts _ _ _ _.
move => H_msg Hsb.
have Hsb12: sb1.[? uid] = sb2.[? uid] by rewrite Hsb.
move: Hsb12.
rewrite send_broadcast_notin_targets; first rewrite send_broadcast_notin_targets //.
- rewrite fnd_set.
  case: ifP; last by move/eqP.
  move => _.
  rewrite in_fnd; case.
  move: H_msg.
  set ms := (global_state.msg_in_transit _ _ _ _ _).
  move => H_msg.
  move/msetP => Hms.
  move: (Hms (r, m)).
  rewrite msetB1E.
  case Hrm: ((r, m) == (r, m)); last by move/eqP: Hrm.
  rewrite /=.
  move: H_msg.
  rewrite -mset_neq0.
  move/eqP.
  case: (ms (r, m)) => //.
  move => n _.
  by ppsimpl; lia.
- rewrite in_fsetE /=.
  apply/negP.
  case/andP => Hf.
  case/negP: Hf.
  by rewrite in_fsetE.
- rewrite 2!in_fsetE.
  by apply/orP; left.
- rewrite in_fsetE /= in_fsetE.
  apply/negP.
  case/andP => Hf.
  by case/negP: Hf.
Qed.

Lemma msetD_seq_mset_perm_eq (T:choiceType) (A: {mset T}) (l l': seq T):
  A `+` seq_mset l = A `+` seq_mset l' -> perm_eq l l'.
Proof using.
  move/(f_equal (msetB^~A)); rewrite !msetDKB => H_seq_eq.
  apply/(perm_eq_trans _ (perm_eq_seq_mset l')).
  rewrite perm_eq_sym -H_seq_eq.
  apply perm_eq_seq_mset.
Qed.

Definition some_message_received (g1 g2:GState) : Prop :=
  exists uid, size (odflt mset0 g2.(msg_in_transit).[?uid])
            < size (odflt mset0 g1.(msg_in_transit).[?uid]).
Definition some_user_changed (g1 g2:GState) : Prop :=
  exists uid, g1.(users).[?uid] <> g2.(users).[?uid].

Lemma perm_eq_cons1P (T : eqType) (s : seq T) (a : T) : reflect (s = [:: a]) (perm_eq s [:: a]).
Proof.
case: s => [|x s]; first by rewrite /perm_eq /= ?eqxx; constructor.
case: s => [|y s].
  apply: (iffP idP).
    rewrite /perm_eq /= ?eqxx.
    move/andP => [Ht Ht'].
    move: Ht.
    case Hax: (a == x) => //.
    by move/eqP: Hax =>->.
  by move =>->; apply perm_eq_refl.
apply: (iffP idP) => //.
set s1 := [:: _ & _].
set s2 := [:: _].
move => Hpr.
by have Hs: size s1 = size s2 by apply perm_eq_size.
Qed.

Lemma utransition_result_perm_eq uid upre upost l l' :
  uid # upre ~> (upost, l) ->
  uid # upre ~> (upost, l') ->
  perm_eq l l' ->
  l = l'.
Proof.
move => Htr Htr' Hpq.
case Hs: (size l') => [|n].
  move: Hs Hpq.
  move/size0nil =>->.
  by move/perm_eq_nilP.
case Hn: n => [|n'].
  move: Hs.
  rewrite Hn.
  destruct l' => //=.
  case Hl': (size l') => //.
  move: Hpq.
  move/size0nil: Hl' =>->.
  by move/perm_eq_cons1P.
move: Hs.
rewrite Hn => Hl'.
have Heq: size l = size l' by apply perm_eq_size.
move: Heq.
rewrite Hl' => Hl.
have Hll': size l' >= 2 by rewrite Hl'.
have Hll: size l >= 2 by rewrite Hl.
clear n n' Hn Hl' Hl.
inversion Htr; inversion Htr'; subst; simpl in *; try by [].
move: Hpq.
set m1 := (Proposal, _, _, _, _).
set m2 := (Block, _, _, _, _).
set s1 :=  [:: _; _].
set s2 :=  [:: _; _].
move => Hpm.
have Hm1: m1 \in s2.
  rewrite -(perm_eq_mem Hpm) /= inE.
  by apply/orP; left.
have Hm2: m2 \in s2.
  rewrite -(perm_eq_mem Hpm) /= inE.
  apply/orP; right.
  by rewrite inE.
move: Hm1 Hm2.
rewrite inE.
move/orP; case; last by rewrite inE.
rewrite /s2.
move/eqP =><-.
rewrite inE.
move/orP; case; first by move/eqP.
rewrite inE.
by move/eqP =><-.
Qed.

(* Priority:MED This lemma is necessary for technical reasons to rule out
   the possibility that a step that counts as one user sending a message
   can't also count as a send from a different user or different message *)
Lemma transition_label_unique : forall lbl lbl2 g1 g2,
    related_by lbl g1 g2 ->
    related_by lbl2 g1 g2 ->
    match lbl with
    | lbl_deliver _ _ _ _ =>
      match lbl2 with
      | lbl_deliver _ _ _ _ => lbl2 = lbl
      | lbl_step_internal _ _=> lbl2 = lbl
      | _ => True
      end
    | lbl_step_internal _ _=>
      match lbl2 with
      | lbl_deliver _ _ _ _ => lbl2 = lbl
      | lbl_step_internal _ _=> lbl2 = lbl
      | _ => True
      end
    | _ => True
    end.
Proof using.
  move => lbl lbl2 g1 g2.
  destruct lbl eqn:H_lbl;try done.
  + (* deliver *)
    (* one user changed, with a message removed from their mailbox *)
    rewrite /=.
    move => [key_ustate [ustate_post [H_step H]]].
    move: H => [Hcorrupt [key_mailbox [Hmsg Hg2]]].
    rewrite Hg2 {Hg2} /related_by.
    destruct lbl2;try done.
    * (* deliver/deliver *)
      move => [key_ustate' [ustate_post' [H_step' [Hcorrupt' [key_mailbox' [Hmsg' Heq]]]]]].
      eapply deliver_deliver_lbl_unique in Heq; eauto.
      move: Heq => [Hs [Hr [Hm Hl]]].
      by rewrite Hs Hr Hm Hl.
    * (* deliver/internal *)
      move => [key_user [ustate_post' [Hcorrupt' [H_step' Heq]]]].
      by eapply deliver_internal_False in Heq; eauto.
  + (* step internal *)
    rewrite /=. (* one user changed, no message removed *)
    move => [key_ustate [ustate_post [H_corrupt [Hstep Hres]]]].
    rewrite Hres {Hres} /related_by.
    destruct lbl2;try done.
    * (* internal/deliver *)
      move => [key_ustate' [upost' [H_step' [H_corrupt' [key_mbox [Hmsg Heq]]]]]].
      apply sym_eq in Heq.
      by eapply deliver_internal_False in Heq; eauto.
    * (* internal/internal *)
      move => [key_user [ustate_post0 [Hcorrupt0 [Htr0 Heq]]]].
      case Hs: (s == s0); last first.
        move/eqP: Hs => Hs.
        move: Heq.
        rewrite /step_result /= /step_result /=.
        set us1 := _.[_ <- _].
        set us2 := _.[_ <- _].
        move => Heq.
        have Hus: us1 = us2 by move: Heq; move: (us1) (us2) => us3 us4; case.
        clear Heq.
        have Hus1c: us1.[? s0] = us2.[? s0] by rewrite Hus.
        move: Hus1c.
        rewrite 2!fnd_set.
        case: ifP => [|_]; first by move/eqP => Hs'; case: Hs.
        case: ifP => [_|]; last by move/eqP.
        rewrite in_fnd; case => Hg.
        by apply internal_not_noop in Htr0.
      move/eqP: Hs => Hs.
      move: Heq.
      rewrite -Hs.
      rewrite /step_result /= /step_result /=.
      set us1 := _.[_ <- _].
      set us2 := _.[_ <- _].
      set mh1 := (_ `+` seq_mset _)%mset.
      set mh2 := (_ `+` seq_mset _)%mset.
      move => Heq.
      have Hus: us1 = us2 by move: Heq; move: (us1) (us2) => us3 us4; case.
      have Hus1c: us1.[? s0] = us2.[? s0] by rewrite Hus.
      move: Hus1c.
      rewrite 2!fnd_set -Hs.
      case: ifP; last by move/eqP.
      move => _; case => Hustate.
      have Hmh: mh1 = mh2 by case: Heq.
      clear Heq Hcorrupt0.
      move: key_user Htr0.
      rewrite -Hs -Hustate => key_user.
      rewrite -(eq_getf key_ustate) => Hstep'.
      move: Hmh.
      rewrite /mh1 /mh2.
      move/msetD_seq_mset_perm_eq => Hprm.
      suff Hsuff: l = l0 by rewrite Hsuff.
      move: Hstep Hstep' Hprm.
      exact: utransition_result_perm_eq.
Qed.

Definition step_at path ix lbl :=
  exists g1 g2,
    step_in_path_at g1 g2 ix path
    /\ related_by lbl g1 g2.

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

Definition upred uid (P : pred UState) : pred GState :=
  fun g =>
    match g.(users).[? uid] with
    | Some u => P u
    | None => false
    end.

Definition honest_during_step (step:nat * nat * nat) uid(path : seq GState) :=
  all (upred uid (fun u => step_leb (step_of_ustate u) step ==> ~~u.(corrupt))) path.

Lemma honest_during_le s1 s2 uid trace:
  step_le s1 s2 ->
  honest_during_step s2 uid trace ->
  honest_during_step s1 uid trace.
Proof using.
  clear.
  move => H_le.
  unfold honest_during_step.
  apply sub_all => g.
  unfold upred. case: (g.(users).[?uid]) => [u|];[|done].
  move => /implyP H.
  apply /implyP => /step_leP H1.
  apply /H /step_leP /(step_le_trans H1 H_le).
Qed.

Definition committee (r p s:nat) : {fset UserId} :=
  [fset uid : UserId | `[<committee_cred (credential uid r p s)>] ].

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

Definition quorum_has_honest_statement tau : Prop :=
  forall trace r p s (quorum : {fset UserId}),
    quorum `<=` committee r p s ->
    #|` quorum | >= tau ->
   exists honest_voter, honest_voter \in quorum /\
     honest_during_step (r,p,s) honest_voter trace.

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

Hypothesis quorums_s_honest_overlap : quorum_honest_overlap_statement tau_s.
Definition quorum_s_has_honest : quorum_has_honest_statement tau_s
  := quorum_has_honest_from_overlap_stmt quorums_s_honest_overlap.

Hypothesis quorums_c_honest_overlap : quorum_honest_overlap_statement tau_c.
Definition quorum_c_has_honest : quorum_has_honest_statement tau_c
  := quorum_has_honest_from_overlap_stmt quorums_c_honest_overlap.

Hypothesis quorums_b_honest_overlap : quorum_honest_overlap_statement tau_b.
Definition quorum_b_has_honest : quorum_has_honest_statement tau_b
  := quorum_has_honest_from_overlap_stmt quorums_b_honest_overlap.

Hypothesis quorums_v_honest_overlap : quorum_honest_overlap_statement tau_v.
Definition quorum_v_has_honest : quorum_has_honest_statement tau_v
  := quorum_has_honest_from_overlap_stmt quorums_v_honest_overlap.

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

Lemma honest_last_all uid g0 p (H_path : is_trace g0 p):
    user_honest uid (last g0 p) ->
    all (user_honest uid) (g0::p).
Proof using.
  move => H_honest.
  destruct p. inversion H_path.
  destruct H_path as [H_g0 H_path]; subst.
  revert H_honest.
  elim/last_ind: p H_path => [|s x IH] /=; first by move=> _ ->.
  rewrite rcons_path last_rcons all_rcons.
  move/andP => [Hpath Hstep] Hx.
  specialize (IH Hpath).
  rewrite Hx.
  apply IH. by apply/honest_backwards_gstep /asboolP: Hx.
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

Lemma path_prefix : forall T R p (x:T) n,
    path R x p -> path R x (take n p).
Proof using.
  induction p;[done|].
  move => /= x n /andP [Hr Hpath].
  destruct n. done.
  simpl;apply /andP;by auto.
Qed.

Lemma is_trace_prefix : forall trace g0 n,
    is_trace g0 trace -> n > 0 -> is_trace g0 (take n trace).
Proof.
  clear.
  induction trace;[done|].
  destruct n. done.
  simpl.
  unfold is_trace.
  move => [H_g0 H_path] _.
  split;[done|by apply path_prefix].
Qed.

(* Generic lemmas *)
Lemma path_drop'' T (R:rel T) x p (H:path R x p) n:
  match drop n p with
  | List.nil => true
  | List.cons x' p' => path R x' p'
  end.
Proof using.
  by elim: n x p H=> [|n IHn] x [|a l /andP [] H_path];last apply IHn.
Qed.

Lemma is_trace_drop g0 g0' trace trace' (H_trace: is_trace g0 trace) n:
  drop n trace = g0' :: trace' -> is_trace g0' (g0' :: trace').
Proof using.
  move => H_drop.
  destruct trace. inversion H_trace.
  destruct H_trace as [H_g0 H_trace]; subst.
  eapply path_drop' with (n:=n) in H_trace.
  unfold is_trace.
  destruct n.
    by rewrite drop0 in H_trace; rewrite drop0 in H_drop; inversion H_drop; subst.
    by rewrite H_drop in H_trace.
Qed.

Lemma path_gsteps_onth
      g0 trace (H_path : is_trace g0 trace)
      ix_p g_p (H_g_p : onth trace ix_p = Some g_p):
    forall (P : pred GState),
    ~~ P g0 -> P g_p ->
    (* exists n g1 g2, step_in_path_at g1 g2 n (g0::trace) /\ ~~ P g1 /\ P g2. *)
    exists n g1 g2, step_in_path_at g1 g2 n trace /\ ~~ P g1 /\ P g2.
Proof using.
  destruct trace;[by contradict H_path|].
  move: H_path => [H_g0 H_path];subst g.
  move=> P H_NPg0 H_Pg.
  have H_path' := path_prefix ix_p H_path.
  destruct ix_p as [|ix_p];
    first by exfalso;move:H_g_p H_NPg0;case => ->;rewrite H_Pg.
  change (onth trace ix_p = Some g_p) in H_g_p.

  pose proof (path_steps H_path' H_NPg0).
  have H_size_trace := onth_size H_g_p.
  rewrite -nth_last nth_take size_takel // (onth_nth H_g_p) in H.
  specialize (H H_Pg).
  move:H;clear -H_NPg0;move => [n H].

  exists n.
  unfold step_in_path_at.
  destruct (drop n (g0 :: take ix_p.+1 trace)) as [|x l] eqn: H_eq;[|destruct l];[done..|].
  rewrite -[g0::trace](cat_take_drop ix_p.+2).
  move/andP in H;exists x, g;split;[|assumption].
  rewrite drop_cat.
  case:ifP;[rewrite H_eq;done|].
  move => /negP /negP /=;rewrite ltnS -ltnNge => H_oversize.
  by rewrite drop_oversize // in H_eq.
Qed.

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

Definition users_before_round (r:nat) (g : GState) : Prop :=
  forall i (Hi : i \in g.(users)), user_before_round r (g.(users).[Hi]).

Definition messages_before_round (r:nat) (g : GState) : Prop :=
  forall (mailbox: {mset R * Msg}), mailbox \in codomf (g.(msg_in_transit)) ->
  forall deadline msg, (deadline,msg) \in mailbox ->
     msg_round msg < r.

Definition state_before_round r (g:GState) : Prop :=
  users_before_round r g
  /\ messages_before_round r g
  /\ (forall msg, msg \in g.(msg_history) -> msg_round msg < r).

Definition opred (T : Type) (P : pred T) : pred (option T) :=
  fun o => match o with
           | None => false
           | Some v => P v
           end.

Definition is_pending (target:UserId) (msg_body:Msg) : pred GState :=
  fun g => opred (fun (ms:{mset R * Msg}) => has (fun p => p.2 == msg_body) ms)
                 (g.(msg_in_transit).[?target]).

(*
(* possible lemmas for pending_honest_sent *)
Lemma new_msg_from_send_or_replay g1 g2 (H_step: g1 ~~> g2):
    forall target (key_msg2 : target \in g2.(msg_in_transit)) d pending_msg,
      (d,pending_msg) \in g2.(msg_in_transit).[key_msg2] ->
    (forall (key_msg1 : target \in g1.(msg_in_transit)),
      (d,pending_msg) \notin g1.(msg_in_transit).[key_msg1]) ->
    let sender := msg_sender pending_msg in
    user_honest sender g1 ->
    user_sent sender pending_msg g1 g2
    \/ pending_msg \in g1.(msg_history).
Proof using.
Abort.

Definition pending_in_history_after (r:nat)
           (msg_in_transit:{fmap UserId -> {mset R * Msg}}) (msg_history:{mset Msg}) : Prop :=
  forall uid (key : uid \in msg_in_transit) d pending_msg,
    (d,pending_msg) \in msg_in_transit.[key] ->
  r <= msg_round pending_msg ->
  pending_msg \in msg_history.

Lemma pending_in_history_after_invariant g1 g2 (H_step: g1 ~~> g2):
  forall r, pending_in_history_after r (g1.(msg_in_transit)) (g1.(msg_history))
         -> pending_in_history_after r (g2.(msg_in_transit)) (g2.(msg_history)).
Proof using.
  clear -H_step.
  destruct H_step;try exact (fun r H => H);autounfold with gtransition_unfold;destruct pre;simpl in * |- *.
  * move => r H_pending.
    unfold pending_in_history_after.
    move => uid0 key d pending_msg H_msg H_r.

    assert (uid0 \in domf msg_in_transit).
    move:(key). rewrite -!fsub1set => key'. refine (fsubset_trans key' _).
    apply send_broadcasts_domf. admit.
    rewrite dom_setf mem_fset1U //.
  (*  SearchAbout domf setf.
    apply send_i
    specialize (H_pending uid0). *)
Abort.

Lemma pending_in_history g0 trace (H_path: path gtransition g0 trace)
    r (H_start:state_before_round r g0):
    forall g ix,
      onth trace ix = Some g ->
    forall uid (key : uid \in g.(msg_in_transit)) d pending_msg,
      (d,pending_msg) \in g.(msg_in_transit).[key] ->
    r <= msg_round pending_msg ->
    pending_msg \in g.(msg_history).
Proof.
  move => g ix H_g uid key d pending_msg H_pending H_r.
  have H_path' := path_prefix ix.+1 H_path.
  have H_last := onth_take_last H_g g0.
Abort.
*)

Lemma utransition_msg_sender_good uid u msg result:
  uid # u ; msg ~> result ->
  forall m, m \in result.2 -> uid = msg_sender m.
Proof using.
  clear.
  by destruct 1 => /= m /Iter.In_mem /=;intuition;subst m.
Qed.

Lemma utransition_internal_sender_good uid u result:
  uid # u ~> result ->
  forall m, m \in result.2 -> uid = msg_sender m.
Proof using.
  clear.
  by destruct 1 => /= m /Iter.In_mem /=;intuition;subst m.
Qed.

Lemma replay_had_original
      g0 trace (H_path: is_trace g0 trace)
      r (H_start: state_before_round r g0):
  forall g ix, onth trace ix = Some g ->
  forall (msg:Msg), msg \in g.(msg_history) ->
    r <= msg_round msg ->
    exists send_ix, user_sent_at send_ix trace (msg_sender msg) msg.
Proof using.
  clear -H_path H_start.
  move => g ix H_g msg H_msg H_r.
  pose proof (path_gsteps_onth H_path H_g (P:=fun g => msg \in g.(msg_history))).
  cbv beta in H.
  have H_msg0: msg \notin g0.(msg_history)
    by clear -H_start H_r;apply/negP => H_msg;
       move: H_start => [] _ [] _ {H_msg}/(_ _ H_msg);rewrite ltnNge H_r.

  move:(H H_msg0 H_msg). clear -H_path.
  move => [n [g1 [g2 [H_step [H_pre H_post]]]]].
  exists n, g1, g2;split;[assumption|].
  apply (transition_from_path H_path), transitions_labeled in H_step.
  move: H_step => [lbl H_rel];clear -H_pre H_post H_rel.
  destruct lbl;
    try (exfalso;apply /negP: H_post;
         simpl in H_rel;decompose record H_rel;clear H_rel;subst g2;
         simpl;assumption).
  * (* deliver *)
    unfold user_sent.
    suff: s = msg_sender msg /\ msg \in l.
    move => [<- H_l].
    exists l;split;[|left;exists r, m];assumption.
    simpl in H_rel;decompose record H_rel;clear H_rel.
    move: H_post H_pre;subst g2.
    rewrite in_msetD.
    move=> /orP []; [by move => Hp Hn;exfalso;apply/negP: Hp|].
    rewrite in_seq_mset.
    move => H_l. split;[|assumption].
    by apply (utransition_msg_sender_good H H_l).
  * (* internal *)
    unfold user_sent.
    suff: s = msg_sender msg /\ msg \in l.
    move => [<- H_l].
    exists l;split;[|right];assumption.
    simpl in H_rel;decompose record H_rel;clear H_rel.
    move: H_post H_pre;subst g2.
    rewrite in_msetD.
    move=> /orP [];
      [by move => Hp Hn;exfalso;apply/negP: Hp|].
    rewrite in_seq_mset.
    move => H_l. split;[|assumption].
    by apply (utransition_internal_sender_good H0 H_l).
Qed.

Definition user_forged (msg:Msg) (g1 g2: GState) :=
  let: (mty,v,r,p,sender) := msg in
  related_by (lbl_forge_msg sender r p mty v) g1 g2.

Lemma broadcasts_prop
  uid (msg:Msg) (l:seq Msg)
  time (targets : {fset UserId}) (mailboxes' mailboxes : {fmap UserId -> {mset R * Msg}}):
  (odflt mset0 mailboxes'.[? uid] `<=` odflt mset0 mailboxes.[? uid])%mset ->
  match (send_broadcasts time targets mailboxes' l).[? uid] with
  | Some msg_mset => has (fun p : R * Msg => p.2 == msg) msg_mset
  | None => false
  end ->
  ~~
  match mailboxes.[? uid] with
  | Some msg_mset => has (fun p : R * Msg => p.2 == msg) msg_mset
  | None => false
  end -> msg \in l.
Proof using.
  clear.
  move => H_sub H_pre H_post.
  have{H_post}H_post: ~~has (fun p: R * Msg => p.2 == msg) (odflt mset0 mailboxes.[?uid])
    by case:fndP H_post;[|rewrite enum_mset0].

  rewrite send_broadcastsE in H_pre.
  case:mailboxes'.[?uid]/fndP => H_mb';
   [|by move:H_pre;rewrite not_fnd //;
     congr (uid \notin _): H_mb';apply updf_domf].

  have{H_post}H_post: ~~has (fun p: R * Msg => p.2 == msg) (mailboxes'.[H_mb'])
    by apply/contraNN:H_post => /hasP /= [x H_in H_x];
       apply/hasP;exists x;[apply (msubset_subset H_sub);rewrite in_fnd|].

  move: {mailboxes H_sub}H_pre.

  case:(uid \in targets)/boolP=>H_tgt;
    [|by apply contraTT;rewrite updf_update'].

  rewrite updf_update {targets H_tgt}// => /hasP /=[[d msg'] H_in /eqP /=H_msg].
  move:H_msg H_in=> {msg'}-> /in_merge_msgs [//|H_in].

  move/negP in H_post;contradict H_post.
  by apply /hasP;exists (d,msg).
Qed.

Lemma pending_sent_or_forged
      g0 trace (H_path: is_trace g0 trace)
      r (H_start: state_before_round r g0):
    forall g_pending pending_ix,
      onth trace pending_ix = Some g_pending ->
    forall uid (key_msg : uid \in g_pending.(msg_in_transit)) d pending_msg,
      (d,pending_msg) \in g_pending.(msg_in_transit).[key_msg] ->
    let sender := msg_sender pending_msg in
    r <= msg_round pending_msg ->
    exists send_ix g1 g2, step_in_path_at g1 g2 send_ix trace
      /\ (user_sent sender pending_msg g1 g2
          \/ user_forged pending_msg g1 g2).
Proof using.
  clear -H_path H_start.
  intros g_pending pending_ix H_g uid key_msg d msg H_msg sender H_round.
  subst sender.
  set P := fun g => match g.(msg_in_transit).[? uid] with
                  | Some msg_mset => has (fun (p:R*Msg) => p.2 == msg) msg_mset
                  | None => false
                    end.
  have H_P: P g_pending by rewrite /P in_fnd;apply/hasP;exists (d,msg).
  have H_P0: ~~P g0.
  {
  unfold P;simpl.
  clear -H_start H_round.
  case Hmb: (_.[?uid]) => [mb|//].
  move: H_start => [_ [H_msgs _]].
  rewrite leqNgt in H_round.
  apply/contraNN: H_round.

  move /hasP =>[[d msg'] H_in /eqP /= ?];subst msg'.
  apply: H_msgs H_in.
  by apply/codomfP;exists uid.
  }
  (* msg has round >= r, while g0 comes before r, and so msg \notin mmailbox0 *)
  (* if the user does not have a mailbox, then it's already true*)
  move: {H_P0 H_P}(path_gsteps_onth H_path H_g H_P0 H_P).
  subst P;cbv beta.

  move => [n [g1 [g2 [H_step [H_pre H_post]]]]].

  move: (H_step) => /(transition_from_path H_path) /transitions_labeled [lbl H_rel].
  destruct lbl.
    (* tick *)
    exfalso;apply /negP: H_post;simpl in H_rel;decompose record H_rel;clear H_rel;subst g2;
      simpl;assumption.
    (* deliver *)
    exists n,g1,g2;split;[assumption|].
    left. unfold user_sent.
    suff: s = msg_sender msg /\ msg \in l
      by move => [<- H_l];exists l;split;[|left;exists r0, m];assumption.

    simpl in H_rel;decompose record H_rel;clear H_rel.
    suff: msg \in l by split;[apply (utransition_msg_sender_good H)|];assumption.
    move: H_post H_pre;subst g2;apply broadcasts_prop;
    by rewrite fnd_set;case:ifP => [/eqP ->|_];
                                     [rewrite in_fnd;exact:msubD1set|exact:msubset_refl].
    (* internal *)
    exists n,g1,g2;split;[assumption|].
    left. unfold user_sent.
    suff: s = msg_sender msg /\ msg \in l by
        move => [<- H_l];exists l;split;[|right];assumption.

    simpl in H_rel;decompose record H_rel;clear H_rel.
    suff: msg \in l by split;[apply (utransition_internal_sender_good H0)|];assumption.
    move: H_post H_pre;subst g2;apply broadcasts_prop;
    by apply msubset_refl.
    (* exit partition *)
    exfalso. apply /negP: H_post. simpl in H_rel;decompose record H_rel;clear H_rel. subst g2.
    unfold recover_from_partitioned, reset_msg_delays.
    (* reset_msg_delays preserves the set of messages, but not their deadlines *)
    apply/contraNN:H_pre;clear.
    cbn -[eq_op] => H_post.
    case:fndP => H_in;move:H_post;
       [rewrite updf_update //
       |by rewrite not_fnd //;
           change (uid \notin ?f) with (uid \notin domf f);
        rewrite -updf_domf].
    by rewrite /reset_user_msg_delays map_mset_has (eq_has (a2:=(fun p => p.2 == msg))).
    (* enter partition *)
    exfalso;apply /negP: H_post;simpl in H_rel;decompose record H_rel;clear H_rel;subst g2;
      simpl;assumption.
    (* corrupt user *)
    exfalso;apply /negP: H_post;simpl in H_rel;decompose record H_rel;clear H_rel;subst g2.
    unfold corrupt_user_result, drop_mailbox_of_user; simpl.
    (* the empty msg mset cannot have a message *)
    set m1 := (msg_in_transit g1).[? s].
    by destruct m1;[rewrite fnd_set;case:ifP;[rewrite enum_mset0|]|].
    (* replay a message *)
    (* replayed message must have originally been sent honestly *)
    rename s into target.
    move: H_rel => /= [ustate_key [hist_msg [H_tgt_honest [H_msg_history H_g2]]]].
    pose proof (replay_had_original H_path H_start (step_in_path_onth_pre H_step) H_msg_history).
    move: H.
    suff ->: hist_msg = msg.
    move/(_ H_round) => [send_ix [g3 [g4]]];clear => H. exists send_ix, g3, g4.
    tauto.
    subst g2.
    symmetry; apply /eqP. rewrite -mem_seq1.
    apply/broadcasts_prop: H_post H_pre.
    apply msubset_refl.
    (* forge a message *)
    exists n,g1,g2;split;[assumption|].
    right.
    unfold user_forged.
    suff ->: msg = (m,e,n0,n1,s) by assumption.
    simpl in H_rel;decompose record H_rel;clear H_rel;subst g2.
    apply/eqP;rewrite -mem_seq1.
    apply/broadcasts_prop: H_post H_pre.
    apply msubset_refl.
Qed.

(* A message from an honest user was actually sent in the trace *)
(* Use this to relate an honest user having received a quorum of messages
   to some honest user having sent those messages *)
(* Hopefully the statement can be cleaned up *)
Lemma pending_honest_sent: forall g0 trace (H_path: is_trace g0 trace),
    forall r, state_before_round r g0 ->
    forall g_pending pending_ix,
      onth trace pending_ix = Some g_pending ->
    forall uid (key_msg : uid \in g_pending.(msg_in_transit)) d pending_msg,
      (d,pending_msg) \in g_pending.(msg_in_transit).[key_msg] ->
    let sender := msg_sender pending_msg in
    honest_during_step (msg_step pending_msg) sender trace ->
    r <= msg_round pending_msg ->
    exists send_ix, user_sent_at send_ix trace sender pending_msg.
Proof using.
  clear.
  move => g0 trace H_path r H_start g ix H_g
             uid key_msg d msg H_msg sender H_honest H_round.
  have [send_ix [g1 [g2 [H_step H_send]]]]
    := pending_sent_or_forged H_path H_start H_g H_msg H_round.
  exists send_ix, g1, g2.
  split;[assumption|].
  case:H_send => [//|H_forged];exfalso.
  destruct msg as [[[[mty v] r1] p] forger].
  rewrite /user_forged /= in H_forged;decompose record H_forged;clear H_forged.
  move:H => [H_corrupt H_le].
  have {H_honest} := all_onth H_honest (step_in_path_onth_pre H_step).
  rewrite /upred (in_fnd x) H_corrupt implybF => /negP;apply;apply /step_leP.
  refine (step_le_trans H_le _).
  apply/step_leP;rewrite /msg_step /step_leb !eq_refl !ltnn /=.
  have: mtype_matches_step mty v x0 by assumption.
  by clear;destruct mty,v,1.
Qed.

(*
   This lemma connects message receipt to the sending of a message,
   used to reach back to an earlier honest transition.
 *)
Lemma received_was_sent g0 trace (H_path: is_trace g0 trace)
    r0 (H_start: state_before_round r0 g0)
    u d msg (H_recv: msg_received u d msg trace):
    let: (_,_,r,_,sender) := msg in
    r0 <= r ->
    honest_during_step (msg_step msg) (sender:UserId) trace ->
    exists ix, user_sent_at ix trace sender msg.
Proof using.
  clear -H_path H_start H_recv.
  move: H_recv => [ix_r [ms H_deliver]].
  rewrite {1}[msg]surjective_pairing
          [msg.1]surjective_pairing
          [msg.1.1]surjective_pairing
          [msg.1.1.1]surjective_pairing.
  set msg_r := msg.1.1.2.
  set sender := msg.2.
  move => H_round H_honest_sender.

  move:H_deliver => [g1_d [g2_d [H_step_d H_rel_d]]].
  have {H_step_d}H_g1_d := step_in_path_onth_pre H_step_d.

  move:H_rel_d => [ukey1 [upost H_step]].
  move:H_step => [H_ustep] [H_honest_recv] [key_mailbox] [H_msg_in H_g2_d].
  clear g2_d H_g2_d.

  pose proof (pending_honest_sent H_path H_start H_g1_d H_msg_in) as H.
  specialize (H H_honest_sender H_round).
  exact H.
Qed.

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
(*
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
    | [H: repropose_ok _ _ _ _ _ |- _] => unfold repropose_ok in H; use_hyp H
    | [H: no_propose_ok _ _ _ _ |- _] => unfold no_propose_ok in H; use_hyp H
    | [H: softvote_new_ok _ _ _ _ _ |- _] => unfold softvote_new_ok in H; use_hyp H
    | [H: softvote_repr_ok _ _ _ _ _ |- _] => unfold softvote_repr_ok in H; use_hyp H
    | [H: no_softvote_ok _ _ _ _ |- _] => unfold no_softvote_ok in H; use_hyp H
    | [H: certvote_ok _ _ _ _ _ _ |- _] => unfold certvote_ok in H; use_hyp H
    | [H: no_certvote_ok _ _ _ _ |- _] => unfold no_certvote_ok in H; use_hyp H
    | [H: nextvote_val_ok _ _ _ _ _ _ _ |- _] => unfold nextvote_val_ok in H; use_hyp H
    | [H: nextvote_open_ok _ _ _ _ _ _ _ |- _] => unfold nextvote_open_ok in H; use_hyp H
    | [H: nextvote_stv_ok _ _ _ _ _ _ _ /\ _ |- _] => destruct H as [H Hs]; unfold nextvote_stv_ok in H; use_hyp H
    | [H: no_nextvote_ok _ _ _ _ _ |- _] => unfold no_nextvote_ok in H; use_hyp H
    | [H: set_softvotes _ _ _ _ |- _] => unfold set_softvotes in H; use_hyp H
    | [H: certvote_timeout_ok _ _ _ _ |- _] => unfold timout_ok in H; use_hyp H
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
Abort.
*)

(* Priority:LIVENESS *)
(* The global transition relation preserves sensibility of global states *)
(*
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
Abort.
*)

(* Generalization of preservation of sensibility to paths *)
(*
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
*)

(* SAFETY *)

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
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
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
- case: H => tH [vH oH].
  case: vH => rH [pH sH].
  unfold ustate_after => /=.
  do 2! [right]. do 2! [split; auto]. by rewrite sH.
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
  move => sender_key r p s mtype mval Hhave Hcomm Hmatch.
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

Lemma gtrans_preserves_users: forall gs1 gs2,
  gs1 ~~> gs2 -> domf gs1.(users) = domf gs2.(users).
Proof using.
move => gs1 gs2.
elim => //.
- move => increment pre Htick.
  by rewrite -tick_users_domf.
- move => pre uid msg_key pending Hpending key_ustate ustate_post sent Hcorrupt Huser /=.
  by rewrite mem_fset1U //.
- move => pre uid ustate_key Hcorrupt ustate_post sent Huser /=.
  by rewrite mem_fset1U //.
- move => pre uid ustate_key Hcorrupt /=.
  by rewrite mem_fset1U //.
Qed.

Lemma gtrans_domf_users: forall gs1 gs2,
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

(* is_trace assumption breaks this, but this is not used anywhere *)
Lemma greachable_domf_users: forall g1 g2,
    greachable g1 g2 -> domf g1.(users) `<=` domf g2.(users).
Proof using.
  move => g1 g2 [trace H_path H_last].
  destruct trace. inversion H_path.
  destruct H_path as [H_g0 H_path]. subst g.
  revert trace g1 H_path H_last.
  elim => //=.
  - by move => _ _ <-.
  - move => a l IH g1 /andP [/asboolP H_step H_path] H_last.
    apply gtrans_domf_users in H_step.
    apply /(fsubset_trans H_step){H_step}.
    by apply IH.
Qed.

(* Generalization of non-decreasing round-period-step results to paths *)
Lemma greachable_rps_non_decreasing : forall g1 g2 uid us1 us2,
  greachable g1 g2 ->
  g1.(users).[? uid] = Some us1 -> g2.(users).[? uid] = Some us2 ->
  ustate_after us1 us2.
Proof using.
move => g1 g2 uid us1 us2.
case => gtrace Hpath Hlast.
destruct gtrace. inversion Hpath.
destruct Hpath as [H_g0 Hpath]; subst g.
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

(* A user has certvoted a value for a given period along a given path *)
Definition certvoted_in_path_at ix path uid r p v : Prop :=
  user_sent_at ix path uid (Certvote,val v,r,p,uid).

Definition certvoted_in_path path uid r p v : Prop :=
  exists ix, certvoted_in_path_at ix path uid r p v.

Definition certified_in_period trace r p v :=
  exists (certvote_quorum:{fset UserId}),
     certvote_quorum `<=` committee r p 3
  /\ #|` certvote_quorum | >= tau_c
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
  /\ #|` softvote_quorum | >= tau_s
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
  /\ #|` nextvote_quorum | >= tau_b
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
  /\ #|` nextvote_quorum | >= tau_v
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

Lemma softvote_value_unique uid r p g1 g2 v:
  user_sent uid (Softvote,val v,r,p,uid) g1 g2 ->
  user_honest uid g1 ->
  forall v2, user_sent uid (Softvote,val v2,r,p,uid) g1 g2 ->
  v2 = v.
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

Lemma at_greachable
      g0 states (H_path: is_trace g0 states)
      ix1 ix2 (H_le : ix1 <= ix2)
      g1 (H_g1 : onth states ix1 = Some g1)
      g2 (H_g2 : onth states ix2 = Some g2):
  greachable g1 g2.
Proof using.
  clear -H_path H_le H_g1 H_g2.
  assert (ix2 < size states) by
  (rewrite -subn_gt0 -size_drop;
   move: H_g2;clear;unfold onth;
   by destruct (drop ix2 states)).

  exists (g1 :: (drop ix1.+1 (take ix2.+1 states))).
  {
    eapply is_trace_prefix with (n:=ix2.+1) in H_path; try (by intuition).
    eapply is_trace_drop with (g0':=g1) (n:=ix1) in H_path; try eassumption.
    rewrite {1}(drop_nth g2).
    rewrite nth_take //.
    rewrite (onth_nth H_g1) //.
    rewrite size_take.
    destruct (ix2.+1 < size states); by ppsimpl; lia.
  }
  {
    simpl.
    rewrite (last_nth g1) size_drop size_takel //.
    move:(H_le). rewrite leq_eqVlt.
    move/orP => [H_eq | H_lt].
    by move/eqP in H_eq;subst;rewrite subnn;simpl;congruence.
    by rewrite subSn //= nth_drop subnKC // nth_take ?ltnS // (onth_nth H_g2).
  }
Qed.

Lemma order_ix_from_steps g0 trace (H_path: is_trace g0 trace):
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
      g0 path (H_path : is_trace g0 path)
      ix ix2 (H_lt : ix < ix2)
      pre post (H_step : step_in_path_at pre post ix path)
      pre2 post2 (H_step2 : step_in_path_at pre2 post2 ix2 path):
  greachable post pre2.
Proof using.
  apply step_in_path_onth_post in H_step.
  apply step_in_path_onth_pre in H_step2.
  eapply at_greachable;eassumption.
Qed.

Lemma order_state_from_step g0 states (H_path: is_trace g0 states) uid
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

Lemma order_sends g0 trace (H_path: is_trace g0 trace) uid
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

(* basic lemma for propagating honest backwards *)
Lemma user_honest_from_during g0 trace (H_path: is_trace g0 trace):
  forall ix g1,
    onth trace ix = Some g1 ->
  forall uid (H_in : uid \in g1.(users)),
    honest_during_step (step_of_ustate (g1.(users)[`H_in])) uid trace ->
  user_honest uid g1.
Proof using.
  move => ix g1 H_onth uid H_in /all_nthP.
  move/(_ g1 ix (onth_size H_onth)).
  rewrite (onth_nth H_onth g1) /user_honest /upred (in_fnd H_in).
  move/implyP;apply.
  by apply /step_leP /step_le_refl.
Qed.

(* L1: An honest user cert-votes for at most one value in a period *)
(* :: In any global state, an honest user either never certvotes in a period or certvotes once in step 3 and never certvotes after that during that period
   :: If an honest user certvotes in a period (step 3) then he will never certvote again in that period *)
Lemma no_two_certvotes_in_p : forall g0 trace (H_path : is_trace g0 trace) uid r p,
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

(* 'user_sent uid (Softvote, val v1, r, p, uid) pre post' implies the
   round-period-step of user state at pre is exactly r, p, 2 *)
(* not really needed *)
Lemma step_of_softvote_sent uid r p: forall v pre post,
  user_sent uid (Softvote, val v, r, p, uid) pre post ->
  forall ustate, pre.(users).[? uid] = Some ustate ->
  (step_of_ustate ustate) = (r, p, 2).
Proof using delays_order.
  intros v pre post H_sent ustate H_ustate.
  destruct H_sent as [ms [H_msg [[d1 [in1 H_step]]|H_step]]].
  destruct H_step as (key_ustate & ustate_post & H_step & H_honest & key_mailbox & H_msg_in_mailbox & ->).
  remember (ustate_post,ms) as ustep_out in H_step.
  destruct H_step; injection Hequstep_out; clear Hequstep_out;intros <- <-; revert H_msg; move/Iter.In_mem => H_msg; try contradiction.
  simpl in H_msg; destruct H_msg; try contradiction.
  inversion H0;subst;clear H0.
  destruct H_step as (key_user & ustate_post & H_honest & H_step & ->).
  assert (pre.(users)[` key_user] = ustate)
    by (rewrite in_fnd in H_ustate;injection H_ustate;trivial).
  rewrite -> H in * |- *.
  inversion H_step;clear H_step;move: H;subst;move => H;
  move: H_msg => /Iter.In_mem /=;intuition;try discriminate.

  unfold softvote_new_ok in H3;decompose record H3;clear H3.
  move: H6 => [-> [-> ->]]. congruence.
  unfold softvote_repr_ok in H3;decompose record H3;clear H3.
  move: H6 => [-> [-> ->]]. congruence.
Qed.

(* Priority:HIGH
   Proof should be very similar to no_two_certvotes_in_p *)
(* L2: An honest user soft-votes for at most one value in a period *)
Lemma no_two_softvotes_in_p : forall g0 trace (H_path : is_trace g0 trace) uid r p,
    forall ix1 v1, softvoted_in_path_at ix1 trace uid r p v1 ->
    forall ix2 v2, softvoted_in_path_at ix2 trace uid r p v2 ->
                   ix1 = ix2 /\ v1 = v2.
Proof using.
  clear.
  move => g0 trace H_path uid r p.
  move => ix1 v1 H_send1 ix2 v2 H_send2.

  have: ix1 <= ix2 by
  eapply (order_sends H_path H_send1 H_send2 (step_le_refl _)).
  have: ix2 <= ix1 by
  eapply (order_sends H_path H_send2 H_send1 (step_le_refl _)).

  move => H_le1 H_le2.
  have: ix1 = ix2.
  apply/eqP. rewrite eqn_leq. apply/andP. split;assumption.
  intro;subst ix2;clear H_le1 H_le2.
  split;[reflexivity|].

  unfold softvoted_in_path_at in H_send1, H_send2.
  destruct H_send1 as [pre1 [post1 [H_step1 H_send1]]].
  destruct H_send2 as [pre2 [post2 [H_step2 H_send2]]].

  destruct (step_ix_same H_step1 H_step2) as [-> ->].
  symmetry.
  refine (softvote_value_unique H_send1 _ H_send2).
  (* honesty follows from user_sent *)
  destruct H_send1 as [ms' [H_msg' [[d1' [in1' H_step']]|H_step']]].
    destruct H_step' as (key_ustate' & ustate_post' & H_step' & H_honest' & key_mailbox' & H_msg_in_mailbox' & ->).
    unfold user_honest. rewrite in_fnd. intuition.
  destruct H_step' as (key_user' & ustate_post' & H_honest' & H_step' & ->).
  unfold user_honest. rewrite in_fnd. intuition.
Qed.


(* A user has nextvoted bottom for a given period along a given path *)
Definition nextvoted_open_in_path_at ix path uid r p s : Prop :=
  user_sent_at ix path uid (Nextvote_Open, step_val s,r,p,uid).

Definition nextvoted_open_in_path path r p s uid : Prop :=
  exists ix, nextvoted_open_in_path_at ix path uid r p s.

(* A user has nextvoted a value for a given period along a given path *)
Definition nextvoted_value_in_path path r p s uid v : Prop :=
  exists ix, user_sent_at ix path uid (Nextvote_Val, next_val v s, r, p, uid).

Lemma certvote_postcondition uid v r p g1 g2:
  user_sent uid (Certvote,val v,r,p,uid) g1 g2 ->
  forall u, g2.(users).[?uid] = Some u ->
  v \in certvals u r p /\
        exists b, b \in u.(blocks) r /\ valid_block_and_hash b v.
Proof using.
  move => H_sent u H_u.
  destruct H_sent as [ms [H_msg [[d1 [in1 H_step]]|H_step]]].
  (* need to grab u *)
  * { (* message delivery cases *)
      destruct H_step as (key_ustate & ustate_post & H_step & H_honest
                          & key_mailbox & H_msg_in_mailbox & ->).
      remember (ustate_post,ms) as ustep_out in H_step.
      destruct H_step; injection Hequstep_out; clear Hequstep_out;
      intros <- <-; revert H_msg; move/Iter.In_mem => H_msg; try contradiction.
      simpl in H_msg; destruct H_msg; try contradiction.
      inversion H0;subst;clear H0.
      unfold certvote_ok in H;decompose record H;clear H.
      rewrite fnd_set eq_refl in H_u. case: H_u => {u}<-.
      unfold certvote_result.
      split;[|exists b;split];assumption.
    }
  * { (* internal transition cases *)
      destruct H_step as (key_user & ustate_post & H_honest & H_step & ->).
      remember (ustate_post,ms) as ustep_out in H_step.
      destruct H_step; injection Hequstep_out; clear Hequstep_out;
        intros <- <-; move/Iter.In_mem in H_msg; try contradiction;
      simpl in H_msg; destruct H_msg as [H_msg | H_msg]; try contradiction;
      try destruct H_msg as [H_msg | H_msg]; inversion H_msg;subst;clear H_msg.
      rewrite fnd_set eq_refl in H_u. case:H_u => H_u.
      subst.
      unfold certvote_ok in H;decompose record H;clear H.
      split;[|exists b;split];assumption.
    }
Qed.

Lemma nextvote_open_precondition g1 g2 uid r p s:
  user_sent uid (Nextvote_Open, step_val s, r, p, uid) g1 g2 ->
  forall u, g1.(users).[?uid] = Some u ->
  nextvote_open_ok u uid r p s.
Proof using.
  move => H_sent u H_u.
  destruct H_sent as [ms [H_msg [[d1 [in1 H_step]]|H_step]]].
  * { (* message delivery cases *)
      destruct H_step as (key_ustate & ustate_post & H_step & H_honest
                          & key_mailbox & H_msg_in_mailbox & ->).
      remember (ustate_post,ms) as ustep_out in H_step.
      destruct H_step; injection Hequstep_out; clear Hequstep_out;
      intros <- <-; revert H_msg; move/Iter.In_mem => H_msg; try contradiction.
      simpl in H_msg; destruct H_msg; try contradiction; inversion H0.
    }
  * { (* internal transition cases *)
      destruct H_step as (key_user & ustate_post & H_honest & H_step & ->).
      remember (ustate_post,ms) as ustep_out in H_step.
      assert ((global_state.users UserId UState [choiceType of Msg] g1) [` key_user] = u).
      rewrite in_fnd in H_u; inversion H_u; trivial.
      rewrite H in H_step. clear H.
      destruct H_step; injection Hequstep_out; clear Hequstep_out;
        intros <- <-; revert H_msg; move/Iter.In_mem => H_msg; try contradiction;
      simpl in H_msg; destruct H_msg as [H_msg | H_msg]; try contradiction;
      try destruct H_msg as [H_msg | H_msg]; inversion H_msg.
      subst; assumption.
    }
Qed.

Lemma nextvote_val_precondition g1 g2 uid v r p s:
  user_sent uid (Nextvote_Val, next_val v s, r, p, uid) g1 g2 ->
  forall u, g1.(users).[?uid] = Some u ->
  (exists b, nextvote_val_ok u uid v b r p s) \/
  (nextvote_stv_ok u uid r p s /\ u.(stv) p = Some v).
Proof.
  move => H_sent u H_u.
  destruct H_sent as [ms [H_msg [[d1 [in1 H_step]]|H_step]]].
  * { (* message delivery cases *)
      destruct H_step as (key_ustate & ustate_post & H_step & H_honest
                          & key_mailbox & H_msg_in_mailbox & ->).
      remember (ustate_post,ms) as ustep_out in H_step.
      destruct H_step; injection Hequstep_out; clear Hequstep_out;
      intros <- <-; revert H_msg; move/Iter.In_mem => H_msg; try contradiction.
      simpl in H_msg; destruct H_msg; try contradiction; inversion H0.
    }
  * { (* internal transition cases *)
      destruct H_step as (key_user & ustate_post & H_honest & H_step & ->).
      remember (ustate_post,ms) as ustep_out in H_step.
      assert ((global_state.users UserId UState [choiceType of Msg] g1) [` key_user] = u).
      rewrite in_fnd in H_u; inversion H_u; trivial.
      rewrite H in H_step. clear H.
      destruct H_step; injection Hequstep_out; clear Hequstep_out;
        intros <- <-; revert H_msg; move/Iter.In_mem => H_msg; try contradiction;
      simpl in H_msg; destruct H_msg as [H_msg | H_msg]; try contradiction;
      try destruct H_msg as [H_msg | H_msg]; inversion H_msg.
      left; exists b; subst; assumption.
      right;subst;assumption.
    }
Qed.

(* Several lemmas here showing that some of the
   sets in the UState may only increase over time,
   or within a round *)
Lemma softvotes_utransition_internal:
  forall uid pre post msgs, uid # pre ~> (post, msgs) ->
  forall r p, pre.(softvotes) r p \subset post.(softvotes) r p.
Proof using.
  move => uid pre post msgs step r p.
  remember (post,msgs) as result eqn:H_result;
  destruct step;case:H_result => [? ?];subst;done.
Qed.

Lemma softvotes_utransition_deliver:
  forall uid pre post m msgs, uid # pre ; m ~> (post, msgs) ->
  forall r p,
    pre.(softvotes) r p \subset post.(softvotes) r p.
Proof using.
  move => uid pre post m msgs step r p;
  remember (post,msgs) as result eqn:H_result;
    destruct step;case:H_result => [? ?];subst;
  destruct pre;simpl;autounfold with utransition_unfold;
    repeat match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b end;
  try (by apply subxx_hint);
  by apply/subsetP => x H_x;rewrite ?in_cons mem_undup H_x ?orbT.
Qed.

Lemma softvotes_gtransition g1 g2 (H_step:g1 ~~> g2) uid:
  forall u1, g1.(users).[?uid] = Some u1 ->
  exists u2, g2.(users).[?uid] = Some u2
             /\ forall r p, u1.(softvotes) r p \subset u2.(softvotes)  r p.
Proof using.
  clear -H_step => u1 H_u1.
  have H_in1: (uid \in g1.(users)) by rewrite -fndSome H_u1.
  have H_in1': g1.(users)[`H_in1] = u1 by rewrite in_fnd in H_u1;case:H_u1.
  destruct H_step;simpl users;autounfold with gtransition_unfold;
    try (rewrite fnd_set;case H_eq:(uid == uid0);
      [move/eqP in H_eq;subst uid0|]);
    try (eexists;split;[eassumption|done]);
    first rewrite updf_update //;
    (eexists;split;[reflexivity|]).
  * (* tick *)
    rewrite H_in1' /user_advance_timer.
    by match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b end.
  * (* deliver *)
    move:H1. rewrite ?(eq_getf _ H_in1) H_in1'. apply softvotes_utransition_deliver.
  * (* internal *)
    move:H0. rewrite ?(eq_getf _ H_in1) H_in1'. apply softvotes_utransition_internal.
  * (* corrupt *)
    rewrite ?(eq_getf _ H_in1) H_in1'. done.
Qed.

Lemma softvotes_monotone g1 g2 (H_reach:greachable g1 g2) uid:
  forall u1, g1.(users).[?uid] = Some u1 ->
  forall u2, g2.(users).[?uid] = Some u2 ->
  forall r p,
    u1.(softvotes) r p \subset u2.(softvotes)  r p.
Proof using.
  clear -H_reach.
  move => u1 H_u1 u2 H_u2.
  destruct H_reach as [trace H_path H_last].
  destruct trace. inversion H_path.
  destruct H_path as [H_g0 H_path]. subst g.
  move: g1 H_path H_last u1 H_u1.
  induction trace.
  * simpl. by move => g1 _ <- u1;rewrite H_u2{H_u2};case => ->.
  * cbn [path last] => g1 /andP [/asboolP H_step H_path] H_last u1 H_u1 r p.
    specialize (IHtrace a H_path H_last).
    have [umid [H_umid H_sub]] := softvotes_gtransition H_step H_u1.
    specialize (H_sub r p).
    specialize (IHtrace umid H_umid r p).
    refine (subset_trans H_sub IHtrace).
Qed.

Lemma soft_weight_monotone g1 g2 (H_reach:greachable g1 g2) uid:
  forall u1, g1.(users).[?uid] = Some u1 ->
  forall u2, g2.(users).[?uid] = Some u2 ->
  forall v r p,
    soft_weight v u1 r p <= soft_weight v u2 r p.
Proof using.
  move => u1 H_u1 u2 H_u2 v r p.
  have H_mono := softvotes_monotone H_reach H_u1 H_u2 r p.
  apply fsubset_leq_card.
  unfold softvoters_for.
  move: (u1.(softvotes)) (u2.(softvotes)) H_mono;clear => s1 s2 /subsetP H_mono.
  apply subset_imfset.
  simpl.
  move => x /andP [H_x_s1 H_val].
  by apply/andP;split;[apply/H_mono|].
Qed.

Lemma blocks_utransition_internal:
  forall uid pre post msgs, uid # pre ~> (post, msgs) ->
  forall r, pre.(blocks) r \subset post.(blocks) r.
Proof using.
  move => uid pre post msgs step r.
  remember (post,msgs) as result eqn:H_result;
  destruct step;case:H_result => [? ?];subst;done.
Qed.

Lemma blocks_utransition_deliver:
  forall uid pre post m msgs, uid # pre ; m ~> (post, msgs) ->
  forall r,
    pre.(blocks) r \subset post.(blocks) r.
Proof using.
  move => uid pre post m msgs step r;
  remember (post,msgs) as result eqn:H_result;
    destruct step;case:H_result => [? ?];subst;
  destruct pre;simpl;autounfold with utransition_unfold;
    repeat match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b
           | _ => progress simpl end;
  try (by apply subxx_hint);
  by apply/subsetP => x H_x;rewrite ?in_cons mem_undup H_x ?orbT.
Qed.

Lemma blocks_gtransition g1 g2 (H_step:g1 ~~> g2) uid:
  forall u1, g1.(users).[?uid] = Some u1 ->
  exists u2, g2.(users).[?uid] = Some u2
             /\ forall r, u1.(blocks) r \subset u2.(blocks) r.
Proof using.
  clear -H_step => u1 H_u1.
  have H_in1: (uid \in g1.(users)) by rewrite -fndSome H_u1.
  have H_in1': g1.(users)[`H_in1] = u1 by rewrite in_fnd in H_u1;case:H_u1.
  destruct H_step;simpl users;autounfold with gtransition_unfold;
    try (rewrite fnd_set;case H_eq:(uid == uid0);
      [move/eqP in H_eq;subst uid0|]);
    try (eexists;split;[eassumption|done]);
    first rewrite updf_update //;
    (eexists;split;[reflexivity|]).
  * (* tick *)
    rewrite H_in1' /user_advance_timer.
    by match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b end.
  * (* deliver *)
    move:H1. rewrite ?(eq_getf _ H_in1) H_in1'. apply blocks_utransition_deliver.
  * (* internal *)
    move:H0. rewrite ?(eq_getf _ H_in1) H_in1'. apply blocks_utransition_internal.
  * (* corrupt *)
    rewrite ?(eq_getf _ H_in1) H_in1'. done.
Qed.

Lemma blocks_monotone g1 g2 (H_reach: greachable g1 g2) uid:
  forall u1, g1.(users).[? uid] = Some u1 ->
  forall u2, g2.(users).[? uid] = Some u2 ->
  forall r, u1.(blocks) r \subset u2.(blocks) r.
Proof using.
  clear -H_reach.
  move => u1 H_u1 u2 H_u2.
  destruct H_reach as [trace H_path H_last].
  destruct trace. inversion H_path.
  destruct H_path as [H_g0 H_path]. subst g.
  move: g1 H_path H_last u1 H_u1.
  induction trace.
  * simpl. by move => g1 _ <- u1;rewrite H_u2{H_u2};case => ->.
  * cbn [path last] => g1 /andP [/asboolP H_step H_path] H_last u1 H_u1 r.
    specialize (IHtrace a H_path H_last).
    have [umid [H_umid H_sub]] := blocks_gtransition H_step H_u1.
    specialize (H_sub r).
    specialize (IHtrace umid H_umid r).
    refine (subset_trans H_sub IHtrace).
Qed.

(* L3: If an honest user cert-votes for a value in step 3, the user will NOT next-vote bottom in the same period
*)
Lemma certvote_excludes_nextvote_open_in_p g0 trace (H_path: is_trace g0 trace) uid r p s v:
  honest_during_step (r,p,s) uid trace ->
  certvoted_in_path trace uid r p v -> ~ nextvoted_open_in_path trace r p s uid .
Proof using.
  clear -H_path.
  move => H_honest [ix_cv H_cv] [ix_nv H_nv].
  move: (H_cv) => [g1_cv [g2_cv [H_step_cv H_vote_cv]]].
  move: (H_nv) => [g1_nv [g2_nv [H_step_nv H_vote_nv]]].

  have H_key1_nv := user_sent_in_pre H_vote_nv.
  set ustate_nv : UState := g1_nv.(users)[`H_key1_nv].
  have H_lookup_nv : _ = Some ustate_nv := in_fnd H_key1_nv.
  have H_nv_precond := nextvote_open_precondition H_vote_nv H_lookup_nv.

  have H_key2_cv := user_sent_in_post H_vote_cv.
  set ustate_cv : UState := g2_cv.(users)[`H_key2_cv].
  have H_lookup_cv : _ = Some ustate_cv := in_fnd H_key2_cv.
  have H_softvotes := certvote_postcondition H_vote_cv H_lookup_cv.

  assert (ix_cv < ix_nv) as H_lt.
  {
  apply (order_ix_from_steps H_path (step_in_path_onth_pre H_step_cv) (step_in_path_onth_pre H_step_nv)
                             (key1:=user_sent_in_pre H_vote_cv) (key2:=user_sent_in_pre H_vote_nv)).
  rewrite (utransition_label_start H_vote_cv);[|by apply in_fnd].
  rewrite (utransition_label_start H_vote_nv);[|by apply in_fnd].
  move:H_nv_precond;clear;simpl;unfold nextvote_open_ok;tauto.
  }

  have H_reach: greachable g2_cv g1_nv := steps_greachable H_path H_lt H_step_cv H_step_nv.

  move: H_nv_precond. unfold nextvote_open_ok.
  move => [] _ [] _ [] _ [] _ [] H_no_softvotes _.

  clear -H_reach H_softvotes H_lookup_cv H_lookup_nv H_no_softvotes.
  specialize (H_no_softvotes v).
  have: v \in certvals ustate_nv r p.
  {
    move: H_softvotes => [H] _. move: H.
    rewrite !mem_filter.
    move/andP => [H_tau H_votes]. apply/andP.
    split.
      by apply/(leq_trans H_tau) /(soft_weight_monotone H_reach H_lookup_cv H_lookup_nv).
      have H_subset := softvotes_monotone H_reach H_lookup_cv H_lookup_nv r p.
      move: H_subset H_votes.
      unfold vote_values.
      destruct ustate_cv, ustate_nv;simpl; clear.
      move => H_subset.
      rewrite !mem_undup.
      move/mapP => [x H_in H_v].
      apply/mapP. exists x;[|assumption].
      move: {H_v}x H_in.
      apply/subsetP.
      by assumption.
  }
  move => H_certval_nv.
  move: H_softvotes =>  [_ [b [H_b H_valid]]].

  refine (H_no_softvotes H_certval_nv b _ H_valid).
  apply/subsetP: {H_valid}b H_b.
  by apply (blocks_monotone H_reach H_lookup_cv H_lookup_nv).
Qed.

Lemma users_not_added g1 g2 (H_step:g1 ~~> g2) uid:
  g1.(users).[?uid] = None ->
  g2.(users).[?uid] = None.
Proof using.
  clear -H_step => H_u1.
  have H_notin1: (uid \notin g1.(users)) by rewrite -fndSome H_u1.
  destruct H_step;simpl users;
    try assumption;
    try (by rewrite fnd_set; case H_eq:(uid == uid0);
         [move/eqP in H_eq; subst; rewrite key_ustate in H_notin1; inversion H_notin1|]);
    try (by rewrite fnd_set; case H_eq:(uid == uid0);
         [move/eqP in H_eq; subst; rewrite ustate_key in H_notin1; inversion H_notin1|]).
  (* tick *)
  apply tick_users_notin; assumption.
Qed.

Lemma received_softvote
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start: state_before_round r0 g0)
      g (H_last: onth trace (size trace).-1 = Some g) :
  forall uid u,
    (global_state.users UserId UState [choiceType of Msg] g).[? uid] = Some u ->
  forall voter v r p,
    (voter, v) \in u.(softvotes) r p ->
    r0 <= r ->
    exists d, msg_received uid d (Softvote, val v, r, p, voter) trace.
Proof using.
  clear -H_path H_start H_last.
  move => uid u H_u voter v r p H_softvotes H_r.

  assert (~~match g0.(users).[? uid] with
            | Some u0 => (voter,v) \in u0.(softvotes) r p
            | None => false
            end). {
    destruct (g0.(users).[?uid]) as [u0|] eqn:H_u0;[|done].
    destruct H_start as [H_users _].
    have H_key0: uid \in g0.(users) by rewrite -fndSome H_u0.
    specialize (H_users _ H_key0).
    rewrite (in_fnd H_key0) in H_u0.
    case: H_u0 H_r H_users => ->.
    clear.
    move => H_r [_] [_] [_] [H_softvotes _].
    by move: {H_softvotes}(H_softvotes _ p H_r) => /nilP ->.
  }

  assert (H_path_copy := H_path).
  apply path_gsteps_onth with
      (P := upred uid (fun u => (voter, v) \in u.(softvotes) r p))
      (ix_p:=(size trace).-1) (g_p:=g)
    in H_path_copy;
    try eassumption; try (unfold upred; rewrite H_u; assumption).

  destruct H_path_copy as [n [g1 [g2 [H_step [H_pg1 H_pg2]]]]].
  unfold upred in *.
  assert (H_step_copy := H_step).
  apply transition_from_path with (g0:=g0) in H_step_copy; try assumption.
  destruct ((global_state.users UserId UState [choiceType of Msg] g2).[? uid]) eqn:H_u2;
    try (by inversion H_u2).
  destruct ((global_state.users UserId UState [choiceType of Msg] g1).[? uid]) eqn:H_u1.
  2: {
    eapply users_not_added in H_u1; try eassumption.
    rewrite H_u1 in H_u2; inversion H_u2.
  }
  assert (exists d ms, related_by (lbl_deliver uid d (Softvote, val v, r, p, voter) ms) g1 g2).

  have H_in1: (uid \in g1.(users)) by rewrite -fndSome H_u1.
  have H_in2: (uid \in g2.(users)) by rewrite -fndSome H_u2.
  have H_in1': g1.(users)[`H_in1] = u1 by rewrite in_fnd in H_u1;case:H_u1.

  destruct H_step_copy; simpl users; autounfold with gtransition_unfold in * |-;
    try (exfalso; rewrite H_u1 in H_u2; inversion H_u2; subst;
         rewrite H_pg2 in H_pg1; inversion H_pg1).

  (* tick *)
  + exfalso.
    rewrite updf_update in H_u2. inversion H_u2 as [H_adv].
    rewrite H_in1' /user_advance_timer in H_adv.
    revert H_adv.
    match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b end;
      intros; subst; rewrite H_pg2 in H_pg1; inversion H_pg1.
    assumption.

  (* deliver *)
  + clear H_step.
    rewrite fnd_set in H_u2. case H_eq:(uid == uid0). move/eqP in H_eq; subst uid0.
    2: {
      rewrite H_eq in H_u2.
      rewrite H_u1 in H_u2. inversion H_u2; subst.
      rewrite H_pg2 in H_pg1; inversion H_pg1.
    }
    rewrite eq_refl in H_u2. inversion H_u2.
    move:H2. rewrite ?(eq_getf _ H_in1) H_in1'.
    intro H_deliv.
    remember (pending.1,pending.2) as pending_res.
    assert (H_pending : pending = pending_res).
    destruct pending. subst pending_res. intuition.
    rewrite Heqpending_res in H_pending; clear Heqpending_res.
    remember (ustate_post,sent) as result eqn:H_result.
    destruct H_deliv eqn:H_dtrans;
    try (by case: H_result => [? ?]; destruct pre;
         subst; simpl in * |-; exfalso; rewrite H_pg2 in H_pg1; inversion H_pg1).

    (* deliver softvote *)
    * case: H_result => [? ?]; destruct pre.
      exists pending.1, [::], H_in1, ustate_post.
      simpl in * |- *.
      subst pre0.
      subst ustate_post. subst u0.
      unfold set_softvotes in H_pg2.
      simpl in H_pg2.
      revert H_pg2.
      match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b eqn:Hb1 end;
        try (by intro; rewrite H_pg2 in H_pg1; inversion H_pg1).
      match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b eqn:Hb2 end;
        try (by rewrite mem_undup; intro; rewrite H_pg2 in H_pg1; inversion H_pg1).

      intro.
      rewrite in_cons mem_undup in H_pg2.
      move/orP in H_pg2.
      destruct H_pg2 as [H_eqv | H_neqv];
        try (by rewrite H_neqv in H_pg1; inversion H_pg1).

      move/eqP in H_eqv. move/eqP in Hb1.
      case: H_eqv. case: Hb1.
      move => H_r_r1 H_p_p0 H_voter_i H_v_v0.
      subst r p voter v.

      split. assumption.
      rewrite in_fnd in H_u1; inversion H_u1. subst.
      split. assumption.

      exists msg_key. rewrite <- H_pending. split. assumption.
      trivial.

    (* set softvote *)
    * case: H_result => [? ?]; destruct pre.
      exists pending.1, [:: (Certvote, val v0, r1, p0, uid)], H_in1, ustate_post.
      simpl in * |- *.
      subst pre0.
      subst ustate_post. subst u0.
      unfold set_softvotes in H_pg2.
      simpl in H_pg2.
      revert H_pg2.
      match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b eqn:Hb1 end;
        try (by intro; rewrite H_pg2 in H_pg1; inversion H_pg1).
      match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b eqn:Hb2 end;
        try (by rewrite mem_undup; intro; rewrite H_pg2 in H_pg1; inversion H_pg1).

      intro.
      rewrite in_cons mem_undup in H_pg2.
      move/orP in H_pg2.
      destruct H_pg2 as [H_eqv | H_neqv];
        try (by rewrite H_neqv in H_pg1; inversion H_pg1).

      move/eqP in H_eqv. move/eqP in Hb1.
      case: H_eqv. case: Hb1.
      move => H_r_r1 H_p_p0 H_voter_i H_v_v0.
      subst r p voter v.

      split. assumption.
      rewrite in_fnd in H_u1; inversion H_u1; subst.
      split. assumption.

      exists msg_key. rewrite <- H_pending. split. assumption.
      trivial.

    (* deliver nonvote msg result *)
    * case: H_result => [? ?]; destruct pre; subst.
      unfold deliver_nonvote_msg_result in H_pg2.
      destruct msg.1.1.1.2 in H_pg2;
        try (rewrite H_pg2 in H_pg1; inversion H_pg1);
      destruct msg.1.1.1.1 in H_pg2;
        rewrite H_pg2 in H_pg1; inversion H_pg1.

  (* internal *)
  + clear H_step.
    rewrite fnd_set in H_u2. case H_eq:(uid == uid0). move/eqP in H_eq; subst uid0.
    2: {
      rewrite H_eq in H_u2.
      rewrite H_u1 in H_u2. inversion H_u2; subst.
      rewrite H_pg2 in H_pg1; inversion H_pg1.
    }
    rewrite eq_refl in H_u2. inversion H_u2.
    move:H1. rewrite ?(eq_getf _ H_in1) H_in1'.
    intro H_trans. remember (ustate_post,sent) as result eqn:H_result.
    destruct H_trans; case:H_result => [? ?]; subst; destruct pre;
    simpl in * |-; exfalso; rewrite H_pg2 in H_pg1; inversion H_pg1.

  (* corrupt *)
  + exfalso.
    rewrite fnd_set in H_u2; case H_eq:(uid == uid0).
    move/eqP in H_eq. subst uid0. rewrite eq_refl in H_u2.
    rewrite ?(eq_getf _ H_in1) H_in1' in H_u2.
    inversion H_u2; subst.
    rewrite H_pg2 in H_pg1; inversion H_pg1.

    rewrite H_eq in H_u2.
    rewrite H_u1 in H_u2. inversion H_u2; subst.
    rewrite H_pg2 in H_pg1; inversion H_pg1.

  destruct H0 as [d [ms H_rel]].
  exists d. unfold msg_received.
  exists n, ms. unfold step_at. exists g1, g2.
  split; assumption.
Qed.

Lemma received_nextvote_open
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start: state_before_round r0 g0):
  forall ix g, onth trace ix = Some g ->
  forall uid u,
    (global_state.users UserId UState [choiceType of Msg] g).[? uid] = Some u ->
  forall voter r p s,
    voter \in u.(nextvotes_open) r p s ->
    r0 <= r ->
    exists d, msg_received uid d (Nextvote_Open, step_val s, r, p, voter) trace.
Proof using.
  clear -H_path H_start.
  move => ix g H_g uid u H_u voter r p s H_voter H_r.
  set P := upred uid (fun u => voter \in u.(nextvotes_open) r p s).
  assert (~~P g0). {
  move: H_start => [H_users _]. clear -H_users H_r.
  subst P. unfold upred.
  destruct (uid \in g0.(users)) eqn: H_in.
  * move/(_ _ H_in) in H_users. rewrite in_fnd.
    move: {g0 H_in}(g0.(users)[` H_in]) H_users => u H_users.
    unfold user_before_round in H_users.
    decompose record H_users.
    by move: {H4 H_r}(H4 r p s H_r) => /nilP ->.
  * by rewrite not_fnd // H_in.
  }
  assert (P g). {
    unfold P, upred.
    rewrite H_u. assumption.
  }
  have := path_gsteps_onth H_path H_g H H0.
  clear -H_path.
  move => [n [g1 [g2 [H_step [H_pre H_post]]]]].
  have H_gtrans := transition_from_path H_path H_step.
  unfold msg_received, step_at.
  suff: exists d ms, related_by (lbl_deliver uid d (Nextvote_Open, step_val s, r, p, voter) ms) g1 g2
    by move => [d [ms H_rel]];exists d, n, ms, g1, g2;split;assumption.

  move: H_gtrans H_pre H_post;unfold P, upred;clear;destruct 1;
      try solve [move => /negP H_n /H_n []].
  { (* tick *)
  move => /negP H_n H_p. exfalso. move: H_n H_p. apply contrap.
  unfold tick_update, tick_users. cbn.
  destruct (uid \in pre.(users)) eqn:H_uid.
  * rewrite updf_update // in_fnd.
    move: (pre.(users)[` H_uid]) => u.
    by unfold user_advance_timer;destruct u, corrupt;simpl.
  * apply negbT in H_uid.
    rewrite [(updf _ _ _).[? uid]] not_fnd //.
    change (?k \in ?f) with (k \in domf f).
    rewrite -updf_domf. assumption.
  }
  { (* deliver *)
    rewrite fnd_set.
    destruct (uid == uid0) eqn:H_uids;[|by move/negP => H_n /H_n []].
    move => /eqP in H_uids. subst uid0.
    rewrite in_fnd.
    destruct pending as [d pmsg]. unfold snd in H1.

    remember (pre.(users)[`key_ustate]) as ustate;
    remember (ustate_post, sent) as result;
    destruct H1 eqn:H_step;case: Heqresult => {ustate_post}<- {sent}<-;subst pre0;
                                                try by move => /negP H_n H_p;exfalso.
    *
    unfold pre'.
    move => H_n H_p.
    assert ((r,p,s) = (r0,p0,s0)). {
    apply /eqP. apply/contraNT: H_n => /negbTE H_neq.
    move: H_p. unfold set_nextvotes_open;simpl. rewrite H_neq. done.
    } case: H2 => ? ? ?;subst r0 p0 s0.
    assert (i = voter). {
      symmetry. apply /eqP. apply/contraNT: H_n => /negbTE H_neq.
    rewrite /set_nextvotes_open /= eq_refl in H_p.

    match type of H_p with context C [if ?b then _ else _] => destruct b end.
      by rewrite mem_undup in H_p.
      by rewrite in_cons H_neq mem_undup in H_p.
    } subst i.
    by finish_case.
    *
    unfold pre'.
    move => H_n H_p.
    assert ((r,p,s) = (r0,p0,s0)). {
    apply /eqP. apply/contraNT: H_n => /negbTE H_neq.
    move: H_p. unfold set_nextvotes_open;simpl. rewrite H_neq. done.
    } case: H2 => ? ? ?;subst r0 p0 s0.
    assert (i = voter). {
      symmetry. apply /eqP. apply/contraNT: H_n => /negbTE H_neq.
    rewrite /set_nextvotes_open /= eq_refl in H_p.

    match type of H_p with context C [if ?b then _ else _] => destruct b end.
      by rewrite mem_undup in H_p.
      by rewrite in_cons H_neq mem_undup in H_p.
    } subst i.
    by finish_case.
    *
    move => /negP H_n H_p; exfalso;contradict H_n.
    move: (pre.(users)[`key_ustate]) H_p => u.
    clear.
    unfold deliver_nonvote_msg_result.
    destruct msg as [[[[m v] mr] mp] mu].
    simpl.
    by destruct v;first destruct m.
  }
  { (* internal *)
  move => /negP H_n H_p. exfalso. move: H_n H_p. apply contrap.
  rewrite fnd_set.
  destruct (uid == uid0) eqn:H_uids;[|done].
  move => /eqP in H_uids. subst uid0.
  rewrite in_fnd.
  move: (pre.(users)[` ustate_key]) H0 => u H_step.
  clear -H_step.
  remember (ustate_post,sent) as result;destruct H_step;
    case: Heqresult => <- _;by destruct pre.
  }
  { (* corrupt *)
  move => /negP H_n H_p. exfalso. move: H_n H_p. apply contrap.
  rewrite fnd_set.
  destruct (uid == uid0) eqn:H_uids;[|done].
  move => /eqP in H_uids. subst uid0.
  by rewrite in_fnd.
  }
Qed.

Lemma received_nextvote_val
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start: state_before_round r0 g0):
  forall ix g, onth trace ix = Some g ->
  forall uid u,
    (global_state.users UserId UState [choiceType of Msg] g).[? uid] = Some u ->
  forall voter v r p s,
    (voter, v) \in u.(nextvotes_val) r p s ->
    r0 <= r ->
    exists d, msg_received uid d (Nextvote_Val, next_val v s, r, p, voter) trace.
Proof using.
  clear -H_path H_start.
  move => ix g H_g uid u H_u voter v r p s H_voter H_r.
  set P := upred uid (fun u => (voter,v) \in u.(nextvotes_val) r p s).
  assert (~~P g0). {
  move: H_start => [H_users _]. clear -H_users H_r.
  subst P. unfold upred.
  destruct (uid \in g0.(users)) eqn: H_in.
  * move/(_ _ H_in) in H_users. rewrite in_fnd.
    move: {g0 H_in}(g0.(users)[` H_in]) H_users => u H_users.
    unfold user_before_round in H_users.
    decompose record H_users.
    by move: {H6 H_r}(H6 r p s H_r) => /nilP ->.
  * by rewrite not_fnd // H_in.
  }
  assert (P g). {
    unfold P, upred.
    rewrite H_u. assumption.
  }
  have := path_gsteps_onth H_path H_g H H0.
  clear -H_path.
  move => [n [g1 [g2 [H_step [H_pre H_post]]]]].
  have H_gtrans := transition_from_path H_path H_step.
  unfold msg_received, step_at.
  suff: exists d ms, related_by (lbl_deliver uid d (Nextvote_Val, next_val v s, r, p, voter) ms) g1 g2
    by move => [d [ms H_rel]];exists d, n, ms, g1, g2;split;assumption.

  move: H_gtrans H_pre H_post;unfold P, upred;clear;destruct 1;
      try solve [move => /negP H_n /H_n []].
  { (* tick *)
  move => /negP H_n H_p. exfalso. move: H_n H_p. apply contrap.
  unfold tick_update, tick_users. cbn.
  destruct (uid \in pre.(users)) eqn:H_uid.
  * rewrite updf_update // in_fnd.
    move: (pre.(users)[` H_uid]) => u.
    by unfold user_advance_timer;destruct u, corrupt;simpl.
  * apply negbT in H_uid.
    rewrite [(updf _ _ _).[? uid]] not_fnd //.
    change (?k \in ?f) with (k \in domf f).
    rewrite -updf_domf. assumption.
  }
  { (* deliver *)
    rewrite fnd_set.
    destruct (uid == uid0) eqn:H_uids;[|by move/negP => H_n /H_n []].
    move => /eqP in H_uids. subst uid0.
    rewrite in_fnd.
    destruct pending as [d pmsg]. unfold snd in H1.

    remember (pre.(users)[`key_ustate]) as ustate;
    remember (ustate_post, sent) as result;
    destruct H1 eqn:H_step;case: Heqresult => {ustate_post}<- {sent}<-;subst pre0;
                                                try by move => /negP H_n H_p;exfalso.
    *
    unfold pre'.
    move => H_n H_p.
    assert ((r,p,s) = (r0,p0,s0)). {
    apply /eqP. apply/contraNT: H_n => /negbTE H_neq.
    move: H_p. unfold set_nextvotes_val;simpl. rewrite H_neq. done.
    } case: H2 => ? ? ?;subst r0 p0 s0.
    assert ((voter,v) = (i,v0)). {
    apply /eqP. apply/contraNT: H_n => /negbTE H_neq.
    move: H_p. unfold set_nextvotes_val;simpl. rewrite eq_refl.
    match goal with
      [|- context C[(i, v0) \in ?nvs]] => destruct ((i,v0) \in nvs) eqn:H_in
    end.
      by rewrite H_in mem_undup.
      by rewrite H_in in_cons mem_undup; move/orP; destruct 1 as [H_eq|H_in'];
        [rewrite H_neq in H_eq; discriminate|].
    } case: H2 => ? ?;subst i v0.
    by finish_case.
    *
    unfold pre'.
    move => H_n H_p.
    assert ((r,p,s) = (r0,p0,s0)). {
    apply /eqP. apply/contraNT: H_n => /negbTE H_neq.
    move: H_p. unfold set_nextvotes_val;simpl. rewrite H_neq. done.
    } case: H2 => ? ? ?;subst r0 p0 s0.
    assert ((voter,v) = (i,v0)). {
    apply /eqP. apply/contraNT: H_n => /negbTE H_neq.
    move: H_p. unfold set_nextvotes_val;simpl. rewrite eq_refl.
    match goal with
      [|- context C[(i, v0) \in ?nvs]] => destruct ((i,v0) \in nvs) eqn:H_in
    end.
      by rewrite H_in mem_undup.
      by rewrite H_in in_cons mem_undup; move/orP; destruct 1 as [H_eq|H_in'];
        [rewrite H_neq in H_eq; discriminate|].
    } case: H2 => ? ?;subst i v0.
    by finish_case.
    *
    move => /negP H_n H_p; exfalso;contradict H_n.
    move: (pre.(users)[`key_ustate]) H_p => u.
    clear.
    unfold deliver_nonvote_msg_result.
    destruct msg as [[[[m v0] mr] mp] mu].
    simpl.
    by destruct v0;first destruct m.
  }
  { (* internal *)
  move => /negP H_n H_p. exfalso. move: H_n H_p. apply contrap.
  rewrite fnd_set.
  destruct (uid == uid0) eqn:H_uids;[|done].
  move => /eqP in H_uids. subst uid0.
  rewrite in_fnd.
  move: (pre.(users)[` ustate_key]) H0 => u H_step.
  clear -H_step.
  remember (ustate_post,sent) as result;destruct H_step;
    case: Heqresult => <- _;by destruct pre.
  }
  { (* corrupt *)
  move => /negP H_n H_p. exfalso. move: H_n H_p. apply contrap.
  rewrite fnd_set.
  destruct (uid == uid0) eqn:H_uids;[|done].
  move => /eqP in H_uids. subst uid0.
  by rewrite in_fnd.
  }
Qed.

  (*
    Suppose (voter,v) \in u.(softvotes) r p
    => message (Softvote, val v, r, p, i) was received
    => message (Softvote, val v, r, p, i) was sent:
      either
      - user i sent (Softvote, val v, r, p, i)
        (through an internal transition only)
        => softvoting preconditions imply i was a committee member
      - or adversary (using i) forged and sent the message
        => forging does the credentials check
      - or adversary replayed the message
        => the message is in msg_history
        => user i sent it (through an internal transition only)
        => softvoting preconditions imply i was a committee member
   *)

Lemma softvotes_sent
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start: state_before_round r0 g0):
  forall ix g, onth trace ix = Some g ->
  forall uid u, g.(users).[? uid] = Some u ->
  forall r, r0 <= r -> forall voter v p,
      (voter,v) \in u.(softvotes) r p ->
      honest_during_step (r,p,2) voter trace ->
      softvoted_in_path trace voter r p v.
Proof using.
  clear -H_path H_start.
  move => ix g H_onth uid u H_u r H_r voter v p H_voter H_honest.
  generalize dependent g. generalize dependent ix. generalize dependent voter.

  induction trace using last_ind;[discriminate|].

  move: (H_path).
  rename H_path into H_path_trans.
  destruct (rcons trace x) eqn:H_rcons.
  inversion H_path_trans.
  destruct H_path_trans as [H_g0 H_path_add]; subst g.
  rewrite <- H_rcons.

  move => H_path voter H_voter H_honest ix g H_onth H_u.
  destruct (ix == (size trace)) eqn:H_add.
  * { (* ix = size trace *)
  move/eqP in H_add. subst.
  have H_onth_copy := H_onth.
  unfold onth in H_onth_copy.
  rewrite drop_rcons // drop_size in H_onth_copy.
  case:H_onth_copy => H_x. subst x.

  have H_path_copy := H_path.
  eapply received_softvote in H_path;try eassumption;[|by rewrite size_rcons].

  destruct H_path as [d H_msg_rec].

  apply received_was_sent with (r0:=r0)
                               (u:=uid) (d:=d)
                               (msg:=(Softvote, val v, r, p, voter))
    in H_path_copy;[|assumption..].
  apply H_path_copy in H_r;[|assumption].
  destruct H_r as [ix0 [g1 [g2 [H_s_at H_sent]]]].
  exists ix0, g1, g2;split;assumption.
  }
  *
  move /eqP in H_add.
  have H_onth' := onth_size H_onth.
  rewrite size_rcons in H_onth'.
  assert (H_ix : ix < size trace) by (ppsimpl; lia; done).
  clear H_onth' H_add.

  assert (H_onth_trace : (onth trace ix) = Some g). {
  unfold onth; unfold onth in H_onth; rewrite drop_rcons in H_onth.
  apply drop_nth with (x0:=g0) in H_ix; rewrite H_ix in H_onth.
  rewrite H_ix. trivial.
  ppsimpl; lia.
  }

  assert (H_trace: is_trace g0 trace).
  destruct trace;[by inversion H_onth_trace|].
  inversion H_rcons; subst.
  unfold is_trace.
  split;[done|].
    by rewrite rcons_path in H_path_add; move/andP: H_path_add; intuition.

  eapply IHtrace in H_trace; try eassumption.
  destruct H_trace as [ix0 [g1 [g2 [H_s_at H_sent]]]].
  unfold softvoted_in_path, softvoted_in_path_at.
  exists ix0, g1, g2;split;[|assumption].
  by apply step_in_path_prefix with (size trace);rewrite take_rcons.
  by move: H_honest;rewrite /honest_during_step all_rcons => /andP [] _.
Qed.

Lemma user_sent_credential uid msg g1 g2:
  user_sent uid msg g1 g2 ->
  let:(r,p,s) := msg_step msg in uid \in committee r p s.
Proof using.
  move => [ms [H_in [[d [pending H_rel]]|H_rel]]];move: H_in;
            simpl in H_rel;decompose record H_rel.
  * { (* utransition deliver *)
    move: H. clear. move: {g1 x}(g1.(users)[`x]) => u.
    remember (x0,ms) as result.
    destruct 1;case:Heqresult => ? ?;subst x0 ms;move/Iter.In_mem => /= H_in;intuition;
    subst msg;simpl;
    apply/imfsetP;exists uid;[|reflexivity];apply/asboolP.
    unfold certvote_ok in H;decompose record H;assumption.
    }
  * { (* utransition internal *)
    move: H0. clear. move: {g1 x}(g1.(users)[`x]) => u.
    remember (x0,ms) as result.
    destruct 1;case:Heqresult => ? ?;subst x0 ms;move/Iter.In_mem => /= H_in;intuition;
    (subst msg;simpl;
     apply/imfsetP;exists uid;[|reflexivity];apply/asboolP);
    autounfold with utransition_unfold in * |-;
    match goal with [H:context C [comm_cred_step] |- _] => decompose record  H;assumption end.
    }
Qed.

Lemma user_forged_credential msg g1 g2:
  user_forged msg g1 g2 ->
  let:(r,p,s) := msg_step msg in msg_sender msg \in committee r p s.
Proof using.
  move: msg => [[[[mty v] r] p] sender] H_forged.
  simpl in H_forged;decompose record H_forged;clear H_forged;subst g2.
  move: (g1.(users)[`x]) H1 H0 => u. clear.
  destruct mty, v;simpl;(try solve[destruct 1]) => {x0}-> H_cred;
  (apply/imfsetP;exists sender;[|reflexivity];apply/asboolP;assumption).
Qed.

Lemma softvote_credentials_checked
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start: state_before_round r0 g0):
  forall ix g, onth trace ix = Some g ->
  forall uid u, g.(users).[? uid] = Some u ->
  forall r, r0 <= r -> forall v p,
    softvoters_for v u r p `<=` committee r p 2.
Proof.
  (* cleanup needed *)
  clear -lambda big_lambda L tau_s tau_c tau_b tau_v valid correct_hash H_path H_start.
  intros ix g H_onth uid u H_lookup r H_r v p.
  apply/fsubsetP => voter H_softvoters.

  have H_softvote : (voter,v) \in u.(softvotes) r p
    by move: H_softvoters;clear;move => /imfsetP [] [xu xv] /= /andP [H_in /eqP] -> ->.

  apply onth_take_some in H_onth.
  assert (H_ix : ix.+1 > 0) by intuition.
  have [d [n [ms H_deliver]]] :=
    received_softvote
      (is_trace_prefix H_path H_ix) H_start
      H_onth H_lookup
      H_softvote H_r.

  set msg := (Softvote,val v,r,p,voter).
  assert
    (exists send_ix g1 g2, step_in_path_at g1 g2 send_ix trace
                           /\ (user_sent voter msg g1 g2 \/ user_forged msg g1 g2))
    as H_source. {
    rewrite /step_at /= in H_deliver;decompose record H_deliver.
    assert (onth trace n = Some x)
      by (refine (onth_from_prefix (step_in_path_onth_pre _));eassumption).
    eapply pending_sent_or_forged;try eassumption.
  }

  destruct H_source as (send_ix & g1 & g2 & H_step & [H_send | H_forge]).
  apply user_sent_credential in H_send. assumption.
  apply user_forged_credential in H_forge. assumption.
Qed.

Lemma nextvote_open_credentials_checked
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start: state_before_round r0 g0):
  forall ix g, onth trace ix = Some g ->
  forall uid u, g.(users).[? uid] = Some u ->
  forall r, r0 <= r -> forall p s,
      nextvoters_open_for u r p s `<=` committee r p s.
Proof.
  clear -lambda big_lambda L tau_s tau_c tau_b tau_v valid correct_hash H_path H_start.
  intros ix g H_onth uid u H_lookup r H_r p s.
  apply/fsubsetP => voter H_nextvoters.

  have H_nextvote : voter \in u.(nextvotes_open) r p s
    by revert H_nextvoters; rewrite in_fset;
    change (in_mem voter _) with (voter \in u.(nextvotes_open) r p s).

  apply onth_take_some in H_onth.
  assert (H_ix : ix.+1 > 0) by intuition.
  have [d [n [ms H_deliver]]] :=
    received_nextvote_open
      (is_trace_prefix H_path H_ix) H_start
      H_onth H_lookup
      H_nextvote H_r.

  set msg := (Nextvote_Open,step_val s,r,p,voter).
  assert
    (exists send_ix g1 g2, step_in_path_at g1 g2 send_ix trace
                           /\ (user_sent voter msg g1 g2 \/ user_forged msg g1 g2))
    as H_source. {
    rewrite /step_at /= in H_deliver;decompose record H_deliver.
    assert (onth trace n = Some x)
      by (refine (onth_from_prefix (step_in_path_onth_pre _));eassumption).
    eapply pending_sent_or_forged;try eassumption.
  }

  destruct H_source as (send_ix & g1 & g2 & H_step & [H_send | H_forge]).
  apply user_sent_credential in H_send. assumption.
  apply user_forged_credential in H_forge. assumption.
Qed.

Lemma nextvote_val_credentials_checked
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start: state_before_round r0 g0):
  forall ix g, onth trace ix = Some g ->
  forall uid u, g.(users).[? uid] = Some u ->
  forall r, r0 <= r -> forall v p s,
      nextvoters_val_for v u r p s `<=` committee r p s.
Proof.
  clear -lambda big_lambda L tau_s tau_c tau_b tau_v valid correct_hash H_path H_start.
  intros ix g H_onth uid u H_lookup r H_r v p s.
  apply/fsubsetP => voter H_nextvoters.

  have H_nextvote : (voter,v) \in u.(nextvotes_val) r p s
    by move: H_nextvoters;clear;move => /imfsetP [] [xu xv] /= /andP [H_in /eqP] -> ->.

  apply onth_take_some in H_onth.
  assert (H_ix : ix.+1 > 0) by intuition.
  have [d [n [ms H_deliver]]] :=
    received_nextvote_val
      (is_trace_prefix H_path H_ix) H_start
      H_onth H_lookup
      H_nextvote H_r.

  set msg := (Nextvote_Val,next_val v s,r,p,voter).
  assert
    (exists send_ix g1 g2, step_in_path_at g1 g2 send_ix trace
                           /\ (user_sent voter msg g1 g2 \/ user_forged msg g1 g2))
    as H_source. {
    rewrite /step_at /= in H_deliver;decompose record H_deliver.
    assert (onth trace n = Some x)
      by (refine (onth_from_prefix (step_in_path_onth_pre _));eassumption).
    eapply pending_sent_or_forged;try eassumption.
  }

  destruct H_source as (send_ix & g1 & g2 & H_step & [H_send | H_forge]).
  apply user_sent_credential in H_send. assumption.
  apply user_forged_credential in H_forge. assumption.
Qed.

(* Priority:HIGH
   Top-level result,
   much of proof shared with certvote_excludes_nextvote_open_in_p
 *)
(* L3’: If an honest user cert-votes for a value in step 3, the user can only next-vote that value in the same period *)
Lemma certvote_nextvote_value_in_p
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start : state_before_round r0 g0) uid r p s v v':
  honest_during_step (r,p,s) uid trace ->
  r0 <= r ->
  certvoted_in_path trace uid r p v ->
  nextvoted_value_in_path trace r p s uid v' ->
  v = v'.
Proof using quorums_s_honest_overlap.
  clear -H_path H_start quorums_s_honest_overlap.
  move => H_honest H_r [ix_cv H_cv] [ix_nv H_nv].
  move: (H_cv) => [g1_cv [g2_cv [H_step_cv H_vote_cv]]].
  move: (H_nv) => [g1_nv [g2_nv [H_step_nv H_vote_nv]]].

  have H_g1_nv := step_in_path_onth_pre H_step_nv.
  have H_key1_nv := user_sent_in_pre H_vote_nv.
  set ustate_nv : UState := g1_nv.(users)[`H_key1_nv].
  have H_lookup_nv : _ = Some ustate_nv := in_fnd H_key1_nv.
  have H_nv_precond := nextvote_val_precondition H_vote_nv H_lookup_nv.

  have H_g2_cv := step_in_path_onth_post H_step_cv.
  have H_key2_cv := user_sent_in_post H_vote_cv.
  set ustate_cv : UState := g2_cv.(users)[`H_key2_cv].
  have H_lookup_cv : _ = Some ustate_cv := in_fnd H_key2_cv.
  have H_cv_cond := certvote_postcondition H_vote_cv H_lookup_cv.

  assert (ix_cv < ix_nv).
  {
  apply (order_ix_from_steps H_path (step_in_path_onth_pre H_step_cv) H_g1_nv
                             (key1:=user_sent_in_pre H_vote_cv) (key2:=user_sent_in_pre H_vote_nv)).
  rewrite (utransition_label_start H_vote_cv);[|by apply in_fnd].
  rewrite (utransition_label_start H_vote_nv);[|by apply in_fnd].

  destruct H_nv_precond as [H_nv_precond | H_nv_precond].
  move:H_nv_precond =>[b];clear;simpl;unfold nextvote_val_ok;tauto.
  (* stv case of nextvote_val_precondition *)
  right;split;[reflexivity|];right;split;[reflexivity|].
  case: H_nv_precond.
  clear.
  unfold nextvote_stv_ok.
  tauto.
  }

  have H_reach : greachable g2_cv g1_nv
    := steps_greachable H_path H H_step_cv H_step_nv.

  destruct H_cv_cond as [H_certval_cv [b' [H_blocks H_valid]]].

  assert (v \in certvals ustate_nv r p) as H_certval_v.
  {
    move: H_certval_cv.
    have H_weight_le := soft_weight_monotone H_reach H_lookup_cv H_lookup_nv v r p.
    have H_softvotes_le := softvotes_monotone H_reach H_lookup_cv H_lookup_nv r p.
    clear -H_weight_le H_softvotes_le.
    rewrite /certvals !mem_filter => /andP [H_weight H_votes].
    apply/andP. split. by apply (leq_trans H_weight).
    move:H_votes. rewrite /vote_values !mem_undup. move/mapP => [] x H_x ->.
    apply map_f. move: H_x.
    by apply/subsetP.
  }

  assert (tau_s <= soft_weight v ustate_nv r p) as H_v
      by (move:H_certval_v;rewrite mem_filter => /andP [] //).

  destruct H_nv_precond as [H_nv_precond_val | H_nv_precond_stv].

  * (* from nextvote val *)
  {
  have {H_nv_precond_val}H_certval_v' : v' \in certvals ustate_nv r p
    by move: H_nv_precond_val => [] b;unfold nextvote_val_ok;tauto.

  assert (tau_s <= soft_weight v' ustate_nv r p) as H_v'
      by (move: H_certval_v';rewrite mem_filter => /andP [] //).


  have H_votes_checked :=
    softvote_credentials_checked H_path H_start H_g1_nv H_lookup_nv H_r.

  have Hq := quorums_s_honest_overlap trace.
  specialize (Hq r p 2 _ _ (H_votes_checked _ _) H_v (H_votes_checked _ _) H_v').

  move: Hq => [softvoter [H_voted_v [H_voted_v' H_softvoter_honest]]].
  assert (softvoted_in_path trace softvoter r p v) as H_sent_v. {
  apply (softvotes_sent H_path H_start H_g1_nv H_lookup_nv H_r).
  move:H_voted_v => /imfsetP /= [] x /andP [H_x_in].
  unfold matchValue. destruct x. move => /eqP ? /= ?;subst.
  assumption.
  assumption.
  }
  assert (softvoted_in_path trace softvoter r p v') as H_sent_v'. {
  apply (softvotes_sent H_path H_start H_g1_nv H_lookup_nv H_r).
  move:H_voted_v' => /imfsetP /= [] x /andP [H_x_in].
  unfold matchValue. destruct x. move => /eqP ? /= ?;subst.
  assumption.
  assumption.
  }
  move: H_sent_v => [ix_v H_sent_v].
  move: H_sent_v' => [ix_v' H_sent_v'].

  by case:(no_two_softvotes_in_p H_path H_sent_v H_sent_v').
  }

  * {
  exfalso.
  (* stv case of nextvote_val_precondition *)
  destruct H_nv_precond_stv as [H_nv_stv _].
  destruct H_nv_stv as [H_time [H_rps [H_ccs [H_nv_step [H_not_valid [H_p H_no_quorum]]]]]].

  apply (H_not_valid _ H_certval_v b');[|assumption].
  by move: (blocks_monotone H_reach H_lookup_cv H_lookup_nv r) (b') H_blocks => /subsetP.
  }
Qed.

Definition period_advances uid r p (users1 users2: {fmap UserId -> UState}) : Prop :=
  {ukey_1: uid \in users1 &
  {ukey_2: uid \in users2 &
  let ustate1 := users1.[ukey_1] in
  let ustate2 := users2.[ukey_2] in
  ustate1.(round) = ustate2.(round)
  /\ step_lt (step_of_ustate ustate1) (r,p,0)
  /\ step_of_ustate ustate2 = (r,p,1)}}.

(* L5.0 A node enters period p > 0 only if it received t_H next-votes for
   the same value from some step s of period p-1 *)
Definition period_advance_at n path uid r p g1 g2 : Prop :=
  step_in_path_at g1 g2 n path /\ period_advances uid r p (g1.(users)) (g2.(users)).

Lemma set_nil : forall (T : finType), [set x in [::]] = @set0 T.
Proof. by move => T. Qed.

Lemma finseq_size : forall (T : finType) (s: seq T), #|s| = size (undup s).
Proof.
move=> T s.
rewrite -cardsE.
elim: s => //=; first by rewrite set_nil cards0.
move => x s IH.
rewrite set_cons /=.
case: ifP => //=.
  move => xs.
  suff Hsuff: x |: [set x0 in s] = [set x in s] by rewrite Hsuff.
  apply/setP => y.
  rewrite in_setU1.
  case Hxy: (y == x) => //.
  rewrite /= inE.
  by move/eqP: Hxy=>->.
move/negP/negP => Hx.
by rewrite cardsU1 /= inE Hx /= add1n IH.
Qed.


Lemma imfset_filter_size_lem (A B : choiceType) (f : A -> B) (sq : seq A) (P : A -> bool):
  #|` [fset x | x in [seq f x | x <- sq & P x]]| = #|` [fset f x | x in sq & P x]|.
Proof.
  clear -f sq P.
  rewrite Imfset.imfsetE !size_seq_fset.
  apply perm_eq_size, uniq_perm_eq;[apply undup_uniq..|].

  intro fx. rewrite !mem_undup map_id /= filter_undup mem_undup.
  apply Bool.eq_true_iff_eq;rewrite -!/(is_true _).
  by split;move/mapP => [x H_x ->];apply map_f;move:H_x;rewrite mem_undup.
Qed.

(* some collection of votes recorded in nv_open/val field *)
(* where certs check out and tau_b many of them *)
(* statement uses received_next_vote pred *)
(* only end up with vote recorded in your set if you actually receive it/it is sent *)
(* stop at in a nextvote collection *)

(* Priority:MED
   Structural lemma about advancement
 *)
Lemma period_advance_only_by_next_votes
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start: state_before_round r0 g0):
    forall n uid r p,
      r0 <= r ->
      (exists g1 g2, period_advance_at n trace uid r p g1 g2) ->
      let path_prefix := take n.+2 trace in
      exists (s:nat) (v:option Value) (next_voters:{fset UserId}),
        next_voters `<=` committee r p.-1 s
        /\ (tau_b <= #|` next_voters | \/ tau_v <= #|` next_voters |)
        /\ forall voter, voter \in next_voters ->
           received_next_vote uid voter r p.-1 s v path_prefix.
Proof.
  intros n uid r p H_r H_adv pref.
  destruct H_adv as [g1 [g2 [H_step [H_g1 [H_g2 [H_round [H_lt H_rps]]]]]]].
  assert (H_gtrans : g1 ~~> g2) by (eapply transition_from_path; eassumption).

  assert (H_lt_0 := H_lt).
  eapply step_lt_le_trans with (c:=(r,p,1)) in H_lt.
  2: { simpl; intuition. }

  destruct H_gtrans.

  (* tick *)
  exfalso.
  pose proof (tick_users_upd increment H_g1) as H_tick.
  rewrite in_fnd in H_tick.

  assert (H_tick_adv :
            (tick_users increment pre) [` H_g2] =
            user_advance_timer
              increment
              ((global_state.users UserId UState [choiceType of Msg] pre) [` H_g1])).
    by inversion H_tick; simpl; assumption.

  clear H_tick.
  unfold tick_update in H_rps.
  cbn -[in_mem mem] in H_rps.

  rewrite H_tick_adv in H_rps.
  unfold user_advance_timer in H_rps.
  destruct (local_state.corrupt UserId Value PropRecord Vote
                                ((global_state.users UserId UState [choiceType of Msg] pre)
                                   [` H_g1]));
    rewrite <- H_rps in H_lt; apply step_lt_irrefl in H_lt; assumption.

  { (* message delivery cases *)
    unfold delivery_result in H_rps.
    rewrite setfNK in H_rps.
    destruct (uid == uid0) eqn:H_uid.
    move/eqP in H_uid. subst.
    simpl in H_rps.
    assert (H_g1_key_ustate_opt :
              Some ((global_state.users UserId UState [choiceType of Msg] pre) [` H_g1]) =
              Some ((global_state.users UserId UState [choiceType of Msg] pre) [` key_ustate])).
      by repeat rewrite -in_fnd.

    inversion H_g1_key_ustate_opt as [H_g1_key_ustate]. clear H_g1_key_ustate_opt.
    rewrite H_g1_key_ustate in H_lt; rewrite <- H_rps in H_lt.
    rewrite H_g1_key_ustate in H_round.
    unfold step_of_ustate in H_lt.

    remember (ustate_post,sent) as ustep_out in H1.
    remember ((global_state.users UserId UState [choiceType of Msg] pre) [` key_ustate]) as u in H1.

    destruct H1; injection Hequstep_out; clear Hequstep_out; intros <- <-;
      try (inversion H_rps; exfalso; subst; subst pre';
           apply step_lt_irrefl in H_lt; contradiction).

    (* positive case: nextvote open *)
    {
      destruct H1 as [H_valid_rps H_quorum_size].
      rewrite H_g1_key_ustate in H_lt_0.
      clear H_g1_key_ustate H_g1.
      rename pre0 into u.
      rewrite -Hequ in H0 H_lt_0 H_lt H_round.
      cbn -[step_le step_lt] in * |-.

      destruct H_valid_rps as [H_r1 [H_p0 H_s]].
      case:H_rps => H_r' H_p.
      rewrite -H_p H_p0 -H_r' H_r1.

      assert (H_n : n.+2 > 0) by intuition.
      have H_pref := is_trace_prefix H_path H_n.
      apply step_in_path_onth_post in H_step.
      match goal with [_ : onth trace n.+1 = Some ?x |- _] => remember x as dr end.
      assert (H_onth : onth (take n.+2 trace) n.+1 = Some dr).
        subst pref.
        destruct (n.+2 < size trace) eqn:H_n2.
        apply onth_take_some in H_step. rewrite size_take in H_step.
        rewrite H_n2 in H_step. by intuition; eassumption.
        assert (size trace <= n.+2). by clear -H_n2; ppsimpl; lia.
        rewrite take_oversize; assumption.

      assert (H_addsub : (p0 + 1)%Nrec.-1 = p0). by clear; ppsimpl; lia.
      rewrite H_addsub.
      assert (H_r0r1 : r0 <= r1).
        by simpl in H_r1; rewrite H_r1 in H_r'; subst r; eassumption.

      exists s, None, (nextvoters_open_for pre' r1 p0 s); repeat split.
      eapply nextvote_open_credentials_checked with
          (uid:=uid) (u:=(adv_period_open_result pre'));
        try (subst pref; eassumption);
        try (subst dr; rewrite fnd_set; by rewrite eq_refl).

      left.
      unfold nextvoters_open_for.
      move: H_quorum_size.
      by rewrite card_fseq -finseq_size.

      intro voter.
      rewrite in_fset.
      change (in_mem voter _) with (voter \in pre'.(nextvotes_open) r1 p0 s).

      intro H_voter.
      eapply received_nextvote_open with (u:=(adv_period_open_result pre'));
        try (subst pref; eassumption);
        try (subst dr; rewrite fnd_set; by rewrite eq_refl).
    }

    (* positive case: nextvote val *)
    {
      destruct H1 as [H_valid_rps H_quorum_size].
      rewrite H_g1_key_ustate in H_lt_0.
      clear H_g1_key_ustate H_g1.
      rename pre0 into u.
      rewrite -Hequ in H0 H_lt_0 H_lt H_round.

      destruct H_valid_rps as [H_r1 [H_p0 H_s]].
      case:H_rps => H_r' H_p.
      rewrite -H_p H_p0 -H_r' H_r1.

      assert (H_n : n.+2 > 0) by intuition.
      have H_pref := is_trace_prefix H_path H_n.
      apply step_in_path_onth_post in H_step.
      match goal with [_ : onth trace n.+1 = Some ?x |- _] => remember x as dr end.
      assert (H_onth : onth (take n.+2 trace) n.+1 = Some dr).
        subst pref.
        destruct (n.+2 < size trace) eqn:H_n2.
        apply onth_take_some in H_step. rewrite size_take in H_step.
        rewrite H_n2 in H_step. by intuition; eassumption.
        assert (size trace <= n.+2). by clear -H_n2; ppsimpl; lia.
        rewrite take_oversize; assumption.

      assert (H_addsub : (p0 + 1)%Nrec.-1 = p0). by clear; ppsimpl; lia.
      rewrite H_addsub.
      assert (H_r0r1 : r0 <= r1).
        by simpl in H_r1; rewrite H_r1 in H_r'; subst r; eassumption.

      exists s, (Some v), (nextvoters_val_for v pre' r1 p0 s); repeat split.
      eapply nextvote_val_credentials_checked with
          (uid:=uid) (u:=(adv_period_val_result pre' v));
        try (subst pref; eassumption);
        try (subst dr; rewrite fnd_set; by rewrite eq_refl).

      right. move: H_quorum_size.
      unfold nextvote_value_quorum.
      rewrite finseq_size -card_fseq.
      match goal with |[|- is_true (tau_v <= ?A) -> is_true (tau_v <= ?B)]
                       => suff ->: A = B by[] end.
      by apply/imfset_filter_size_lem.

      intros voter H_voter.
      have H_nextvote : (voter,v) \in pre'.(nextvotes_val) r1 p0 s
        by move: H_voter;move=>/imfsetP [] [xu xv] /= /andP [H_in /eqP];intros->->.

      eapply received_nextvote_val with (u:=(adv_period_val_result pre' v));
        try (subst pref; eassumption);
        try (subst dr; rewrite fnd_set; by rewrite eq_refl).
    }

    exfalso.
    rewrite setfNK in H_round.
    assert (H_uid : (uid == uid) = true). apply/eqP; trivial.
    rewrite H_uid in H_round.

    subst pre0.
    inversion H_rps as [H_r0].
    cbn -[step_lt addn] in H_lt. rewrite H_r0 in H_lt.
    destruct H1 as [H_adv _]. unfold advancing_rp in H_adv.
    rewrite H_round in H_adv. clear -H_adv.
    by simpl in H_adv; ppsimpl; lia.

    exfalso. subst.
    unfold deliver_nonvote_msg_result in *.
    destruct pre.
    clear -H_rps H_lt.
    cbn -[step_lt] in * |- *.
    destruct msg.1.1.1.2; destruct msg.1.1.1.1;cbn -[step_lt] in H_lt;
    case:H_rps H_lt => -> -> ->;apply step_lt_irrefl.

    exfalso. rewrite <- H_rps in H_lt; apply step_lt_irrefl in H_lt; contradiction.
  }

  { (* internal step case *)
    exfalso.
    unfold step_result in H_rps.
    rewrite setfNK in H_rps.
    destruct (uid == uid0) eqn:Huid.
    move/eqP in Huid. subst.
    simpl in H_rps.
    assert (H_g1_key_ustate_opt :
              Some ((global_state.users UserId UState [choiceType of Msg] pre) [` H_g1]) =
              Some ((global_state.users UserId UState [choiceType of Msg] pre) [` ustate_key])).
      by repeat rewrite -in_fnd.

    inversion H_g1_key_ustate_opt as [H_g1_key_ustate]. clear H_g1_key_ustate_opt.
    rewrite H_g1_key_ustate in H_lt; rewrite <- H_rps in H_lt.
    unfold step_of_ustate in H_lt.

    remember (ustate_post,sent) as ustep_out in H0.
    remember ((global_state.users UserId UState [choiceType of Msg] pre) [` ustate_key]) as u in H0.

    destruct H0; injection Hequstep_out; clear Hequstep_out; intros <- <-; inversion H_rps;
      try (destruct H0 as [H_lam [H_vrps [H_ccs [H_s [H_rest]]]]];
           clear -H4 H_s; by ppsimpl; lia).

    subst; try apply step_lt_irrefl in H_lt; try contradiction.

    destruct H0 as [H_nv_stv H_stv].
    destruct H_nv_stv as [H_lam [H_vrps [H_ccs [H_s [H_rest]]]]].
    clear -H4 H_s. by ppsimpl; lia.

    (* no nextvote ok - need s > 3 assumption? *)
    move:H_lt_0;rewrite H_g1_key_ustate -Hequ /step_of_ustate H2 H3.
    clear;move: (pre0.(step)) => s /step_ltP /=.
    by rewrite !eq_refl !ltnn ltn0.

    subst. simpl in H_lt.
    simpl in H_rps.
    inversion H_rps. rewrite -> H2 in H_lt. rewrite -> H3 in H_lt. rewrite -> H4 in H_lt. intuition;rewrite ltnn in H6;intuition.
    (*
    unfold certvote_timeout_ok in H0.
    inversion H0; subst.
    clear -H4 H1. rewrite H1 in H4. inversion H4.

    rewrite <- H_rps in H_lt; apply step_lt_irrefl in H_lt; contradiction.
    *)
  }

  (* recover from partition *)
  exfalso.
  simpl in H_g2.
  assert (H_g1_g2_opt :
          Some ((global_state.users UserId UState [choiceType of Msg] pre) [` H_g1]) =
          Some ((global_state.users UserId UState [choiceType of Msg] pre) [` H_g2])).
    by repeat rewrite -in_fnd.

  inversion H_g1_g2_opt as [H_g1_g2]; clear H_g1_g2_opt.
  rewrite H_g1_g2 in H_lt.
  rewrite <- H_rps in H_lt; apply step_lt_irrefl in H_lt; assumption.

  (* enter partition *)
  exfalso.
  simpl in H_g2.
  assert (H_g1_g2_opt :
          Some ((global_state.users UserId UState [choiceType of Msg] pre) [` H_g1]) =
          Some ((global_state.users UserId UState [choiceType of Msg] pre) [` H_g2])).
    by repeat rewrite -in_fnd.

  inversion H_g1_g2_opt as [H_g1_g2]; clear H_g1_g2_opt.
  rewrite H_g1_g2 in H_lt.
  rewrite <- H_rps in H_lt; apply step_lt_irrefl in H_lt; assumption.

  (* corrupt user *)
  exfalso.

  rewrite setfNK in H_rps.
  destruct (uid == uid0) eqn:Huid.
  move/eqP in Huid. subst.
  simpl in H_rps.
  assert (H_g1_ustate_key_opt :
            Some ((global_state.users UserId UState [choiceType of Msg] pre) [` H_g1]) =
            Some ((global_state.users UserId UState [choiceType of Msg] pre) [` ustate_key])).
    by repeat rewrite -in_fnd.

  inversion H_g1_ustate_key_opt as [H_g1_ustate_key]; clear H_g1_ustate_key_opt.
  rewrite H_g1_ustate_key in H_lt.
  rewrite <- H_rps in H_lt; apply step_lt_irrefl in H_lt; assumption.

  rewrite <- H_rps in H_lt; apply step_lt_irrefl in H_lt; assumption.

  (* replay message *)
  exfalso.
  simpl in H_g2.
  assert (H_g1_g2_opt :
          Some ((global_state.users UserId UState [choiceType of Msg] pre) [` H_g1]) =
          Some ((global_state.users UserId UState [choiceType of Msg] pre) [` H_g2])).
    by repeat rewrite -in_fnd.
  inversion H_g1_g2_opt as [H_g1_g2]; clear H_g1_g2_opt.
  rewrite H_g1_g2 in H_lt.
  rewrite <- H_rps in H_lt; apply step_lt_irrefl in H_lt; assumption.

  (* forge message *)
  exfalso.
  simpl in H_g2.
  assert (H_g1_g2_opt :
          Some ((global_state.users UserId UState [choiceType of Msg] pre) [` H_g1]) =
          Some ((global_state.users UserId UState [choiceType of Msg] pre) [` H_g2])).
    by repeat rewrite -in_fnd.
  inversion H_g1_g2_opt as [H_g1_g2]; clear H_g1_g2_opt.
  rewrite H_g1_g2 in H_lt.
  rewrite <- H_rps in H_lt; apply step_lt_irrefl in H_lt; assumption.
Qed.

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

Lemma honest_in_period_entered
      g0 trace (H_path : is_trace g0 trace)
      r (H_start: state_before_round r g0):
  forall p uid, honest_in_period r p uid trace ->
  1 < p ->
  exists n g1 g2, period_advance_at n trace uid r p g1 g2.
Proof using.
  clear -H_path H_start.
  move => p uid [ix H_in_period] H_p_gt.
  destruct (onth trace ix) as [g|] eqn:H_g;[|exfalso;assumption].
  destruct (g.(users).[?uid]) as [u|] eqn:H_u;[|exfalso;assumption].
  move: H_in_period => [H_honest [H_r H_p]].
  set P := upred uid (fun u => (u.(round) == r) && (u.(period) == p)).
  have H_Pg : P g by rewrite /P /upred H_u H_r H_p !eq_refl.
  have H_NPg0  : ~~ P g0.
  {
  rewrite /P /upred.
  destruct (g0.(users).[?uid]) as [u0|] eqn:H_u0;[|exact].
  apply/negP => /andP [/eqP H_r0 /eqP H_p0].
  move: H_start => [H_users_before _].
  unfold users_before_round in H_users_before.
  have H_in_u0: uid \in g0.(users) by rewrite -fndSome H_u0.
  specialize (H_users_before _ H_in_u0).
  rewrite in_fnd in H_u0. case: H_u0 H_users_before => -> [H_u0_step _].
  case: H_u0_step => [| [] _ [] _ [] H_p' _];[by rewrite H_r0 ltnn|].
  by move: H_p_gt;rewrite -H_p0 H_p' ltnn.
  }
  have {H_Pg H_NPg0}[n [g1 [g2 [H_step H_change]]]]
    := path_gsteps_onth H_path H_g H_NPg0 H_Pg.
  exists n,g1,g2;split;[assumption|].

  apply (transition_from_path H_path) in H_step.
  have H_in2 : uid \in g2.(users)
    by move: H_change => [] _;unfold P, upred;
       destruct g2.(users).[?uid] eqn:H_u2 => H_P2;[rewrite -fndSome H_u2|].
  have H_in1 : uid \in g1.(users)
    by rewrite /in_mem /= /pred_of_finmap (gtrans_preserves_users H_step).
  clear -H_step H_change H_in1 H_in2 H_p_gt.
  destruct (H_step);try by exfalso;move: H_change => [] /negP.
  * (* tick *)
    exfalso. move: H_change => [] /negP.
    autounfold with gtransition_unfold;unfold P, upred.
    rewrite updf_update // (in_fnd H_in1).
    move:(pre.(users)[`H_in1]) => u;destruct u,corrupt;exact.
  * (* deliver *)
    {
    move: H_change => [] /negP.
    rewrite {1}/delivery_result /P /upred fnd_set.
    destruct (uid == uid0) eqn:H_eq;
      [move/eqP in H_eq;subst uid0
      |by move => A {A}/A].
    rewrite (in_fnd key_ustate).
    remember (pre.(users)[` key_ustate] : UState) as u.
    move => H_pre /andP [/eqP H_r /eqP H_p].
    exists key_ustate, H_in2.
    rewrite <- Hequ.
    intros ustate1 ustate2; subst ustate1 ustate2.
    rewrite getf_set.

    assert (step_lt (step_of_ustate u) (r,p,0)) as H_step_lt.
    {
      have {H_step}H_after : ustate_after u ustate_post by
        apply (gtr_rps_non_decreasing H_step (uid:=uid));
      [rewrite Hequ;apply in_fnd
      |rewrite fnd_set eq_refl].
      apply ustate_after_iff_step_le in H_after.
      case:H_after =>[|[a b]];[by rewrite H_r;left|].
      right;split;[by rewrite a|left].
      case:b=>[|[b _]];[by rewrite H_p|exfalso].
      apply H_pre;rewrite a b H_r H_p !eq_refl;done.
    }
    suff: u.(round)=ustate_post.(round) /\ step_of_ustate ustate_post = (r,p,1) by tauto.
    remember (ustate_post,sent) as result;destruct H1;
      case:Heqresult => ? ?;subst ustate_post sent;
        try (destruct H_pre;by rewrite H_r H_p !eq_refl).
    + (* adv_period_open_result *)
      by move: H_p H_r;simpl => -> ->;clear;split;reflexivity.
    + (* adv_period_val_result *)
      by move: H_p H_r;simpl => -> ->;clear;split;reflexivity.
    + (* certify result *)
      by rewrite -H_p ltnn in H_p_gt.
    + {
        destruct H_pre;rewrite -H_r -H_p /deliver_nonvote_msg_result.
        clear.
        by repeat match goal with
                |[|- context X [match ?x with _ => _ end]] => destruct x
               end;rewrite !eq_refl.
      }
    }
  * (* internal *)
    {
      move: H_change => [] /negP.
      rewrite {1}/step_result /P /upred fnd_set.
      destruct (uid == uid0) eqn:H_eq;
        [move/eqP in H_eq;subst uid0
        |by move => A {A}/A].
      rewrite (in_fnd ustate_key).
      remember (pre.(users)[` ustate_key] : UState) as u.
      move => H_pre /andP [/eqP H_r /eqP H_p].
      exists ustate_key, H_in2.
      rewrite <- Hequ.
      intros ustate1 ustate2; subst ustate1 ustate2.
      rewrite getf_set.

      assert (step_lt (step_of_ustate u) (r,p,0)) as H_step_lt.
      {
        have {H_step}H_after : ustate_after u ustate_post by
        apply (gtr_rps_non_decreasing H_step (uid:=uid));
          [rewrite Hequ;apply in_fnd
          |rewrite fnd_set eq_refl].
        apply ustate_after_iff_step_le in H_after.
        case:H_after =>[|[a b]];[by rewrite H_r;left|].
        right;split;[by rewrite a|left].
        case:b=>[|[b _]];[by rewrite H_p|exfalso].
        apply H_pre;rewrite a b H_r H_p !eq_refl;done.
      }
      suff: u.(round)=ustate_post.(round) /\ step_of_ustate ustate_post = (r,p,1) by tauto.
      remember (ustate_post,sent) as result;destruct H0;
      case:Heqresult => ? ?;subst ustate_post sent;
           try (destruct H_pre;by rewrite H_r H_p !eq_refl).
    }
  * (* corrupt *)
    exfalso. move: H_change => [] /negP.
    unfold corrupt_user_result, P, upred.
    rewrite fnd_set.
    destruct (uid==uid0) eqn:H_eq;[|by apply].
    move /eqP in H_eq;subst uid0.
    by rewrite (in_fnd ustate_key).
Qed.


(* L5 An honest node can enter period p'>1 only if at least one
      honest node participated in period p'-1 *)
(* Note that we freeze the state of corrupt users,
   so any user whose period actually advanced must have been
   honest at the time *)
Lemma adv_period_from_honest_in_prev g0 trace (H_path: is_trace g0 trace)
  r0 (H_start: state_before_round r0 g0):
  forall n uid r p,
    p > 0 ->
    r0 <= r ->
    (exists g1 g2, period_advance_at n trace uid r p g1 g2) ->
    exists uid', honest_in_period r (p.-1) uid' trace.
Proof.
  intros n uid r p.
  intros H_p H_r H_adv.
  eapply period_advance_only_by_next_votes in H_adv;[|eassumption..].
  destruct H_adv as (s & v & next_voters & H_voters_cred & H_voters_size & ?).
  assert (H_n : n.+2 > 0) by intuition.
  pose proof (is_trace_prefix H_path H_n) as H_path_prefix.
  assert (exists honest_voter, honest_voter \in next_voters /\ honest_during_step (r,p.-1,s) honest_voter (take n.+2 trace)) as (uid_honest & H_honest_voter & H_honest)
      by (destruct H_voters_size;[eapply quorum_b_has_honest|eapply quorum_v_has_honest];eassumption).
  clear H_voters_size.
  exists uid_honest.
  specialize (H uid_honest H_honest_voter).
  unfold received_next_vote in H.
  set msg_bit:= (match v with | Some v => (Nextvote_Val, next_val v s)
               | None => (Nextvote_Open, step_val s)
       end) in H.
  destruct H as [d H].
  pose proof (received_was_sent H_path_prefix H_start H) as H1.
  rewrite {1}[msg_bit]surjective_pairing in H1.
  specialize (H1 H_r).
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
  apply (user_honest_from_during H_path_prefix H_onth (H_in:=H_user_in)).
  rewrite H_start_label.
  revert H_honest.
  apply honest_during_le .
  destruct v;apply step_le_refl.
  }
  {
    move: (g1.(users)[`H_user_in]) H_start_label => u. clear.
    by destruct u, v;case.
  }
Qed.

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

Lemma stv_utransition_internal:
  forall uid pre post msgs, uid # pre ~> (post, msgs) ->
  pre.(round) = post.(round) ->
  pre.(period) = post.(period) ->
  forall p, pre.(stv) p = post.(stv) p.
Proof using.
  move => uid pre post msgs step.
  remember (post,msgs) as result eqn:H_result;
  destruct step;case:H_result => [? ?];subst;done.
Qed.

Lemma stv_utransition_deliver:
  forall uid pre post m msgs, uid # pre ; m ~> (post, msgs) ->
  pre.(round) = post.(round) ->
  pre.(period) = post.(period) ->
  forall p, pre.(stv) p = post.(stv) p.
Proof using.
  move => uid pre post m msgs step H_round H_period.
  remember (post,msgs) as result eqn:H_result;
  destruct step;case:H_result => [? ?];subst;
    try by (destruct pre;simpl;autounfold with utransition_unfold;done).
  * {
      exfalso;move: H_period;clear;destruct pre;simpl;clear.
      rewrite -[period in period = _]addn0. move/addnI. done.
    }
  * {
      exfalso;move: H_period;clear;destruct pre;simpl;clear.
      rewrite -[period in period = _]addn0. move/addnI. done.
    }
  * { exfalso;unfold certify_ok in H;decompose record H;clear H.
      move:H0. rewrite /advancing_rp H_round;clear;simpl.
      by case =>[|[]];[rewrite ltnNge leq_addr
                      |rewrite -[r in _ = r]addn0;move/addnI].
    }
  * { clear.
      unfold deliver_nonvote_msg_result.
      destruct msg as [[[[]]]]. simpl.
      by destruct e;[destruct m|..].
    }
Qed.

Lemma stv_gtransition g1 g2 (H_step:g1 ~~> g2) uid:
  forall u1, g1.(users).[?uid] = Some u1 ->
  exists u2, g2.(users).[?uid] = Some u2
  /\  (u1.(round)  = u2.(round)  ->
       u1.(period) = u2.(period) ->
       forall p, u1.(stv) p = u2.(stv) p).
Proof using.
  clear -H_step => u1 H_u1.
  have H_in1: (uid \in g1.(users)) by rewrite -fndSome H_u1.
  have H_in1': g1.(users)[`H_in1] = u1 by rewrite in_fnd in H_u1;case:H_u1.
  destruct H_step;simpl users;autounfold with gtransition_unfold;
    try (rewrite fnd_set;case H_eq:(uid == uid0);
      [move/eqP in H_eq;subst uid0|]);
    try (eexists;split;[eassumption|done]);
    first rewrite updf_update //;
    (eexists;split;[reflexivity|]).
  * (* tick *)
    rewrite H_in1' /user_advance_timer.
    by match goal with [ |- context C[ match ?b with _ => _ end]] => destruct b end.
  * (* deliver *)
    move:H1. rewrite ?(eq_getf _ H_in1) H_in1'. apply stv_utransition_deliver.
  * (* internal *)
    move:H0. rewrite ?(eq_getf _ H_in1) H_in1'. apply stv_utransition_internal.
  * (* corrupt *)
    rewrite ?(eq_getf _ H_in1) H_in1'. done.
Qed.

Lemma stv_forward
      g1 g2 (H_reach : greachable g1 g2)
      uid u1 u2:
  g1.(users).[?uid] = Some u1 ->
  g2.(users).[?uid] = Some u2 ->
  u1.(round) = u2.(round) ->
  u1.(period) = u2.(period) ->
  forall p, u1.(stv) p = u2.(stv) p.
Proof using.
  clear -H_reach.
  move => H_u1 H_u2 H_r H_p.
  destruct H_reach as [trace H_path H_last].

  destruct trace. inversion H_path.
  destruct H_path as [H_g0 H_path]. subst g.

  move: g1 H_path H_last u1 H_u1 H_r H_p.
  induction trace.
  * simpl. by move => g1 _ <- u1;rewrite H_u2{H_u2};case => ->.
  * cbn [path last] => g1 /andP [/asboolP H_step H_path] H_last u1 H_u1 H_r H_p p.

    assert (H_reach : greachable a g2).
      by eapply ex_intro2 with (a::trace); unfold is_trace.

    specialize (IHtrace a H_path H_last).
    have [umid [H_umid H_sub]] := stv_gtransition H_step H_u1.
    specialize (IHtrace umid H_umid).
    have H_le_u1_umid := gtr_rps_non_decreasing H_step H_u1 H_umid.
    have H_le_umid_u2 := greachable_rps_non_decreasing H_reach H_umid H_u2.
    have H_r': u1.(round) = umid.(round). {
      move: H_r H_p H_le_u1_umid H_le_umid_u2.
      unfold ustate_after. destruct u1,umid,u2;simpl;clear;intros;subst.
      intuition. have := ltn_trans H H0. by rewrite ltnn.
    }
    have H_p': u1.(period) = umid.(period). {
      move: H_r H_p H_le_u1_umid H_le_umid_u2.
      unfold ustate_after. destruct u1,umid,u2;simpl;clear;intros;subst.
      intuition. have := ltn_trans H H0. by rewrite ltnn.
      subst. by rewrite ltnn in H.
      subst. by rewrite ltnn in H0.
      have := ltn_trans H2 H3. by rewrite ltnn.
    }
    specialize (H_sub H_r' H_p').
    rewrite H_sub. clear H_sub.
    apply IHtrace;congruence.
Qed.

Definition round_advance_at n path uid r g1 g2 : Prop :=
  step_in_path_at g1 g2 n path /\
  {ukey_1: uid \in g1.(users) &
  {ukey_2: uid \in g2.(users) &
  let ustate1 := g1.(users).[ukey_1] in
  let ustate2 := g2.(users).[ukey_2] in
  step_lt (step_of_ustate ustate1) (r,1,1)
  /\ step_of_ustate ustate2 = (r,1,1)}}.

Lemma honest_softvote_respects_excl_stv:
  forall p, 1 < p ->
  forall u r,
    (forall s, ~nextvote_bottom_quorum u r p.-1 s) ->
  forall g1 uid,
    g1.(users).[?uid] = Some u ->
  forall v,
    u.(stv) p = Some v ->
  forall v' g2,
    user_sent uid (Softvote, val v', r, p, uid) g1 g2 ->
  v' = v.
Proof.
  move => p H_p u r H_excl g1 uid H_u v H_stv v' g2 H_sent.
  move: H_sent => [ms [H_msg [[d [pending H_deliver]]|H_internal]]].
  *
    move: H_deliver => [key1 [upost]] /=.
    have H_u_key: (g1.(users))[`key1] = u by rewrite in_fnd in H_u;case:H_u.
    rewrite !H_u_key.
    move => [H_step [H_honest _]].
    contradict H_msg => /Iter.In_mem.
    move: H_step;clear.
    by inversion 1;simpl;intuition.
  *
    move: H_internal => [key1 [upost]] /=.
    have H_u_key: (g1.(users))[`key1] = u by rewrite in_fnd in H_u;case:H_u.
    rewrite !H_u_key.
    move => [H_honest [H_step {g2}_]].

    inversion H_step;subst pre uid0 upost ms;clear H_step;try done;
      move:H_msg;rewrite mem_seq1 => /eqP [Hv Hr Hp];subst v0 r0 p0.
    +
    unfold softvote_new_ok in H2;decompose record H2;clear H2.
    contradict H3.
    unfold cert_may_exist.
    move:H1 => [H_r [H_u_p H_s]].
    by rewrite H_u_p H_r subn1.

    +
    unfold softvote_repr_ok in H2;decompose record H2;clear H2.
    move: H5 => [[H_cert H_asdfd1]|[H_cert H_stv0]].
     - contradict H_cert;unfold cert_may_exist.
         by move:H1 => [H_r [H_u_p H_s]];rewrite H_r H_u_p subn1;split.
     - by move:H_stv;rewrite H_stv0;clear;case.
Qed.

Lemma user_sent_honest_pre uid mty v r p g1 g2
      (H_send: user_sent uid (mty,v,r,p,uid) g1 g2):
      (g1.(users)[` user_sent_in_pre H_send]).(corrupt) = false.
Proof.
  set H_in := user_sent_in_pre H_send.
  clearbody H_in.
  move:H_send => [ms [H_in_ms [[d [inc H_ustep]]|H_ustep]]];
      simpl in H_ustep;decompose record H_ustep;clear H_ustep.
  apply/negP;contradict H0;move: H0.
    by rewrite (bool_irrelevance H_in x).
  apply/negP;contradict H;move: H.
    by rewrite (bool_irrelevance H_in x).
Qed.

Lemma user_sent_honest_post uid mty v r p g1 g2
      (H_send: user_sent uid (mty,v,r,p,uid) g1 g2):
      (g2.(users)[` user_sent_in_post H_send]).(corrupt) = false.
Proof.
  set H_in := user_sent_in_post H_send.
  clearbody H_in.
  suff: user_honest uid g2 by rewrite /user_honest in_fnd => /negbTE.
  move:H_send => [ms [H_in_ms [[d [inc H_ustep]]|H_ustep]]];
      simpl in H_ustep;decompose record H_ustep;clear H_ustep;subst g2.
  *
    unfold user_honest, delivery_result;simpl.
    rewrite fnd_set eq_refl.
    move: H H0. clear. admit.
  *
    unfold user_honest, step_result;simpl.
    rewrite fnd_set eq_refl.
    move: H0 H. clear. admit.
Admitted.

Lemma user_honest_in_from_send uid mty v r p ix trace
      (H_vote: user_sent_at ix trace uid (mty,v,r,p,uid)):
   honest_in_period r p uid trace.
Proof.
  (* move => g0 trace H_path r p v H_p H_excl uid v' H_honest H_vote. *)
  destruct H_vote as (g1_v & g2_v & H_vote_step & H_vote_send).

  set H_in: uid \in g1_v.(users) := user_sent_in_pre H_vote_send.
  have H_u := in_fnd H_in.
  set u := (g1_v.(users)[` H_in]) in H_u.

  exists ix.
  rewrite (step_in_path_onth_pre H_vote_step) H_u.
  split.
    by apply/negP;rewrite (user_sent_honest_pre H_vote_send).
    by move:(utransition_label_start H_vote_send H_u) => /=[-> [-> _]].
Qed.

(* L6: if all honest nodes that entered a period p >= 2 did so exclusively for value v *)
(* then an honest node cannot cert-vote for any value other than v in step 3 of period p'. *)
Lemma excl_enter_limits_cert_vote :
  forall g0 trace (H_path: is_trace g0 trace),
  forall p, 1 < p ->
  forall r v,
  (forall (uid : UserId),
    honest_in_period r p uid trace ->
    enters_exclusively_for_value uid r p v trace) ->
  forall uid v',
    honest_during_step (r,p,3) uid trace ->
    certvoted_in_path trace uid r p v' -> v' = v.
Proof using.
  clear.
  move => g0 trace H_path p H_p r v H_excl uid v' H_honest H_vote.
  destruct H_vote as [ix_vote H_vote].

  have H_honest_in:= user_honest_in_from_send H_vote.

  unfold certvoted_in_path_at in H_vote.
  destruct H_vote as (g1_v & g2_v & H_vote_step & H_vote_send).

  set H_in: uid \in g1_v.(users) := user_sent_in_pre H_vote_send.
  have H_u := in_fnd H_in.
  set u := (g1_v.(users)[` H_in]) in H_u.

  destruct (H_excl _ H_honest_in) as (g1 & g2 & ix_enter & H_enter & ustate_enter &
                      H_lookup_enter & H_honest_enter & H_stv & H_not_open).
  move:H_enter => [H_enter_step H_enter].

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
      move: H_enter => [ekey1 [ekey2 [H_round [H_pre H_rps]]]].
      pose proof (utransition_label_start H_vote_send (in_fnd ekey1)).
      move:H_pre; rewrite H /msg_step /step_lt; clear.
      rewrite !ltnn.
      by intuition.
    * move: H_enter => [ukey_1 [ukey_2 [H_round [H_enter_lt H_enter_eq]]]].
      set ustate1: UState := g1.(users)[`ukey_1] in H_enter_lt.
      set ustate2: UState := g2.(users)[`ukey_2] in H_enter_eq.
      move: H_lt. apply/negP. rewrite -leqNgt.
      clear ukey_2 H_round ustate2 H_enter_eq.
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

  assert ((g1_v.(users)[`H_in]).(stv) p = Some v) as H_stv_send.
  {
  move: H_enter => [ukey_1 [ukey_2 [H_round [H_pre H_step_g2]]]].

  have := stv_forward H_reach H_lookup_enter (in_fnd H_in).

  have H_start := utransition_label_start H_vote_send (in_fnd H_in).
  case:H_start => -> -> _.
  rewrite (in_fnd ukey_2) in H_lookup_enter.
  case: H_lookup_enter => H_lookup_enter.
  rewrite H_lookup_enter in H_step_g2.
  case:H_step_g2 => -> -> _.
  by move => <-.
  }

  (* analyze uid's precondition for the certvote step *)
  assert (H_honest_send: user_honest uid g1_v).
  {
    rewrite -[(r,p,3)](utransition_label_start H_vote_send (in_fnd H_in)) in H_honest.
    exact (user_honest_from_during H_path (step_in_path_onth_pre H_vote_step) H_honest).
  }

  have honest_softvotes_only_for_v:
    forall ix uid_sv v', user_sent_at ix trace uid_sv (Softvote,val v',r,p,uid_sv) -> v' = v. {
    move => ix uid_sv v0 H_softvote_send.
    have H_honest_sv := (user_honest_in_from_send H_softvote_send).
    have := H_excl _ H_honest_sv.
    clear ix_enter H_enter_step H_order.
    move => [g1_enter [g2_enter [ix_enter [H_adv [u_sv_entry
            [H_u_sv_entry [H_uv_entry_honest [H_uv_entry_stv H_uv_entry_no_botq]]]]]]]].
    clear g1 g2 H_lookup_enter H_enter H_reach.
    move: H_softvote_send => [g1 [g2 [H_step H_send]]].
    have H_u_sv := in_fnd (user_sent_in_pre H_send).
    set u_sv := g1.(users) [`user_sent_in_pre H_send] in H_u_sv.

    have no_bot_quorum_fwd:  (forall s : nat, ~ nextvote_bottom_quorum u_sv r p.-1 s)
      by admit. (* probably unprovable without revising 'enters_exclusively_for_value' *)
    have stv_fwd : u_sv.(stv) p = Some v
      by admit. (* should be provable through greach *)
    exact (honest_softvote_respects_excl_stv H_p no_bot_quorum_fwd H_u_sv stv_fwd H_send).
  }

  (* To finish get assumption that a softvote quorum exists from
     examining the certvoting *)
  admit.
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

Lemma honest_during_from_ustate trace g0 (H_path : is_trace g0 trace):
  forall ix g,
    onth trace ix = Some g ->
  forall uid u,
    g.(users).[? uid] = Some u ->
    ~~ u.(corrupt) ->
  forall r p s,
    step_lt (r,p,s) (step_of_ustate u) ->
    honest_during_step (r,p,s) uid trace.
Proof using.
  move => ix g H_g uid u H_u H_honest r p s H_lt.
  SearchAbout all.
  have : user_honest uid g by rewrite /user_honest H_u.
  rewrite -(onth_last_take H_g g0).
  move/(honest_last_all uid (is_trace_prefix H_path (ltn0Sn ix))) => H_prefix.
  unfold honest_during_step.
  suff H_suffix: (all (upred uid (fun u => ~~step_leb (step_of_ustate u) (r,p,s))) (drop ix.+1 trace)).
Admitted.

Lemma honest_at_from_during r p s uid trace:
      honest_during_step (r,p,s) uid trace ->
      forall g0 (H_path: is_trace g0 trace),
      forall n g, onth trace n = Some g ->
      forall u, g.(users).[? uid] = Some u ->
      step_le (step_of_ustate u) (r,p,s) ->
      user_honest_at n trace uid.
Proof using.
  clear.
  move => H_honest g0 H_path n g H_onth u H_u H_le.
  apply (onth_at_step H_onth).
  move: H_honest => /all_nthP - /(_ g n (onth_size H_onth)).
  rewrite (onth_nth H_onth) /upred /user_honest H_u => /implyP.
  by apply;apply /step_leP.
Qed.

Lemma one_certificate_per_period: forall g0 trace r p,
    state_before_round r g0 ->
    is_trace g0 trace ->
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

  pose proof (honest_at_from_during H_honest H_path) as H.
  specialize (H _ _ (step_in_path_onth_pre H_step)).
  specialize (H _ H0).
  apply H.
  rewrite H1.
  apply step_le_refl.
  }

  assert (user_honest_at ix2 trace voter) as H_honest2. {
  move: H_cert2.
  unfold certvoted_in_path_at. move => [g1 [g2 [H_step H_vote]]].
  pose proof (honest_at_from_during H_honest H_path) as H.
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

Lemma certificate_is_start_of_next_period:
  forall trace r p v,
    certified_in_period trace r p v ->
    forall uid,
      honest_in_period r p.+1 uid trace ->
      enters_exclusively_for_value uid r p.+1 v trace.
Proof using.
Admitted.

(* Maybe define a "period only nexvote quorum for v"
   instead of the exclusive entry? *)

Lemma excl_enter_excl_next:
  forall g0 trace (H_path: is_trace g0 trace),
  forall r (H_start: state_before_round r g0),
  forall (p : nat) (v : Value),
    1 < p ->
    (forall (uid : UserId),
      honest_in_period r p uid trace ->
      enters_exclusively_for_value uid r p v trace) ->
    (forall (uid : UserId),
      honest_in_period r p.+1 uid trace ->
      enters_exclusively_for_value uid r p.+1 v trace).
Proof using.
  move => g0 trace H_path r H_start p v H_p_gt H_prev_excl uid H_honest.
  have H_honest_softvotes: forall uid, honest_in_period r p uid trace ->
                            forall v', softvoted_in_path trace uid r p v' ->
                                       v' = v.
  {
  move => voter H_voter_honest v' [ix [g1 [g2 [H_step H_voted]]]].
  have H_voter_in := user_sent_in_pre H_voted.
  have H_voter_excl := H_prev_excl voter H_voter_honest.
  have H_stv : (g1.(users)[`H_voter_in]).(stv) p = Some v by admit.
  have H_no_nextvotes_bot : forall s, ~nextvote_bottom_quorum (g1.(users)[` H_voter_in]) r p.-1 s by admit. (* Need to carry forward from entry, probably have to revise entered_exclusively_for *)

  exact (honest_softvote_respects_excl_stv H_p_gt H_no_nextvotes_bot (in_fnd H_voter_in) H_stv H_voted).
  }

  have H_nextvote_val_respects: forall uid s v', nextvoted_val_in_path trace uid r p s v' -> v' = v.
  by admit.

  have H_no_nextvotes_open: forall uid s v', honest_during_step (r,p,s) uid trace -> ~nextvoted_open_in_path trace r p s uid.
    by admit.

    (*
    SearchAbout (0.+1 <= _.+1)
  pose proof (honest_in_period_entered H_path H_start H_honest )
    SearchAbout honest_in_period.
  enter from next votes...
  pose proof honest_softvote_respects_excl_stv. user_sent uid (Softvote,val v',r,p,uid) g1 g2
  SearchAbout Softvote.
  honest_in_period_entered.
   SearchAbout honest_in_period.
  *)
Admitted.

Lemma certificate_is_start_of_later_periods:
  forall trace g0  (H_path: is_trace g0 trace) r p v,
    certified_in_period trace r p v ->
  forall p', p' > p ->
    forall uid,
      honest_in_period r p' uid trace ->
      enters_exclusively_for_value uid r p' v trace.
Proof using.
  clear.
  move => trace g0 H_path r p v H_cert p' H_p_lt.
  have: p' = (p.+1 + (p' - p.+1))%nat by symmetry;apply subnKC.
  move: (p' - p.+1)%nat => n {p' H_p_lt}->.
  elim:n.
  (* Next step after certification *)
  by rewrite addn0; exact: certificate_is_start_of_next_period.
  (* Later steps *)
  move => n;rewrite addnS addSn.
  admit. (* by apply (excl_enter_excl_next H_path). *)
Admitted.

Lemma honest_in_from_during_and_send: forall r p s uid trace,
      honest_during_step (r,p,s) uid trace ->
  forall g0 (H_path : is_trace g0 trace),
  forall ix g1 g2,
    step_in_path_at g1 g2 ix trace ->
  forall mt v,
    user_sent uid (mt,v,r,p,uid) g1 g2 ->
  step_le (msg_step (mt,v,r,p,uid)) (r,p,s) ->
    honest_in_period r p uid trace.
Proof using.
  move => r p s uid trace H_honest g0 H_path ix g1 g2 H_step mt v H_sent H_msg_step.
  have H_g1 := step_in_path_onth_pre H_step.
  exists ix. rewrite H_g1.
  have key1 := user_sent_in_pre H_sent.
  rewrite (in_fnd key1).
  have H_step1 := utransition_label_start H_sent (in_fnd key1).
  lapply (user_honest_from_during H_path H_g1 (H_in:=key1)).
  *
    rewrite /user_honest (in_fnd key1) => /negP H_honest_g1.
    split;[assumption|].
    by injection H_step1.
  *
    revert H_honest.
    apply honest_during_le.
    rewrite H_step1.
    assumption.
Qed.

Theorem safety: forall g0 trace (r:nat),
    state_before_round r g0 ->
    is_trace g0 trace ->
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
  assert (1 <= p1) as H_p2.
  {
    move: H_cert1 => [quorum_p1 [H_creds [H_size _]]].
    move: (quorum_c_has_honest trace H_creds H_size) => [voter1 [H_in _]].
    move: H_creds => /fsubsetP /(_ _ H_in) /imfsetP [x H H_x].
    move: H_x H => {x}<- /asboolP.
    apply credentials_valid_period.
  }
  move: {H_p2}(leq_ltn_trans H_p2 Hlt) => H_p2.

  destruct (nosimpl H_cert2) as (q2 & H_q2 & H_size2 & H_cert2_voted).
  destruct (quorum_c_has_honest trace H_q2 H_size2)
     as (honest_voter & H_honest_q & H_honest_in).

  specialize (H_cert2_voted honest_voter H_honest_q).
  destruct (nosimpl H_cert2_voted) as (ix & ga1 & ga2 & [H_step2 H_send_vote2]).
  assert (honest_in_period r p2 honest_voter trace)
   by (eapply honest_in_from_during_and_send;[eassumption..|apply step_le_refl]).

  pose proof (certificate_is_start_of_later_periods H_path H_cert1 Hlt) as H_entry.

  symmetry.
  apply/(excl_enter_limits_cert_vote H_path H_p2 H_entry): H_cert2_voted.
  have H_honest_ga2 := negbT (user_sent_honest_post H_send_vote2).
  have H_in2:= (in_fnd (user_sent_in_post H_send_vote2)).

  exact (honest_during_from_ustate H_path (step_in_path_onth_post H_step2)
                                   H_in2
        H_honest_ga2 (utransition_label_end H_send_vote2 H_in2)).
Qed.

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

Lemma at_most_one_certval_in_p
      g0 trace (H_path: is_trace g0 trace)
      r0 (H_start: state_before_round r0 g0):
  forall ix g, onth trace ix = Some g ->
  forall uid u, g.(users).[? uid] = Some u ->
  forall r, r0 <= r ->
  forall p v1 v2,
    v1 \in certvals u r p -> v2 \in certvals u r p -> v1 = v2.
Proof using quorums_s_honest_overlap.
  clear -H_path H_start quorums_s_honest_overlap.
  move => ix g H_onth uid u H_lookup r H_round p v1 v2.
  unfold certvals, vote_values, soft_weight.
  rewrite !mem_filter.
  move => /andP [Hv1_q Hv1in].
  move => /andP [Hv2_q Hv2in].
  have H_votes_checked := (softvote_credentials_checked H_path H_start H_onth H_lookup H_round).

  have Hq := quorums_s_honest_overlap trace.
  specialize (Hq r p 2 _ _ (H_votes_checked _ _) Hv1_q (H_votes_checked _ _) Hv2_q).

  move: Hq => [softvoter [H_voted_v1 [H_voted_v2 H_softvoter_honest]]].
  assert (softvoted_in_path trace softvoter r p v1) as H_sent_v1. {
  apply (softvotes_sent H_path H_start H_onth H_lookup H_round).
  move:H_voted_v1 => /imfsetP /= [] x /andP [H_x_in].
  unfold matchValue. destruct x. move => /eqP ? /= ?;subst.
  assumption.
  assumption.
  }
  assert (softvoted_in_path trace softvoter r p v2) as H_sent_v2. {
  apply (softvotes_sent H_path H_start H_onth H_lookup H_round).
  move:H_voted_v2 => /imfsetP /= [] x /andP [H_x_in].
  unfold matchValue. destruct x. move => /eqP ? /= ?;subst.
  assumption.
  assumption.
  }
  move: H_sent_v1 => [ix_v1 H_sent_v1].
  move: H_sent_v2 => [ix_v2 H_sent_v2].

  by case:(no_two_softvotes_in_p H_path H_sent_v1 H_sent_v2).
Qed.

(*
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
Abort.

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
Abort.

Lemma partition_free_suffix : forall n trace,
  partition_free trace ->
  partition_free (drop n trace).
Proof.
intros n trace prfree_H.
generalize dependent n.
induction n. rewrite drop0. assumption.
unfold partition_free in * |- *.
Abort.

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
Abort.


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
Abort.


(* If some period r.p, p >= 2 is reached with unique starting value bot and the
   leader is honest, then the leader’s proposal is certified. *)
(* TODO: all users need starting value bot or just leader? *)
Lemma prop_c : forall ix path uid r p v b,
  p >= 2 ->
  all (fun u => user_stv_val_at ix path u p None) (domf (users_at ix path)) ->
  leader_in_path_at ix path uid r 1 v b ->
  user_honest_at ix path uid ->
  certified_in_period path r p v.
Abort.

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
Abort.

(* Honest user softvotes starting value *)
Lemma stv_not_bot_softvote : forall ix path r p v uid,
  uid \in domf (honest_users (users_at ix path)) ->
  user_stv_val_at ix path uid p (Some v) ->
  softvoted_in_path_at ix path uid r p v.
Abort.

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
  move/allP in H0. unfold prop_in1 in H0.
Abort.

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
Abort.
*)

End AlgoModel.
