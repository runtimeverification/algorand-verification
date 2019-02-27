From mathcomp.ssreflect
Require Import all_ssreflect.

From mathcomp.finmap
Require Import finmap.

Require Import Coq.Reals.Reals.
Require Import Coq.Relations.Relation_Definitions.
Require Import Interval.Interval_tactic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

(* And a finite set of values *)
Variable Value : finType .

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

(* Not used anymore *)
Definition MsgPool := {fset Msg} .

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
    deadline      : MType -> option R;
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

(* The credential of a User at a round-period-step triple
   (we abstract away the random value produced by an Oracle)
*)
Inductive Credential :=
  | cred : UserId -> nat -> nat -> nat -> Credential.

(* A proposition for whether a given credential qualifies its
   owner to be a committee member *)
(* Note: This abstract away how credential values are 
   interpreted (which is a piece of detail that may not be
   relevant to the model at this stage) *)
Variable committee_cred : Credential -> Prop. 

(* Constructor of values signed by a user
*)
Inductive Signature :=
  | sign : UserId -> Value -> Signature.

(* The global state
   Note: I think we should abstract over channels and instead
   collect messages in transit in the global state.
*)
Record GState :=
  mkGState {
    now     : R;
    network_partition : bool;
    users   : seq UState ;
    msg_in_transit : seq Msg;
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

Definition update_users (users' : seq UState) (g : GState) : GState :=
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
Variable chi   : nat -> nat.

(* User-state-level trnasitions *)
Definition u_transition_type := relation UState.

(* TODO: what does valid mean? *)
Definition valid (B : nat) : Prop := True.

Definition valid_round_period (u : UState) r p : Prop :=
  u.(round) = r /\ u.(period) = p .

Definition valid_step (u : UState) s : Prop :=
  u.(step) = s .

Definition comm_cred (u : UState) r p k : Prop :=
  committee_cred (cred u.(id) r p k) .

(* this has been broken down into the smaller propositions above *)
(*
Definition check_params (u : UState) r p c s : Prop :=
  u.(round) = r /\ u.(period) = p /\ u.(step) = s /\ cred u.(id) r p 1 = c.
*)

(* TODO: c < xi_1 *)
(* credentials are now abstract *)
Definition propose_ok (pre : UState) B r p : Prop :=
  valid_round_period pre r p /\ p > 1 /\
  valid_step pre Proposing /\
  comm_cred pre r p 1 /\
  pre.(cert_may_exist) /\ 
  valid B.

(* TODO: update deadline with softvote -> 2*lambda + delta *)
Definition propose_result (pre : UState) : UState :=
  update_step
    (update_deadline (update_timer pre 0)
                     (fun b => if b == Proposal then None else pre.(deadline) b))
    Certvoting.

(* TODO: v = H(B) *)
Definition repropose_ok (pre : UState) (B : nat) v r p : Prop :=
  valid_round_period pre r p /\
  valid_step pre Proposing /\
  comm_cred pre r p 1 /\
  v \in pre.(prev_certvals).

(* TODO: broadcasting? *)
(* TODO: update deadline with softvote -> 2*lambda + delta *)
Definition repropose_result (pre : UState) : UState :=
  update_step
    (update_deadline (update_timer pre 0)
                     (fun b => if b == Proposal then None else pre.(deadline) b))
    Softvoting.

(* TODO: c >= xi_1 *)
Definition no_propose_ok (pre : UState) r p : Prop :=
  valid_round_period pre r p /\
  valid_step pre Proposing /\
  comm_cred pre r p 1.
  
(* TODO: update deadline with softvote -> 2*lambda + delta *)
Definition no_propose_result (pre : UState) : UState :=
  update_step
    (update_deadline (update_timer pre 0)
                     (fun b => if b == Proposal then None else pre.(deadline) b))
    Softvoting.

(* TODO: softvote_new preconditions *)
Definition svote_new_ok (pre : UState) (v : Value) r p : Prop :=
  valid_round_period pre r p /\
  valid_step pre Softvoting /\ 
  comm_cred pre r p 2 /\
  (* now >= period_start + big_lambda *) 
  ~ pre.(cert_may_exist) .
  (* pre.(proposals) r p has v as its current leader value *)         

(* TODO: softvote_new result *)
Definition svote_new_result (pre : UState) (v : Value) : UState :=
  update_step
    (update_deadline (update_timer pre 0)
                     (fun b => if b == Proposal then None else pre.(deadline) b))
    Softvoting.

Definition tr_fun (msg : Msg) (pre : UState) B r p : seq Msg * UState :=
  match msg.1.1.1.1 with
  | Proposal =>
    match propose_ok pre B r p with
    | True =>
      let: post := propose_result pre in
      let: bmsg := (Block, step_val B, r, p, pre.(id)) in
      ([:: msg; bmsg], post)
    end
  | _ => ([:: msg], pre)
  end.


(* [TODO: define user-state-level transitions ] *)
Reserved Notation "x ~> y" (at level 70).

Inductive UTransition : u_transition_type := (***)
  (* | dummy : forall (pre post : UState), pre ~> post *)
  | propose : forall (pre : UState) B r p,
      propose_ok pre B r p ->
      pre ~> propose_result pre
  | repropose : forall (pre : UState) B v r p,
      repropose_ok pre B v r p ->
      pre ~> repropose_result pre
  | no_propose : forall (pre : UState) r p,
      no_propose_ok pre r p ->
      pre ~> no_propose_result pre
  | svote_new : forall (pre : UState) v r p,
      svote_new_ok pre v r p ->
      pre ~> svote_new_result pre v
where "x ~> y" := (UTransition x y) : type_scope .

(* Note: would be nice to use ssreflect's rel instead of relation
   so that connect may be directly used to define the reflexive
   transivite closure *)
(* Definition UTransition_closed pre post :=
 connect UTransition pre post.*)


(* Global transition relation type *)
Definition g_transition_type := relation GState .

Reserved Notation "x ~~> y" (at level 90).

Definition user_can_advance_timer (increment : posreal) (u : UState) : Prop :=
  forall (a : MType),
    match u.(deadline) a with
    | None => True
    | Some d => (u.(timer) + pos increment <= d)%R
    end.
Arguments user_can_advance_timer increment u /.
Definition user_advance_timer (increment : posreal) (u : UState) : UState :=
  update_timer u (u.(timer) + pos increment)%R.

Definition tick_ok increment pre : Prop :=
  List.Forall (user_can_advance_timer increment) (pre.(users)).
Definition tick_result increment pre :=
  pre.(update_now (pre.(now) + pos increment)%R)
     .(update_users (map (user_advance_timer increment) pre.(users))).

(* [TODO: define the transition relation]
*)
Inductive GTransition : g_transition_type :=  (***)
| tick : forall increment pre, tick_ok increment pre ->
    pre ~~> tick_result increment pre
where "x ~~> y" := (GTransition x y) : type_scope .

(* We might also think of an initial state S and a schedule of events X
   and comptue traces corresponding to S and X, and then showing properties
   on them
*)


(** Now we have lemmas showing that transitions preserve various invariants *)

Definition user_timers_valid (u : UState) : Prop :=
  (u.(p_start) <= u.(timer) /\
  forall (a : MType),
  match u.(deadline) a with
  | Some d => u.(timer) <= d
  | None => True
  end)%R.
Arguments user_timers_valid u /.

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

End AlgoModel.