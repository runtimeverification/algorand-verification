From mathcomp.ssreflect
Require Import all_ssreflect.

From mathcomp.finmap
Require Import finmap.

Require Import Coq.Reals.Reals.
Require Import Interval.Interval_tactic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section AlgoModel.


(* We first define a user's state structure *)
(* Note: these definitions follow quite closely the ones given by Victor
   in his automaton model of the system. We may stick to those or refine/abstract 
   over some of the details as we move on.
*)

(* We assume a finite set of users
*)
Variable UserId : finType.

(* What are the values manipulated by the protocol? block hashes perhaps? 
*)
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

(***************
   I was here trying to equip MType with a fintype structure. Some progress is made
   as you can see below but then it took me too much time trying to figure out why the
   FinMixin would't work..  So I gave up at that point. 
*)
(*
Definition eqMT (mt1 mt2: MType) := 
  match mt1, mt2 with
  | Block, Block => true
  | Proposal, Proposal => true
  | Reproposal, Reproposal => true
  | Softvote, Softvote => true
  | Certvote, Certvote => true
  | Nextvote_Open, Nextvote_Open => true
  | Nextvote_Val, Nextvote_Val => true
  | _, _ => false
  end.

Lemma eqMTP : Equality.axiom eqMT.
Proof.
move=> n m. apply: (iffP idP) => [ | <- ] ; last by elim n. 
elim: n m => [] [H1 | H2 | H3 | H4 | H5 | H6 | H7]  //= .  
Qed.

Canonical MType_eqMixin := EqMixin eqMTP. 
Canonical MType_eqType := EqType MType MType_eqMixin.


Definition MType_enum := [:: Block; Proposal; Reproposal; Softvote; Certvote; Nextvote_Open; Nextvote_Val].
Check MType_enum.

Lemma MType_enumP : Finite.axiom MType_enum. 
Proof. by case. Qed.

Check MType_enumP.
Check MType_enum.

Check Finite.axiom.
Check FinMixin.

(* This here fails!! *)
Definition MType_finMixin := Eval hnf in FinMixin MType_enumP.
***************)


(* None is bottom *)
Definition MaybeValue := option Value.

(* Not sure if we will ever need this, but it these are the strucutres used as values in 
   messages in Victor's paper
*)  
Inductive ExValue :=
  | val      : MaybeValue -> ExValue
  | step_val : nat -> ExValue
  | repr_val : Value -> UserId -> nat -> ExValue
  | nexv_val : Value -> nat -> ExValue.

(* A message type as a product type *)
Definition Msg := (MType * ExValue * nat * nat * UserId)%type.

(* Alternatively, we could construct a message as a more elaborate record ??) 
Record Msg := 
  mkMsg {
    type : MType ; val : Value ; round: nat ; period : nat ; user : UserId
  }.
*)

(* Obviously this is not possible, but it would have been useful (let's discuss this when we meet)
*)
(*
Definition MsgPool := {fset Msg} .
*)

(* A proposal/preproposal record is a triple consisting of two
   values along with a boolean indicating with the this is 
   a proposal (true) or a preproposal (false) 
*)
Definition PropRecord := (Value * Value * bool)%type.

(* A vote is a pair of values 
*)
Definition Vote := (nat * Value)%type.

(* Constructors for the different steps in a period
*)
Inductive Steps :=
  | Proposing 
  | Softvoting
  | Certvoting
  | Nextvoting .

(* And now the state of a user
   Note: again we may end up not using all of these fields (and there may
   be others we may want to add later)
*)
Record User := 
  mkUser { 
    id            : UserId;
    corrupt       : bool;
    round         : nat;
    period        : nat;
    step          : Steps;
    timer         : R;
    p_start       : R;
    rec_msgs      : list Msg;
    cert_may_exist: bool;
    prev_certvals : list Value;
    proposals     : nat -> nat -> list PropRecord;    
    blocks        : nat -> nat -> list Value;
    softvotes     : nat -> nat -> list Vote;  
    certvotes     : nat -> nat -> list Vote;
    certvals      : nat -> nat -> list Value;
    nextvotes_open: nat -> nat -> nat -> list Vote;
    nextvotes_val : nat -> nat -> nat -> list Vote;
  }.

(* The credential of a User at a round-period-step triple 
   (we abstract away the random value produced by an Oracle)
*)
Inductive Credential := 
  | cred : UserId -> nat -> nat -> nat -> Credential.

(* Constructor of values signed by a user
*)
Inductive Signature :=
  | sign : UserId -> Value -> Signature. 

(* The global state 
   Note: I think we should abstract over channels and instead 
   collect messages in transit in the global state.
*)
Record Global :=
  mkGlobal {
    now     : R;
    network_partition : bool;
    users   : list User ;
    msg_in_transit : list Msg;
  }.    

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
Variable chi   : nat -> Value. 



End AlgoModel.