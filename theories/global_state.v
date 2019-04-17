(* Remember to re-run
   python2 scripts/extract_record_notation.py theories/global_state.v.rec GState > theories/global_state.v
   after editing this file!
   Running `make theories/global_state.v` should take care of this for you. *)

From mathcomp.ssreflect
Require Import all_ssreflect.

From mathcomp.finmap
Require Import finmap multiset.

Require Import Coq.Reals.Reals.
From Algorand Require Import Rstruct.

Section GlobalState.

Variable UserId : choiceType.
Variable UState : Type.
Variable Msg : choiceType.

Record GState :=
  mkGState {
    (* The current global time value *)
    now : R ;
    (* A flag indicating whether the network is currently partitioned *)
    network_partition : bool ;
    (* The global set of users as a finite map of user ids to user states *)
    users : @finmap_of UserId UState (Phant _) ;
    (* Messages in transit as a finite map from user ids (targets) to multisets of messages *)
    msg_in_transit : @finmap_of UserId (@multiset_of _ (Phant (R * Msg))) (Phant _) ;
    (* The history of all messages broadcast as a multiset of messages *)
    msg_history : @multiset_of _ (Phant Msg) 
  }.



Definition set_GState_now a v := mkGState v (network_partition a) (users a) (msg_in_transit a) (msg_history a).

Definition set_GState_network_partition a v := mkGState (now a) v (users a) (msg_in_transit a) (msg_history a).

Definition set_GState_users a v := mkGState (now a) (network_partition a) v (msg_in_transit a) (msg_history a).

Definition set_GState_msg_in_transit a v := mkGState (now a) (network_partition a) (users a) v (msg_history a).

Definition set_GState_msg_history a v := mkGState (now a) (network_partition a) (users a) (msg_in_transit a) v.

End GlobalState.



Notation "{[ a 'with' 'now' := v ]}" := (set_GState_now  _ _ _ a v).

Notation "{[ a 'with' 'network_partition' := v ]}" := (set_GState_network_partition  _ _ _ a v).

Notation "{[ a 'with' 'users' := v ]}" := (set_GState_users  _ _ _ a v).

Notation "{[ a 'with' 'msg_in_transit' := v ]}" := (set_GState_msg_in_transit  _ _ _ a v).

Notation "{[ a 'with' 'msg_history' := v ]}" := (set_GState_msg_history  _ _ _ a v).


Arguments set_GState_now  _ _ _ _ _/.

Arguments set_GState_network_partition  _ _ _ _ _/.

Arguments set_GState_users  _ _ _ _ _/.

Arguments set_GState_msg_in_transit  _ _ _ _ _/.

Arguments set_GState_msg_history  _ _ _ _ _/.
