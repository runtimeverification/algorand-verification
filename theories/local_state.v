(* Remember to re-run
   python2 scripts/extract_record_notation.py theories/local_state.v.rec UState > theories/local_state.v
   after editing this file!
   Running `make theories/local_state.v` should take care of this for you. *)

From mathcomp.ssreflect
Require Import all_ssreflect.

Require Import Coq.Reals.Reals.

Section LocalState.

Variable UserId : Type.
Variable Value : Type.
Variable PropRecord : Type.
Variable Vote : Type.

Record UState :=
  mkUState {
    id : UserId;
    corrupt       : bool;
    (* The user's current round (starts at 1) *)
    round         : nat;
    (* The user's current period (starts at 1) *)
    period        : nat;
    (* The user's current step counter (starts at 1) *)
    step          : nat;
    (* The user's current timer value (since the beginning of the current period) *)
    timer         : R;
    (* The user's next deadline time value (since the beginning of the current period) *)
    deadline      : R;
   (* The (local) time at which the user's current period started (i.e. local clock = p_start + timer *)
    p_start       : R;
    (* A sequence of proposal/reproposal records for the given round/period *)
    proposals     : nat -> nat -> seq PropRecord;
    (* A sequence of values seen for the given round/period *)
    blocks        : nat -> nat -> seq Value;
    (* A sequence of softvotes seen for the given round/period *)
    softvotes     : nat -> nat -> seq Vote;
    (* A sequence of certvotes seen for the given round/period *)
    certvotes     : nat -> nat -> seq Vote;
    (* A sequence of bottom-nextvotes seen for the given round/period/step *)
    nextvotes_open: nat -> nat -> nat -> seq UserId;
    (* A sequence of value-nextvotes seen for the given round/period/step *)
    nextvotes_val : nat -> nat -> nat -> seq Vote;
    (* A flag for a given round and period indicating whether the preconditions *)
    (* of certvoting in step 3 were satisfied at the time of step 3, regardless *)
    (* of whether the user was actually in the committee of that step *)
    has_certvoted : nat -> nat -> bool
  }.



Definition set_UState_id a v := mkUState v (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) (p_start a) (proposals a) (blocks a) (softvotes a) (certvotes a) (nextvotes_open a) (nextvotes_val a) (has_certvoted a).

Definition set_UState_corrupt a v := mkUState (id a) v (round a) (period a) (step a) (timer a) (deadline a) (p_start a) (proposals a) (blocks a) (softvotes a) (certvotes a) (nextvotes_open a) (nextvotes_val a) (has_certvoted a).

Definition set_UState_round a v := mkUState (id a) (corrupt a) v (period a) (step a) (timer a) (deadline a) (p_start a) (proposals a) (blocks a) (softvotes a) (certvotes a) (nextvotes_open a) (nextvotes_val a) (has_certvoted a).

Definition set_UState_period a v := mkUState (id a) (corrupt a) (round a) v (step a) (timer a) (deadline a) (p_start a) (proposals a) (blocks a) (softvotes a) (certvotes a) (nextvotes_open a) (nextvotes_val a) (has_certvoted a).

Definition set_UState_step a v := mkUState (id a) (corrupt a) (round a) (period a) v (timer a) (deadline a) (p_start a) (proposals a) (blocks a) (softvotes a) (certvotes a) (nextvotes_open a) (nextvotes_val a) (has_certvoted a).

Definition set_UState_timer a v := mkUState (id a) (corrupt a) (round a) (period a) (step a) v (deadline a) (p_start a) (proposals a) (blocks a) (softvotes a) (certvotes a) (nextvotes_open a) (nextvotes_val a) (has_certvoted a).

Definition set_UState_deadline a v := mkUState (id a) (corrupt a) (round a) (period a) (step a) (timer a) v (p_start a) (proposals a) (blocks a) (softvotes a) (certvotes a) (nextvotes_open a) (nextvotes_val a) (has_certvoted a).

Definition set_UState_p_start a v := mkUState (id a) (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) v (proposals a) (blocks a) (softvotes a) (certvotes a) (nextvotes_open a) (nextvotes_val a) (has_certvoted a).

Definition set_UState_proposals a v := mkUState (id a) (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) (p_start a) v (blocks a) (softvotes a) (certvotes a) (nextvotes_open a) (nextvotes_val a) (has_certvoted a).

Definition set_UState_blocks a v := mkUState (id a) (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) (p_start a) (proposals a) v (softvotes a) (certvotes a) (nextvotes_open a) (nextvotes_val a) (has_certvoted a).

Definition set_UState_softvotes a v := mkUState (id a) (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) (p_start a) (proposals a) (blocks a) v (certvotes a) (nextvotes_open a) (nextvotes_val a) (has_certvoted a).

Definition set_UState_certvotes a v := mkUState (id a) (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) (p_start a) (proposals a) (blocks a) (softvotes a) v (nextvotes_open a) (nextvotes_val a) (has_certvoted a).

Definition set_UState_nextvotes_open a v := mkUState (id a) (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) (p_start a) (proposals a) (blocks a) (softvotes a) (certvotes a) v (nextvotes_val a) (has_certvoted a).

Definition set_UState_nextvotes_val a v := mkUState (id a) (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) (p_start a) (proposals a) (blocks a) (softvotes a) (certvotes a) (nextvotes_open a) v (has_certvoted a).

Definition set_UState_has_certvoted a v := mkUState (id a) (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) (p_start a) (proposals a) (blocks a) (softvotes a) (certvotes a) (nextvotes_open a) (nextvotes_val a) v.

End LocalState.



Notation "{[ a 'with' 'id' := v ]}" := (set_UState_id  _ _ _ _ a v).

Notation "{[ a 'with' 'corrupt' := v ]}" := (set_UState_corrupt  _ _ _ _ a v).

Notation "{[ a 'with' 'round' := v ]}" := (set_UState_round  _ _ _ _ a v).

Notation "{[ a 'with' 'period' := v ]}" := (set_UState_period  _ _ _ _ a v).

Notation "{[ a 'with' 'step' := v ]}" := (set_UState_step  _ _ _ _ a v).

Notation "{[ a 'with' 'timer' := v ]}" := (set_UState_timer  _ _ _ _ a v).

Notation "{[ a 'with' 'deadline' := v ]}" := (set_UState_deadline  _ _ _ _ a v).

Notation "{[ a 'with' 'p_start' := v ]}" := (set_UState_p_start  _ _ _ _ a v).

Notation "{[ a 'with' 'proposals' := v ]}" := (set_UState_proposals  _ _ _ _ a v).

Notation "{[ a 'with' 'blocks' := v ]}" := (set_UState_blocks  _ _ _ _ a v).

Notation "{[ a 'with' 'softvotes' := v ]}" := (set_UState_softvotes  _ _ _ _ a v).

Notation "{[ a 'with' 'certvotes' := v ]}" := (set_UState_certvotes  _ _ _ _ a v).

Notation "{[ a 'with' 'nextvotes_open' := v ]}" := (set_UState_nextvotes_open  _ _ _ _ a v).

Notation "{[ a 'with' 'nextvotes_val' := v ]}" := (set_UState_nextvotes_val  _ _ _ _ a v).

Notation "{[ a 'with' 'has_certvoted' := v ]}" := (set_UState_has_certvoted  _ _ _ _ a v).


Arguments set_UState_id  _ _ _ _ _ _/.

Arguments set_UState_corrupt  _ _ _ _ _ _/.

Arguments set_UState_round  _ _ _ _ _ _/.

Arguments set_UState_period  _ _ _ _ _ _/.

Arguments set_UState_step  _ _ _ _ _ _/.

Arguments set_UState_timer  _ _ _ _ _ _/.

Arguments set_UState_deadline  _ _ _ _ _ _/.

Arguments set_UState_p_start  _ _ _ _ _ _/.

Arguments set_UState_proposals  _ _ _ _ _ _/.

Arguments set_UState_blocks  _ _ _ _ _ _/.

Arguments set_UState_softvotes  _ _ _ _ _ _/.

Arguments set_UState_certvotes  _ _ _ _ _ _/.

Arguments set_UState_nextvotes_open  _ _ _ _ _ _/.

Arguments set_UState_nextvotes_val  _ _ _ _ _ _/.

Arguments set_UState_has_certvoted  _ _ _ _ _ _/.
