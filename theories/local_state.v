(* Remember to re-run
   python2 scripts/extract_record_notation.py theories/local_state.v.rec UState > theories/local_state.v
   after editing this file!
   Running `make theories/local_state.v` should take care of this for you. *)

From mathcomp.ssreflect
Require Import all_ssreflect.

Require Import Coq.Reals.Reals.

Section LocalState.

Variable Value : Type.
Variable Step : Type.
Variable Msg : Type.
Variable PropRecord : Type.
Variable Vote : Type.

Record UState :=
  mkUState {
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
    nextvotes_val : nat -> nat -> nat -> seq Vote
  }.



Definition set_UState_corrupt a v := mkUState v (round a) (period a) (step a) (timer a) (deadline a) (p_start a) (rec_msgs a) (cert_may_exist a) (prev_certvals a) (proposals a) (blocks a) (softvotes a) (certvotes a) (certvals a) (nextvotes_open a) (nextvotes_val a).

Definition set_UState_round a v := mkUState (corrupt a) v (period a) (step a) (timer a) (deadline a) (p_start a) (rec_msgs a) (cert_may_exist a) (prev_certvals a) (proposals a) (blocks a) (softvotes a) (certvotes a) (certvals a) (nextvotes_open a) (nextvotes_val a).

Definition set_UState_period a v := mkUState (corrupt a) (round a) v (step a) (timer a) (deadline a) (p_start a) (rec_msgs a) (cert_may_exist a) (prev_certvals a) (proposals a) (blocks a) (softvotes a) (certvotes a) (certvals a) (nextvotes_open a) (nextvotes_val a).

Definition set_UState_step a v := mkUState (corrupt a) (round a) (period a) v (timer a) (deadline a) (p_start a) (rec_msgs a) (cert_may_exist a) (prev_certvals a) (proposals a) (blocks a) (softvotes a) (certvotes a) (certvals a) (nextvotes_open a) (nextvotes_val a).

Definition set_UState_timer a v := mkUState (corrupt a) (round a) (period a) (step a) v (deadline a) (p_start a) (rec_msgs a) (cert_may_exist a) (prev_certvals a) (proposals a) (blocks a) (softvotes a) (certvotes a) (certvals a) (nextvotes_open a) (nextvotes_val a).

Definition set_UState_deadline a v := mkUState (corrupt a) (round a) (period a) (step a) (timer a) v (p_start a) (rec_msgs a) (cert_may_exist a) (prev_certvals a) (proposals a) (blocks a) (softvotes a) (certvotes a) (certvals a) (nextvotes_open a) (nextvotes_val a).

Definition set_UState_p_start a v := mkUState (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) v (rec_msgs a) (cert_may_exist a) (prev_certvals a) (proposals a) (blocks a) (softvotes a) (certvotes a) (certvals a) (nextvotes_open a) (nextvotes_val a).

Definition set_UState_rec_msgs a v := mkUState (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) (p_start a) v (cert_may_exist a) (prev_certvals a) (proposals a) (blocks a) (softvotes a) (certvotes a) (certvals a) (nextvotes_open a) (nextvotes_val a).

Definition set_UState_cert_may_exist a v := mkUState (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) (p_start a) (rec_msgs a) v (prev_certvals a) (proposals a) (blocks a) (softvotes a) (certvotes a) (certvals a) (nextvotes_open a) (nextvotes_val a).

Definition set_UState_prev_certvals a v := mkUState (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) (p_start a) (rec_msgs a) (cert_may_exist a) v (proposals a) (blocks a) (softvotes a) (certvotes a) (certvals a) (nextvotes_open a) (nextvotes_val a).

Definition set_UState_proposals a v := mkUState (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) (p_start a) (rec_msgs a) (cert_may_exist a) (prev_certvals a) v (blocks a) (softvotes a) (certvotes a) (certvals a) (nextvotes_open a) (nextvotes_val a).

Definition set_UState_blocks a v := mkUState (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) (p_start a) (rec_msgs a) (cert_may_exist a) (prev_certvals a) (proposals a) v (softvotes a) (certvotes a) (certvals a) (nextvotes_open a) (nextvotes_val a).

Definition set_UState_softvotes a v := mkUState (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) (p_start a) (rec_msgs a) (cert_may_exist a) (prev_certvals a) (proposals a) (blocks a) v (certvotes a) (certvals a) (nextvotes_open a) (nextvotes_val a).

Definition set_UState_certvotes a v := mkUState (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) (p_start a) (rec_msgs a) (cert_may_exist a) (prev_certvals a) (proposals a) (blocks a) (softvotes a) v (certvals a) (nextvotes_open a) (nextvotes_val a).

Definition set_UState_certvals a v := mkUState (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) (p_start a) (rec_msgs a) (cert_may_exist a) (prev_certvals a) (proposals a) (blocks a) (softvotes a) (certvotes a) v (nextvotes_open a) (nextvotes_val a).

Definition set_UState_nextvotes_open a v := mkUState (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) (p_start a) (rec_msgs a) (cert_may_exist a) (prev_certvals a) (proposals a) (blocks a) (softvotes a) (certvotes a) (certvals a) v (nextvotes_val a).

Definition set_UState_nextvotes_val a v := mkUState (corrupt a) (round a) (period a) (step a) (timer a) (deadline a) (p_start a) (rec_msgs a) (cert_may_exist a) (prev_certvals a) (proposals a) (blocks a) (softvotes a) (certvotes a) (certvals a) (nextvotes_open a) v.

End LocalState.



Notation "{[ a 'with' 'corrupt' := v ]}" := (set_UState_corrupt  _ _ _ _ _ a v).

Notation "{[ a 'with' 'round' := v ]}" := (set_UState_round  _ _ _ _ _ a v).

Notation "{[ a 'with' 'period' := v ]}" := (set_UState_period  _ _ _ _ _ a v).

Notation "{[ a 'with' 'step' := v ]}" := (set_UState_step  _ _ _ _ _ a v).

Notation "{[ a 'with' 'timer' := v ]}" := (set_UState_timer  _ _ _ _ _ a v).

Notation "{[ a 'with' 'deadline' := v ]}" := (set_UState_deadline  _ _ _ _ _ a v).

Notation "{[ a 'with' 'p_start' := v ]}" := (set_UState_p_start  _ _ _ _ _ a v).

Notation "{[ a 'with' 'rec_msgs' := v ]}" := (set_UState_rec_msgs  _ _ _ _ _ a v).

Notation "{[ a 'with' 'cert_may_exist' := v ]}" := (set_UState_cert_may_exist  _ _ _ _ _ a v).

Notation "{[ a 'with' 'prev_certvals' := v ]}" := (set_UState_prev_certvals  _ _ _ _ _ a v).

Notation "{[ a 'with' 'proposals' := v ]}" := (set_UState_proposals  _ _ _ _ _ a v).

Notation "{[ a 'with' 'blocks' := v ]}" := (set_UState_blocks  _ _ _ _ _ a v).

Notation "{[ a 'with' 'softvotes' := v ]}" := (set_UState_softvotes  _ _ _ _ _ a v).

Notation "{[ a 'with' 'certvotes' := v ]}" := (set_UState_certvotes  _ _ _ _ _ a v).

Notation "{[ a 'with' 'certvals' := v ]}" := (set_UState_certvals  _ _ _ _ _ a v).

Notation "{[ a 'with' 'nextvotes_open' := v ]}" := (set_UState_nextvotes_open  _ _ _ _ _ a v).

Notation "{[ a 'with' 'nextvotes_val' := v ]}" := (set_UState_nextvotes_val  _ _ _ _ _ a v).


Arguments set_UState_corrupt  _ _ _ _ _ _ _/.

Arguments set_UState_round  _ _ _ _ _ _ _/.

Arguments set_UState_period  _ _ _ _ _ _ _/.

Arguments set_UState_step  _ _ _ _ _ _ _/.

Arguments set_UState_timer  _ _ _ _ _ _ _/.

Arguments set_UState_deadline  _ _ _ _ _ _ _/.

Arguments set_UState_p_start  _ _ _ _ _ _ _/.

Arguments set_UState_rec_msgs  _ _ _ _ _ _ _/.

Arguments set_UState_cert_may_exist  _ _ _ _ _ _ _/.

Arguments set_UState_prev_certvals  _ _ _ _ _ _ _/.

Arguments set_UState_proposals  _ _ _ _ _ _ _/.

Arguments set_UState_blocks  _ _ _ _ _ _ _/.

Arguments set_UState_softvotes  _ _ _ _ _ _ _/.

Arguments set_UState_certvotes  _ _ _ _ _ _ _/.

Arguments set_UState_certvals  _ _ _ _ _ _ _/.

Arguments set_UState_nextvotes_open  _ _ _ _ _ _ _/.

Arguments set_UState_nextvotes_val  _ _ _ _ _ _ _/.
