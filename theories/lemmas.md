## Transition invariants

* softvote_credentials_checked

Our model only allows messages with a valid credential to be sent,
so if there are no invalid messages in flight in the initial state
of a trace, any message's sender belonds to the appropriate committee.
This lemma states the particular case for softvote messages.

## Analyzing traces

* transition_label_unique

This rule says that different rules in the transition relation
do not overlap.

* pending_honest_sent

This lemma says that if any message in a mailbox which claims to be from
a step and sender at which the sender was honest, then there was a step
in the trace where the sender sent the message according to the protocol.
(though the particular instance of the message in the mailbox may have
come from the adversary replaying a message).

* softvotes_sent

This lemma says that if a vote for a period is recorded in a user's `softvotes`
and the voter was honest at that step, then that user honestly sent a
softvote message earlier in the trace.

The proof should combine `received_was_sent` with
a simpler transition invariant saying that a vote is recorded in a user's
`softvotes` set only if that user received such a softvote message
earlier in the trace.

* period_advance_only_by_next_votes

This lemma says that a user which entered a period must have recieved
a quorum of next votes from a step of the previous period.
The proof analyzes the transitions which can advance a user's period
without advancing the round to see that enough votes must have been
recorded in the user's `nextvotes_open` or `nextvotes_val` sets,
then should combine with a sublemma like `softvotes_sent`

* cert_stv_consistent

A user's `cert_may_exist` flag and starting value `stv` should be
consistent.

* honest_in_period_entered

In a trace with enough history, a user which has a transition
within some period must have a transition at which they entered the
period. Should follow from `path_steps`.

## Medium-level claims

* no_two_softvotes_in_p

This lemma states that an honest user softvotes at most once in a period,
the proof should be straightforward and similar to `no_two_certvotes_in_p`.

## Major claims

* honest_certvote_respects_stv

This lemma helps ties together nextvotes and a following certvote, by
stating that a users with a non-bot starting value may not certvote
for any other value.

* certificate_is_start_of_later_periods

Once a certificate has been produced, honest users can only enter any later period
with their starting value set to the block value which has a certificate.
For the induction step, this will need a lemma that honest nextvotes respect the
starting value.