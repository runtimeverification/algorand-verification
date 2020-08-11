# Algorand Verification

[![CI][action-shield]][action-link]

[action-shield]: https://github.com/runtimeverification/algorand-verification/workflows/CI/badge.svg?branch=master
[action-link]: https://github.com/runtimeverification/algorand-verification/actions?query=workflow%3ACI

A formalization of the [Algorand](https://www.algorand.com) consensus protocol using the [Coq proof assistant](https://coq.inria.fr).
The project provides: 
- an abstract and timed specification of the protocol as a transition system, including node-level behavior, asynchronous messaging and a model of the adversary,
- a **complete** formal proof of _asynchronous safety_ for the transition system.

<img src="resources/pdf-icon.png" alt="PDF" width="2%" /> *[Modeling and Verification of the Algorand Consensus Protocol](https://github.com/runtimeverification/algorand-verification/blob/master/report/report.pdf)*

Statements of some _liveness_ properties for the transition system are also provided, but these are work-in-progress and their proofs are currently **incomplete**.

## Requirements

- [`Coq 8.12`](https://github.com/coq/coq/releases/tag/V8.12.0)
- [`MathComp ssreflect 1.11`](https://math-comp.github.io)
- [`MathComp algebra`](https://math-comp.github.io)
- [`MathComp finmap 1.5.0`](https://github.com/math-comp/finmap)
- [`MathComp analysis 0.3.2`](https://github.com/math-comp/analysis)
- [`Coq record update`](https://github.com/tchajed/coq-record-update)

## Building

We recommend installing the dependencies of the project via
[OPAM](http://opam.ocaml.org/doc/Install.html), for example:
```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.12.0 coq-mathcomp-ssreflect.1.11.0 \
  coq-mathcomp-algebra coq-mathcomp-finmap.1.5.0 \
  coq-mathcomp-analysis.0.3.2 coq-record-update
```

Then, run `make` in the project root directory. This will check all the definitions and proofs.

## Files

All Coq vernacular files can be found under the `theories` directory, and their content is as follows:

- `zify.v`: definitions for using the `lia` arithmetic tactic for MathComp from [mczify](https://github.com/pi8027/mczify)
- `R_util.v`: auxiliary lemmas on real numbers
- `fmap_ext.v`: auxiliary definitions and results on finite maps
- `algorand_model.v`: definition of the Algorand local state, global state, and transition system, along with helper functions and facts
- `safety_helpers.v`: helper functions and lemmas used when proving safety of the transition system
- `quorums.v`: definitions and hypotheses about quorums of nodes
- `safety.v`: statement and complete formal proof of safety for the transition system
- `liveness.v`: an initial attempt at specifying liveness properties for the transition system. This part is work-in-progress and thus the file contains incomplete (admitted) proofs.

## Help and Feedback

Feel free to report GitHub issues or to contact us at: contact@runtimeverification.com
