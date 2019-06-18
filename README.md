# Algorand verification

A formalization of the [Algorand](https://www.algorand.com) consensus protocol using the [Coq](https://coq.inria.fr) proof assistant.
The project provides: 
- an abstract and timed specification of the protocol as a transition system, including node-level behavior, asynchronous messaging and a model of the adversary,
- a **complete** formal proof of _asynchronous safety_ for the transition system.

<img src="resources/pdf-icon.png" alt="PDF" width="2%" /> *[Modeling and Verification of the Algorand Consensus Protocol](https://github.com/runtimeverification/algorand-verification/blob/master/report/report.pdf)*

Statements of some _liveness_ properties for the transition system are also provided, but these are work-in-progress and their proofs are currently **incomplete**.

Requirements
------------

- [`Coq 8.9`](https://coq.inria.fr/download)
- [`MathComp ssreflect 1.8.0`](https://math-comp.github.io)
- [`MathComp algebra 1.8.0`](https://math-comp.github.io)
- [`MathComp finmap 1.2.1`](https://github.com/math-comp/finmap)
- [`Interval 3.4.0`](http://coq-interval.gforge.inria.fr)
- [`Ppsimpl 8.9.0`](https://gforge.inria.fr/scm/?group_id=5430)

Building
--------

We recommend installing the dependencies of the project via
[OPAM](http://opam.ocaml.org/doc/Install.html):
```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.9.1 coq-mathcomp-ssreflect.1.8.0 \
  coq-mathcomp-algebra.1.8.0 coq-mathcomp-finmap.1.2.1 \
  coq-interval.3.4.0 coq-ppsimpl.8.9.0
```

Then, run `make` in the project root directory. This will check all the definitions and proofs.

Files
-----

All Coq vernacular files can be found under the `theories` directory, and their content is as follows:

- `boolp.v`, `reals.v`, `Rstruct.v`, `R_util.v`: definitions and lemmas for using real numbers via MathComp and SSReflect, adapted from the [MathComp analysis project](https://github.com/math-comp/analysis)
- `fmap_ext.v`: some useful auxiliary definitions and lemmas about finite maps
- `local_state.v`: definition of Algorand local node state
- `global_state.v`: definition of Algorand global system state
- `algorand_model.v`: definition of the Algorand transition system, along with helper functions and facts
- `safety_helpers.v`: helper functions and lemmas used when proving safety of the transition system
- `quorums.v`: definitions and hypotheses about quorums of nodes
- `safety.v`: statement and complete formal proof of safety for the transition system
- `liveness.v`: an initial attempt at specifying liveness properties for the transition system. This part is work-in-progress and thus the file contains incomplete (admitted) proofs.

Getting Help
------------
Feel free to report GitHub issues or to contact us at: contact@runtimeverification.com
