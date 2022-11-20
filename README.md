# Algorand Verification

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/runtimeverification/algorand-verification/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/runtimeverification/algorand-verification/actions?query=workflow:"Docker%20CI"




The Algorand consensus protocol is the foundation of a decentralized
digital currency and transactions platform. This project provides a
model of the protocol in Coq, expressed as a transition system over
global states in a message-passing distributed system. Included is
a formal proof of safety for the transition system.

## Meta

- License: [University of Illinois/NCSA Open Source License](LICENSE.md)
- Compatible Coq versions: 8.14 or later
- Additional dependencies:
  - [MathComp ssreflect 1.15.0 or later](https://math-comp.github.io)
  - [MathComp algebra](https://math-comp.github.io)
  - [MathComp finmap 1.5.2 or later](https://github.com/math-comp/finmap)
  - [MathComp analysis 0.5.2 or later](https://github.com/math-comp/analysis)
  - [Mczify](https://github.com/math-comp/mczify)
  - [Coq record update](https://github.com/tchajed/coq-record-update)
- Coq namespace: `Algorand`
- Related publication(s):
  - [Towards a Verified Model of the Algorand Consensus Protocol in Coq](https://arxiv.org/abs/1907.05523) doi:[10.1007/978-3-030-54994-7_27](https://doi.org/10.1007/978-3-030-54994-7_27)

## Building

We recommend installing the dependencies of the project via
[opam](http://opam.ocaml.org/doc/Install.html), for example:
```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.16.0 coq-mathcomp-ssreflect.1.15.0 \
 coq-mathcomp-algebra coq-mathcomp-finmap.1.5.2 \
 coq-mathcomp-analysis.0.5.4 coq-mathcomp-zify coq-record-update
```

Then, run `make` in the project root directory. This will check all the definitions and proofs.

## Contents

The project includes: 
- an abstract and timed specification in Coq of the Algorand consensus protocol as a transition system, including node-level behavior, asynchronous messaging and a model of the adversary,
- a **complete** formal proof of _asynchronous safety_ for the transition system.

For more details on the formalization, see the report:

<img src="resources/pdf-icon.png" alt="PDF" width="2%" /> *[Modeling and Verification of the Algorand Consensus Protocol](https://github.com/runtimeverification/algorand-verification/blob/master/report/report.pdf)*

Statements of some _liveness_ properties for the transition system are also provided, but these are work-in-progress and their proofs are currently **incomplete**.  

All Coq source files can be found under the `theories` directory, and their content is as follows:

- `fmap_ext.v`: auxiliary definitions and results on finite maps
- `algorand_model.v`: definition of the Algorand local state, global state, and transition system, along with helper functions and facts
- `safety_helpers.v`: helper functions and lemmas used when proving safety of the transition system
- `quorums.v`: definitions and hypotheses about quorums of nodes
- `safety.v`: statement and complete formal proof of safety for the transition system
- `liveness.v`: an initial attempt at specifying liveness properties for the transition system. This part is work-in-progress and thus the file contains incomplete (admitted) proofs.

## Help and Feedback

Feel free to report GitHub issues or to contact us at: contact@runtimeverification.com
