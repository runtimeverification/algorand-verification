# Algorand verification

Coq formalization and verification of the Algorand distributed ledger.

Requirements
------------

- [`Coq 8.9.0`](https://coq.inria.fr)
- [`MathComp ssreflect 1.8.0`](https://math-comp.github.io)
- [`MathComp algebra 1.8.0`](https://math-comp.github.io)
- [`MathComp finmap 1.2.0`](https://github.com/math-comp/finmap)
- [`Interval 3.4.0`](http://coq-interval.gforge.inria.fr)
- [`Ppsimpl 8.9.0`](https://gforge.inria.fr/scm/?group_id=5430)

Building
--------

We recommend installing the dependencies of the project via
[OPAM](http://opam.ocaml.org/doc/Install.html):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect.1.8.0 coq-mathcomp-algebra.1.8.0 coq-mathcomp-finmap.1.2.0 coq-interval.3.4.0 coq-ppsimpl.8.9.0
```

Then, run `make` in the project root directory.
