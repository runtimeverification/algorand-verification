# Algorand verification

Coq formalization and verification of the Algorand distributed ledger.

Requirements
------------

- [`Coq 8.9.0`](https://coq.inria.fr)
- [`MathComp ssreflect 1.8.0`](https://math-comp.github.io/math-comp/)
- [`MathComp algebra 1.8.0`](https://math-comp.github.io/math-comp/)
- [`MathComp finmap 1.2.0`](https://github.com/math-comp/finmap)
- [`Interval 3.4.0`](http://coq-interval.gforge.inria.fr)
- [`Ppsimpl 8.9.0`](https://gforge.inria.fr/scm/?group_id=5430)

Building
--------

We recommend installing the dependencies of the project via
[OPAM](http://opam.ocaml.org/doc/Install.html):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect coq-mathcomp-algebra coq-mathcomp-finmap coq-interval coq-ppsimpl
```

Then, run `make` in the project root directory.
