# Algorand verification

A Coq formalization of Algorand.

Requirements
------------

- [`Coq 8.9`](https://coq.inria.fr)
- [`Mathematical Components 1.7`](https://math-comp.github.io/math-comp/) (`ssreflect` suffices)

Building
--------

We recommend installing the dependencies of the project via
[OPAM](http://opam.ocaml.org/doc/Install.html):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect coq-interval coq-mathcomp-finmap
```
