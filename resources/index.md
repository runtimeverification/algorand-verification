---
title: Algorand Verification
lang: en
header-includes:
  - |
    <style type="text/css"> body {font-family: Arial, Helvetica; margin-left: 5em; font-size: large;} </style>
    <style type="text/css"> h1 {margin-left: 0em; padding: 0px; text-align: center} </style>
    <style type="text/css"> h2 {margin-left: 0em; padding: 0px; color: #580909} </style>
    <style type="text/css"> h3 {margin-left: 1em; padding: 0px; color: #C05001;} </style>
    <style type="text/css"> body { width: 1100px; margin-left: 30px; }</style>
---

<div style="text-align:left"><img src="https://github.githubassets.com/images/modules/logos_page/Octocat.png" height="25" style="border:0px">
[View the project on GitHub](https://github.com/runtimeverification/algorand-verification)
<img src="https://github.githubassets.com/images/modules/logos_page/Octocat.png" height="25" style="border:0px"></div>

## About

Welcome to the Algorand Verification project website!

The Algorand consensus protocol is the foundation of a decentralized
digital currency and transactions platform. This project provides a
model of the protocol in Coq, expressed as a transition system over
global states in a message-passing distributed system. Included is
a formal proof of safety for the transition system.

This is an open source project, licensed under the University of Illinois/NCSA Open Source License.

## Get the code

The latest release of Algorand Verification can be [downloaded from GitHub](https://github.com/runtimeverification/algorand-verification/releases).

## Documentation

Generated HTML documentation is available for source files in the latest release:

- [fmap_ext.v](docs/latest/coq2html/Algorand.fmap_ext.html): auxiliary definitions and results on finite maps
- [algorand_model.v](docs/latest/coq2html/Algorand.algorand_model.html): definition of the Algorand local state, global state, and transition system, along with helper functions and facts
- [safety_helpers.v](docs/latest/coq2html/Algorand.safety_helpers.html): helper functions and lemmas used when proving safety of the transition system
- [quorums.v](docs/latest/coq2html/Algorand.quorums.html): definitions and hypotheses about quorums of nodes
- [safety.v](docs/latest/coq2html/Algorand.safety.html): statement and complete formal proof of safety for the transition system

## Help and contact

- Report issues on [GitHub](https://github.com/runtimeverification/algorand-verification/issues)

## Authors

- Musab A. Alturki
- Jing Chen
- Victor Luchangco
- Brandon Moore
- Karl Palmskog
- Lucas Peña
- Grigore Roșu
