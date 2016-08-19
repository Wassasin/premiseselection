# Data used
For this thesis several datasets were used. Because some libraries have grown and changed considerably over the years, the version used is of tremendous importance to the generated dataset and the resulting performance.

In order to extract the required data some patches need to be applied to the projects, and some dependencies need to be installed. In this document I attempt to give a complete as possible set of instructions on how to reproduce the datasets used.
This is useful if you wish to run the toolchain on a different library (or a different version of previously used libraries), but also if you want to reproduce the results in this thesis.

It takes quite a bit of time and resources to generate the datasets.
For your convenience the generated dataset is also hosted online.

# System
These instructions have been tested with:
* Ubuntu 15.04

# Dependencies
```
# apt-get install ocaml opam
```

Initialize opam if you haven't yet, and follow the instructions.
```
$ opam init
```

```
$ COQ_XML=-xml COQ_XML_LIBRARY_ROOT=../../../xml/math-comp COQBIN=../../coq/bin/ COQLIBS="-coqlib ../../coq -R . mathcomp" make
```
