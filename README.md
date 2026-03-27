# Definitional Proof Irrelevance Made Accessible

This artifact is split in three components:

- rocq-prototype contains a fork of The Rocq Prover, with support for rewrite rules that can be enabled in proof terms only.
  Its README is at the root, and redirects to INSTALL.md (also at the root) for installation guidance.
- Acc_in_Action contains examples to test the prototype on.
- rocq-formalisation is a Rocq development which formalises the equivalence between T≡ and T= as extensions of CICobs.
  It was written with Rocq 9.0.1, the libraries it requires are listed in its README (at the root).

## Formalisation

(extracted from [its README.md file](rocq-formalisation/README.md))

This repository contains the formalization of most proofs given in the paper.

[See the rendered Rocq code, with comments.](https://yann-leray.github.io/acc-in-sprop)

### Building

You need the the Rocq Prover 9.0.1 and Autosubst 2 OCaml (needs ocaml<5, recommended 4.14.2).
Note that the prototype does not provide a version of Rocq suitable for compiling the formalisation.
You can install
them using
```sh
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only .
```
(there will be warnings about the opam file that can be safely ignored)

Then to verify the proof, just use `make`:
```sh
make autosubst
make   # you may add -j JOBS to compile faster
```

For the overview of all files in the formalisation, go to [the README in the folder](rocq-formalisation/README.md)


## Prototype
(extracted from [its INSTALL.md file](rocq-prototype/README.md))

To install and use this fork of Rocq, we recommend using the opam package manager.
To install Rocq in an OPAM switch, follow these instructions:

```sh
opam pin add . -n
# Register the packages here but don't install, they are not all needed

opam repo add rocq-core-dev https://rocq-prover.org/opam/core-dev
# Necessary for the standard library with this development version

opam install rocq-prover
# Make sure opam installs rocq-stdlib.dev and not rocq-stdlib.9.0.0
# You may also want to install rocqide
```

To install additional packages from the Rocq environment:

```sh
opam repo add rocq-extra-dev https://rocq-prover.org/opam/extra-dev
# The repository where most development versions are available

opam install <package>
# e.g. rocq-equations (*) or vsrocq-language-server
```

(*) Note that these packages are kept in sync with the development version of Rocq,
so they may become incompatible with this prototype fork.

If so, you can go to the development repo of the package, find the latest commit before
2026-01-20 and use opam to pin the package to the specific commit.
For instance, for equations, `opam pin add rocq-equations "git+https://github.com/mattam82/Coq-Equations.git#757662b9c875d7169a07b861d48e82157520ab1a"`


## Examples

The file `Acc_in_Action/gcd.v` contains the evaluation of the gcd
function with Acc in SProp (both with autorewriting and use of conversion).

The file `Acc_in_Action/gcd_Prop.v` contains the evaluation of the gcd
function with Acc in Prop.

The file `Acc_in_Action/SystemF_SProp.v` contains the evaluation of
the evaluator for System with Acc in SProp (both with autorewriting and use of conversion).

The file `Acc_in_Action/SystemF_Prop.v` contains the evaluation of
the evaluator for System with Acc in Prop.

To make intiial compilation fast, some of the tests are commented out,
uncomment them if you want to run them. 

To test files, you need to enable rewrite rules in Rocq.
This is generally done by passing the command-line flag `-allow-rewrite-rules`
to the program running Rocq (it can be rocq itself, rocqide, vscoqtop, coq-lsp, etc.)
For tools which recognise `_CoqProject` files (all but `rocq compile`), the argument will be added by it automatically.

Otherwise, for rocq or rocqide, simply pass the flag to the command line.
For VSCode integration, there should be an "args" setting in the extension to pass additional command-line arguments.
For Proof General, there should be a variable called PG-prog-args to pass the flag (not tested).
In any case, ensure you are using the prototype and not falling back to another installation of Rocq.
