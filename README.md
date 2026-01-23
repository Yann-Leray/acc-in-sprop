# Formalization for the paper "Definitional Proof Irrelevance Made Accessible"

This repository contains the formalization of most proofs given in the paper.

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



## Overview

### Syntax 

We specify the common syntax for the theories $\mathcal{T}_=$ and $\mathcal{T}_\equiv$ in [AST.sig](theories/autosubst/AST.sig),
which is used by Autosubst to automatically generate the syntax and notions of renaming and substitutions, along with their respective laws. The [autosubst](theories/autosubst/) directory also contains some custom non-automatically generated files, like [RAsimpl.v](doc/coqdoc/AccInSProp.theories.autosubst.RAsimpl.html) which defines a faster substitution simplification tactic, and [SubstNotations.v](doc/coqdoc/AccInSProp.theories.autosubst.SubstNotations.html) which specifies some notations.


### Preliminary files

- [BasicAST.v](doc/coqdoc/AccInSProp.theories.BasicAST.html): Definition of universe levels and of its basic operations

- [Util.v](doc/coqdoc/AccInSProp.theories.Util.html): General tactics, lemmas and notations.

- [Typing.v](doc/coqdoc/AccInSProp.theories.Typing.html): Typing rules of $\mathcal{T}_=$ and $\mathcal{T}_\equiv$. We use a single mutual inductive family parametrized by a mode `M`, which can be either `mdef` for the definitional theory ($\mathcal{T}_\equiv$), or `mprop` for the propositional theory ($\mathcal{T}_=$). The rule for `accelcomp` then requires a proof that `M = mdef`. We also assume a `Parameter assm_sig : list term` for representing the signature of axioms $\Sigma$, and suppose that the type of an axiom is well typed in $\mathcal{T}_=$ if it is well-typed in $\mathcal{T}_\equiv$. This assumption is of course validated by the common axioms one uses in practice, such as propositional extensionality, functional extensionality, excluded middle and various forms of choice.

- [BasicMetaTheory.v](doc/coqdoc/AccInSProp.theories.BasicMetaTheory.html): Basic metatheoretic properties of the two systems, including stability under weakening and substitution, validity, type inversion and some more economical versions of the typing and conversion rules.

- [AccConstructions.v](doc/coqdoc/AccInSProp.theories.AccConstructions.html): Working internally to $\mathcal{T}_\equiv$ or $\mathcal{T}_=$, we show that the usual elimination principle for accessibility can be derived from the weaker one we have in the definition of the theories.

### Canonicity of $\mathcal{T}_\equiv$

- [Reduction.v](doc/coqdoc/AccInSProp.theories.Reduction.html): Definition of a typed and deterministic weak-head reduction relation for $\mathcal{T}_\equiv$, needed for defining the logical relation. We also prove some of its basic properties.

- [LRDef.v](doc/coqdoc/AccInSProp.theories.LRDef.html): Definition of the logical relation for proving canonicity of $\mathcal{T}_\equiv$. We use a module to hide the definition of the logical relation, which has some technical aspects.

- [LRBasicProps.v](doc/coqdoc/AccInSProp.theories.LRBasicProps.html): Basic properties of the logical relation, including escape, closure under reduction and anti-reduction, stability under annotation exchange, inversion, irrelevance, symmetry and transitivity. We also extend the logical relation to substitutions, define validity, and prove that they both also satisfy symmetry and transitivity.

- [FundamentalAux.v](doc/coqdoc/AccInSProp.theories.FundamentalAux.html): Auxiliary lemmas for proving the fundamental theorem of the logical relation.

- [FundamentalPi.v](doc/coqdoc/AccInSProp.theories.FundamentalPi.html), [FundamentalNat.v](doc/coqdoc/AccInSProp.theories.FundamentalNat.html), [FundamentalAcc.v](doc/coqdoc/AccInSProp.theories.FundamentalAcc.html), [FundamentalCast.v](doc/coqdoc/AccInSProp.theories.FundamentalCast.html): Cases of proof of fundamental theorem for function types, natural numbers, accessibility and observational equality. As explained in the paper, the proofs for accessibility and observational equality rely on some assumptions which are provable in set theory by constructing the standard model of $\mathcal{T}_\equiv$.

- [Fundamental.v](doc/coqdoc/AccInSProp.theories.Fundamental.html): Proof of the fundamental theorem of the logical relation. As a corollary, we derive canonicity for $\mathcal{T}_\equiv$.

- [CompCanonicity.v](doc/coqdoc/AccInSProp.theories.CompCanonicity.html): Proof of computational canonicity for $\mathcal{T}_\equiv$, in which the natural number is computed through untyped reduction of the erasure of the term.


### Conservativity of $\mathcal{T}_\equiv$ over $\mathcal{T}_=$


- [HEq.v](doc/coqdoc/AccInSProp.theories.HEq.html): Definition of heterogeneous equality in $\mathcal{T}_=$ and proofs of its important properties. To make the proofs practically feasible, here we work internally to the object theory: we postulate sufficiently many primitives to turn Rocq into a proof assistant for $\mathcal{T}_=$.

- [CHEqProps.v](doc/coqdoc/AccInSProp.theories.CHEqProps.html): Postulates of the external versions of the terms and proofs constructed internally in the file [HEq.v](doc/coqdoc/AccInSProp.theories.HEq.html).

- [CDecoration.v](doc/coqdoc/AccInSProp.theories.CDecoration.html): Definition of the decoration relation and proof of the fundamental lemma of the translation, stating that related well-typed terms in $\mathcal{T}_=$ are heterogeneously equal.

- [CTranslation.v](doc/coqdoc/AccInSProp.theories.CTranslation.html): Proof of the decorating translation from  $\mathcal{T}_\equiv$ to $\mathcal{T}_=$. As a corollary, we deduce the conservativity of $\mathcal{T}_\equiv$ over $\mathcal{T}_=$. Combined with the result of [CompCanonicity.v](doc/coqdoc/AccInSProp.theories.CompCanonicity.html), we derive propositional canonicity for $\mathcal{T}_=$.


### Set theoretic model

Higher-order IZF_R with omega universes:

- [ZF_axioms.v](doc/coqdoc/AccInSProp.theories.SetModel.ZF_axioms.html): axioms

- [ZF_library.v](doc/coqdoc/AccInSProp.theories.SetModel.ZF_library.html): unions, cartesian products, function sets, dependent function sets

- [ZF_nat.v](doc/coqdoc/AccInSProp.theories.SetModel.ZF_nat.html): set-theoretic natural numbers with large eliminator

- [ZF_acc.v](doc/coqdoc/AccInSProp.theories.SetModel.ZF_acc.html): set-theoretic accessibility predicate with large eliminator

Higher-order model of OTT :

- [HO.v](doc/coqdoc/AccInSProp.theories.SetModel.HO.html): preliminaries

- [HO_univ.v](doc/coqdoc/AccInSProp.theories.SetModel.HO_univ.html): universes

- [HO_prop.v](doc/coqdoc/AccInSProp.theories.SetModel.HO_prop.html): type of propositions with definitional proof irrelevance

- [HO_pi.v](doc/coqdoc/AccInSProp.theories.SetModel.HO_pi.html): proof-relevant dependent products (with beta/eta)

- [HO_sigma.v](doc/coqdoc/AccInSProp.theories.SetModel.HO_sigma.html): dependent sums (with beta/eta)

- [HO_nat.v](doc/coqdoc/AccInSProp.theories.SetModel.HO_nat.html): natural numbers with large eliminator (with beta)

- [HO_box.v](doc/coqdoc/AccInSProp.theories.SetModel.HO_box.html): boxed proposiitons (with eta)

- [HO_false.v](doc/coqdoc/AccInSProp.theories.SetModel.HO_false.html): false proposition (not inhabited in the empty context)

- [HO_forall.v](doc/coqdoc/AccInSProp.theories.SetModel.HO_forall.html): proof-irrelevant dependent products

- [HO_obseq.v](doc/coqdoc/AccInSProp.theories.SetModel.HO_obseq.html): observational equality, cast, cast-on-refl, funext, propext, injectivity of pi, cast-on-functions, no confusion (nat ≠ pi)

- [HO_acc.v](doc/coqdoc/AccInSProp.theories.SetModel.HO_acc.html): accessibility predicate and its eliminator (with beta)
