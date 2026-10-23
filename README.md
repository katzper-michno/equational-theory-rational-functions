# The equational theory of rational string-to-string functions

Mikołaj Bojańczyk, Kacper Lewandowski, Katzper Michno

This repository accompanies the paper *The equational theory of rational string-to-string
functions*. It contains a Lean 4 formalisation of its results, which is submitted to the
[Lax archive](https://laxarchive.org) as `lax-149335`.

## The result

The paper gives a sound and complete equational axiomatisation of the rational
string-to-string functions, one of the central classes in the theory of transducers. The
axioms are stated over a compositional, algebraic syntax for rational functions: *rational
terms* $f : A \to B$ between types built from $1$, $\times$, $+$ and lists $A^*$, generated
by finitely many atomic functions under composition and functoriality. The axiomatisation
is finitary, as it consists of finitely many uniform families of axioms, each parameterised
by the types involved, and purely equational, with no implication rules. The main theorem
says that two rational terms denote the same function if and only if they are provably
equivalent.

## Repository layout

The repository root is the Lax submission folder.

- `concepts/` — the concept package `Lax149335`: one module per definition or result of the
  main part of the paper. Each module gives the natural-language statement together with its
  Lean encoding; definitions are Lean definitions, and every result is an `axiom` (a
  *statement*) that contains no proof. These files are the part that a reader has to check
  against the paper.
- `proofs/` — the proof package `Lax149335Proofs`, which proves the statements. The
  annotated proofs, one per statement, are in `proofs/Lax149335Proofs/Results/`. Each of
  them derives its statement from the statements of the results that the paper's proof
  uses, so the proof network on the Lax website follows the structure of the paper.
- `manifest.yaml`, `abstract.md`, `LICENSE` — the submission metadata.

## Building

The formalisation uses the Lax archive environment: Lean `v4.33.0` and mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`. With the [Lax CLI](https://github.com/lax-archive/lax)
installed (`npm install -g lax-archive`, then `lax doctor`):

```
lax build      # builds and validates both packages
lax serve      # previews the submission's pages locally
```

Alternatively, run `lake build` in `concepts/` and then in `proofs/`.

The GitHub Action `.github/workflows/lax-build.yml` runs `lax build` on pushes to `main` and
on pull requests that change the Lean submission.

## Status

Every definition and result of the main part of the paper is formalised, and every result
is proved except **Theorem 3.2** (expressive completeness: every rational function is
defined by a rational term). It concerns the transducer model rather than the equational
theory, and nothing else depends on it, so it is recorded as an open statement.

The table refers to the numbering of the current version of the paper. The last column lists
the results whose statements the annotated proof uses.

| Paper | Concept (`concepts/Lax149335/`) | Proof uses |
| --- | --- | --- |
| Definitions 2.2, 2.4 (types, finite alphabets) | `Types` | |
| Definitions 2.1, 2.3 (rational functions) | `RationalFunctions` | |
| Definition 2.5 (simple rational functions) | `SimpleRationalFunctions` | |
| Theorem 2.6 (conjugacy completeness) | `ConjugacyCompleteness` | |
| Claim 2.7 | `SynchronisedLengths` | |
| Corollary 2.8 (decidability) | `DecidableEquivalence` | |
| Theorem 2.9 (simplification of rational terms) | `Simplification` | 7.7 |
| Definition 3.1, Figure 1 (rational terms) | `Terms` | |
| Theorem 3.2 (expressive completeness) | `ExpressiveCompleteness` | *open* |
| derived terms, Definition 5.1 (values) | `DerivedTerms` | |
| the axioms, the bundle term | `EquationalTheory` | |
| Theorem 4.1 (finite axiomatisation) | `FiniteAxiomatisation` | 5.5, 5.6, 6.1, 7.7 |
| Lemma 5.2 | `ValueConcatenation` | |
| Lemma 5.3 | `ValueNormalisation` | |
| Definition 5.4 | `InjectiveTerms` | |
| Lemma 5.5 | `Cancellation` | |
| Lemma 5.6 | `StringRepresentations` | |
| simple rational terms as rational terms, conjugacy | `SimpleRationalTerms` | |
| Lemma 6.1 | `SimpleCompleteness` | 5.5, 6.2, 6.4, 6.5, 6.7 |
| Lemma 6.2 | `ConjugacyRule` | |
| Definition 6.3 | `GuardedTerms` | |
| Lemma 6.4 | `GuardedReduction` | |
| Lemma 6.5 | `NonemptyReduction` | 6.6 |
| Claim 6.6 | `EmptySummands` | |
| Lemma 6.7 (bundles) | `BundleLemma` | 5.6 |
| Definition 7.1, Table 1 (lifts and drops) | `LiftsAndDrops` | |
| Lemma 7.2 | `LiftInverses` | |
| Lemma 7.3 | `JointSimplification` | |
| Lemma 7.4 | `LiftDropFactorisation` | 7.5 |
| Lemma 7.5 (exchange) | `Exchange` | |
| Corollary 7.6 | `AperiodicCompleteness` | 5.5, 5.6, 6.1, 7.2, 7.3, 7.4 |
| Theorem 7.7 (provable simplification of rational terms) | `ProvableSimplification` | 7.3 |

## Formalisation choices

The *Formalization notes* sections of the concept files record where a statement deviates
from the paper. In short:

- **Corollary 2.8** is stated as: two simple rational terms define the same function if and
  only if they agree on an explicit finite set of test inputs, of size at most the size of
  the input type. This gives the decision procedure; running time is not expressible.
- **Lemmas 6.4 and 6.5** are "without loss of generality" steps; they are stated as
  reductions of the conjugacy rule, with the bound on the list nesting depth that the
  induction of Lemma 6.1 needs.
- **Lemma 6.2** is stated for an arbitrary term and value, and **Lemma 6.7** with a bundle
  size that does not depend on the type; both are stronger than in the paper.
- The inverse `unpref` of prefix multiplication and the bundle term of the window axiom are
  defined explicitly, as in the appendix. Naturality of prefix multiplication is derivable
  and is not an axiom.
- The appendix results needed by the proofs (the exchange lemmas, drop normalisation and
  simplification, the bundle lemma, the group exchange, Simon lift and group injection
  lemmas, value extraction, unprefixing) are proved in `proofs/Lax149335Proofs/Appendix/` as
  auxiliary lemmas.

## Layout of the proof package

The proof development is organised by the part of the paper it formalises:
`RationalFunctions/` (Section 2), `Terms/` (Section 3), `EquationalTheory/` (Section 4),
`Preliminaries/` (Section 5), `SimpleCompleteness/` (Section 6), `GeneralCompleteness/`
(Section 7), `Appendix/` (the appendix), and `Results/` (the annotated proofs).
`Bridge.lean` makes the definitions of the concept package available in the proof
development under their short names (`Ty`, `Term`, `PEq`, …).

## Provenance

The original version of this formalisation was edited by
[Aristotle](https://aristotle.harmonic.fun) (Harmonic).

## License

Apache License 2.0, see `LICENSE`.
