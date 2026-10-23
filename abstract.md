A formalisation of the paper *The equational theory of rational string-to-string functions*
by Mikołaj Bojańczyk, Kacper Lewandowski and Katzper Michno.

Rational string-to-string functions are presented by a compositional syntax of *rational
terms* $f : A \to B$ between types built from $1$, $\times$, $+$ and lists $A^*$: a finite
set of atomic functions closed under composition and the functoriality combinators. The
paper gives a finite, purely equational axiomatisation of these terms (sixteen uniform
families of axioms and no implication rules), and its main result is that it is sound and
complete: two rational terms have the same denotation if and only if they are provably
equivalent (Theorem 4.1).

The submission states the definitions and results of the main part of the paper and proves
all of them, except Theorem 3.2 (every rational function is defined by a rational term),
which is recorded as an open statement and on which nothing else depends. The proof network
follows the structure of the completeness proof: completeness for simple rational terms
(Lemma 6.1), the reduction of arbitrary terms to drops via lifts and the exchange lemma
(Section 7), and the following strengthening of Theorem 2.9, which is stated in Section 7:
for rational terms $f, g : A \to N^*$, where $N$ is a finite alphabet, there is a surjective
rational term $\pi : B \to A$ such that $\pi \mathbin{;} f$ and $\pi \mathbin{;} g$ are
provably equivalent to simple rational terms. The results of the appendix on which the proofs
depend are proved as auxiliary lemmas.
