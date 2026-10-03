[![](logo.svg)](https://axiommath.ai/)

# Exceptional Bondal–Thomsen Collections

This is a Lean formalization of the main results of Reginald Anderson, *Exceptionality, strongness, and asymptotic rarity for the Bondal–Thomsen collection* (preprint). Theorem numbers refer to that paper.

## Main Results

**Theorem 1.2** (exceptionality). Let $X$ be a smooth projective toric Fano variety over an algebraically closed field $k$ of characteristic zero, with Bondal–Thomsen collection $\Theta_X$. The following are equivalent:

1. $\Theta_X$ admits an exceptional ordering;
2. $\mathrm{Ext}^q(L, M) = 0$ for all $L, M \in \Theta_X$ and $q > 0$;
3. $\Theta_X$ admits a full strong exceptional ordering.

Here $X$ is the toric scheme of its fan, Ext is taken among sheaves of modules on $X$, and the bounded derived category $D^b(X)$ is modelled by complexes with bounded coherent cohomology.

**Theorem 1.3** (rarity). Let $k$ be any field, $T_n$ the set of smooth projective toric Fano $n$-folds over $k$ up to toric isomorphism, and $G_n \subseteq T_n$ those whose $\Theta_X$ admits a full strong exceptional ordering. For some $C > 0$ and all large $n$,

$$\\#G_n \le e^{Cn}, \qquad \\#T_n \ge \exp\bigl(n \\, \log \\, n - 2n \\, \log \\, \log \\, n - Cn\bigr),$$

so $\\#G_n / \\#T_n \to 0$. This disproves the nonvanishing part of Conjecture 6.1 of [Ramirez–Zhang–Son–Anderson](https://arxiv.org/abs/2410.23290).

## Assumptions

Theorem 1.2 assumes one published result, taken as an explicit hypothesis in [BondalThomsen/Cited.lean](BondalThomsen/Cited.lean):

> For every smooth complete toric variety $X$ over $k$, $\Theta_X$ classically generates $D^b(X)$.

This is Corollary D of Hanlon–Hicks–Lazarev, *Resolutions of toric subvarieties by line bundles and applications*, Forum Math. Pi **12** (2024), e24. Theorem 1.3 is unconditional. Both use only Lean's three standard axioms.

See [§Formal Challenge](#formal-challenge) for a formal certificate.

## Dependencies

This depends on [Mathlib](https://github.com/leanprover-community/mathlib4), and adapts code from:

* [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti): toric cones, fans and toric schemes; sheaf cohomology; invertible sheaves, Cartier divisors and Picard groups.
* [frenzymath/MiyaokaMori-CharZero](https://github.com/frenzymath/MiyaokaMori-CharZero): curve degrees, nefness and ampleness.
* [apnelson1/Matroid](https://github.com/apnelson1/Matroid): matroid minors, representations and duality.
* [Vilin97/lean-pool](https://github.com/Vilin97/lean-pool): binomial bounds, supporting hulls, closedness of finitely generated cones (by Juan Pablo Traverso Gianini), and a first-cohomology cokernel.
* [boonsuan/nivat](https://github.com/boonsuan/nivat): a common-denominator lemma.
* Individual lemmas from [akopjan/NRR-AAK](https://github.com/akopjan/NRR-AAK), [akopjan/HamSandwich](https://github.com/akopjan/HamSandwich), [openai/ten-proofs](https://github.com/openai/ten-proofs), [MinusGix/flean](https://github.com/MinusGix/flean), [marcmorningstar/lean4-ergodic-theory](https://github.com/marcmorningstar/lean4-ergodic-theory), [bryangingechen/CombinatorialRigidity](https://github.com/bryangingechen/CombinatorialRigidity) and [mccorvie/classification-of-surfaces](https://github.com/mccorvie/classification-of-surfaces).

## Formal Challenge

[Challenge/Basic.lean](Challenge/Basic.lean) states the results above with `sorry` proofs, plus checks that the hypotheses of Theorem 1.2 are satisfiable and that each $T_n$ is finite and eventually nonempty. It depends only on Mathlib and [Challenge/Defs](Challenge/Defs), verbatim copies of the library's definitions. To verify it with [comparator](https://github.com/leanprover/comparator):

```
lake env comparator Comparator/comparator.json
```

This repository has been locally verified with comparator.
