# Erdős Problem 623 at and below aleph-omega

The project asks whether every function picking a point outside each finite input set admits an infinite independent set at cardinality $\aleph_\omega$. Independence means that every finite subset of the witness is mapped outside the entire witness.

**At the stated cardinal.** `OMA.Erdos623Bridge.exact_iff_koepke` identifies the project's literal proposition with the countable-language structural free-subset property on one representative of $\aleph_\omega$. It uses `type_of%` on the pinned Formal Conjectures declaration. Its axiom audit lists only `propext`, `Classical.choice`, and `Quot.sound`. An independent set can be thinned to a countably infinite one. The structural property passes along every embedding, so a positive answer at $\aleph_\omega$ would give a countably infinite independent set at every larger cardinal in the same universe. [Pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/623.lean)

Sungchul Lee formalized the intermediate equivalences for a well-ordered type. They connect one forbidden output, countably many forbidden outputs, and freeness in a countable first-order language. Peter Koepke's 1984 Theorems 2.2 and 4.4 establish the corresponding relative consistency strength of a measurable cardinal. Lee's paper applies those metatheorems to the positive and negative answers to 623. The Lean replay verifies the mathematical equivalence. The forcing and inner-model arguments are cited results outside the replay. [Lee's pinned sources and paper](https://github.com/lsngchl/Erdos623/tree/fabea68c8296ce1f538e88bf5c8d4a302dc39c32) · [Koepke, 1984](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/consistency-strength-of-the-freesubset-property-for/D2052578B8F129E1211EBB9F6E1D21C1)

**Below the stated cardinal.** Erdős and Hajnal's Theorem 2 is verified in the standalone Mathlib file `ErdosHajnalLower.lean`. On every infinite set of smaller cardinality there exists a map that avoids its own finite input and hits every infinite subset from within. The proof builds a countable-valued obstruction on $\aleph_n$ catching an omitted point in every $(n+1)$-element set. It encodes the index of that point by adding finitely many larger elements to the input. [Erdős and Hajnal, 1958](https://www.renyi.hu/~p_erdos/1958-12.pdf)

**How large can a free set be?** At $\aleph_\omega$ there is an input-avoiding map for which every independent subset is countable and one is countably infinite. This is the sharp upper bound observed by Erdős and Hajnal. For countable-valued maps there is also an exact finite threshold. Every such map on $X$ has an $(n+1)$-element free set if and only if $|X|\geq\aleph_{n+1}$. Here a finite set is free when, for each subset of it, every point forbidden by that subset belongs to the subset or lies outside the free set. `AtAlephOmega.lean` and `SharpArity.lean` give these two proofs using only Mathlib and the lower-cardinal construction.

**A computable example.** On the natural numbers `cardMap` returns the size of its input whenever the size is absent. Otherwise it returns one more than the maximum. A finite set $S$ is free exactly when every element of $S$ is at least $|S|$. There are free sets of every finite size. For every infinite $Y$ and every natural number $j$, some $j$-element subset of $Y$ omitting $j$ maps to $j$.

## Replay

Use the Formal Conjectures, Mathlib and donor revisions in `manifest.json`, Lean 4.33.1 and Python 3.11+. In a built checkout of Formal Conjectures with `FormalConjecturesUtil` available, use `lake env` to run the following. Supply an unused build directory. The donor checkout supplies Lee's source files. The driver checks their original hashes, applies the 4.33.1 compatibility edits, checks the resulting hashes and builds every listed local module. It then audits all 28 endpoints. `ErdosHajnalLower.lean` and `CountableExample.lean` can each be checked independently in Mathlib.

```sh
lake env python3 /path/to/research/Erdos623/replay.py \
  --formal /path/to/formal-conjectures --donor /path/to/Erdos623 \
  --build /tmp/erdos623-replay
```
