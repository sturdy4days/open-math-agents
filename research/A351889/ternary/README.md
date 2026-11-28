# Periods of multinacci sequences modulo powers of three

For every width $n\ge 2$, the period $T(n,3)$ of the window initialized with $n-1$ zeros and one is coprime to three. For every exponent $r\ge 1$,

$$T(n,3^r)=3^{r-1}T(n,3).$$

The computation applies to the actual sequence and eventual-period definition in A351889. If $q=3^k$ with $k\ge 1$, the base periods are $q^2-1$ at width $q-1$ and $q^2+q+1$ at width $q$. Consequently the latter formula proves the case $p=3$ of Chai Wah Wu’s third A351889 conjecture. The signed A210456 proof establishes Fred W. Helenius’s digital-root formulas at modulus nine. [A351889](https://oeis.org/A351889) · [A337212](https://oeis.org/A337212) · [Signed A210456 proof](https://github.com/sturdy4days/open-math-agents/blob/81f10f968e4e6e6953a0fd1198a30a743e2c9f6b/proofs/oeis-a210456.lean)

The proof relates eventual periods to polynomial divisibility. The recurrence denominator over the field with three elements has simple roots at every width. Hence the least period modulo three has no factor of three. Over the integers modulo nine the companion matrix and its cube have different traces. The matrix Euler–Fermat congruence then forces a factor of three in every period. Matt Gaiser’s proof of Wu’s conditional lifting conjecture determines all higher powers. [Florian Luca, Lemma 2.1(iv)](https://www.fq.math.ca/Papers/59-4/luca10142020.pdf) · [V. I. Arnold, The matrix Euler–Fermat theorem](https://doi.org/10.1070/IM2004v068n06ABEH000510) · [Matt Gaiser’s A351889 proof](https://github.com/lefttosolve2/open-math-agents/pull/31755)

The special widths use classical difference sets in finite fields. The quadratic case uses an affine trace-one line. The cubic case uses quotients of elements of a projective line. The source credits the original sequence authors, the conjecture authors and the underlying finite-field results. [Dieter Jungnickel, RICAM 2013, slide 15](https://www.ricam.oeaw.ac.at/specsem/specsem2013/tutorials-lectures/slides/specialdays/jungnickel_1.pdf) · [Mészáros, Rónyai and Szabó, Corollary 1.2](https://arxiv.org/abs/1908.05591)

## Reproduction

Use Lean 4.33.1 with Mathlib at commit `0df444a360eaa60ab8c11dca51a86af692955474`. From the configured Mathlib project, run `lake env python3 /absolute/path/to/replay.py`. The script downloads the exact registered statement and Matt Gaiser’s proof from immutable GitHub revisions, checks their SHA-256 digests, then compiles them in a temporary directory. It checks the research file and audits eight results in a fresh Lean process. [Registered statement](https://github.com/lefttosolve2/open-math-agents/blob/c6635296758d3877cdad0bcb4d3358a1e7507b32/statements/oeis-a351889.lean) · [Imported proof](https://github.com/MattGaiser/open-math-agents/blob/139cdc3b1cd7ee9382070eafddf16859331991f9/proofs/oeis-a351889.lean)

The file `ModuloNine.lean` imports only the registered statement and proves `Multinacci351889.nine_direct` at every width from 2 onwards. The file `TernaryPeriods.lean` uses the external lifting proof for higher powers. The main declarations are `Multinacci351889.ternary_all_widths`, `Multinacci351889.order_prime_to_three`, `Multinacci351889.exact_periods` and `Multinacci351889.wu_third_ternary`.
