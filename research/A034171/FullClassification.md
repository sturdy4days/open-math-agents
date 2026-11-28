# The A034171 congruence

Let $a(n)$ denote OEIS A034171 with its registered offset $1$. For every prime $p\equiv1\pmod 3$ and every positive integer $n$, the factorial quotient satisfies

$$
a(pn)\equiv(-3)^{n(p-1)/2}\,a(n)\pmod{p^2}.
$$

If $3^{p-1}\equiv1\pmod{p^2}$, Peter Bala’s proposed congruence holds for every positive index. At every other eligible prime it fails exactly at the indices whose units digit in base $p$ is nonzero and whose base-$p$ digits are all at most $d=(p-1)/3$.

The exclusions in the OEIS statement cover all failing indices below $p^2$. When the prime fails the base-three Wieferich test, the first unexcluded failure is $p^2+1$, and every $p^j+1$ for $j\ge2$ is another. For $s\ge1$, there are exactly $d(d+1)^{s-1}$ failures in $1\le n<p^s$, counting the excluded indices. The units digit has $d$ choices and each of the other $s-1$ digits has $d+1$.

| Prime | Multiplier $a(p)\bmod p^2$ | First unexcluded failure |
| --- | --- | --- |
| 7 | 22 | 50 |
| 13 | 53 | 170 |
| 1,006,003 | 1 | The congruence holds at every index |

At $p=7$, $a(50)\equiv17$ and $a(350)\equiv31\pmod{49}$. The counterexample at $n=50$ was reported by @Solfanbtc. The registered Lean statement was formalized by @Nealanio.

## Proof

Normalize the coefficients by $b(0)=1$ and $b(n)=3a(n)$ at positive indices. Their integral generating series $B$ satisfies $(1-9X)B^3=1$. Over the prime field, Frobenius gives $B(X)=(1-9X)^d B(X^p)$. Each base-$p$ digit $r$ contributes $(-9)^r\binom{d}{r}$, which gives the support criterion.

Separate the factors divisible by $p$ in each block of the factorial quotient. Pairing unit residues with their opposites removes the block translations modulo $p^2$, which gives $a(pn)\equiv a(p)^n a(n)$. To evaluate $a(p)$, expand the unit product to first order and use the signed binomial sum over indices divisible by three. In the group ring of the cyclic group of order three, its generator $X$ satisfies $(1-X)^7=-27(1-X)$. Taking the coefficient of the identity in $(1-X)^p$ gives the reciprocal sum that evaluates the multiplier.

## Lean verification

FullClassification.lean imports the registered article and Mathlib. It contains the complete proof in one file. The corrected prime-square formula is TripleFactorial.explicit_lift. BalaWieferich.exact_failure gives the digit criterion. TripleFactorial.universal_iff_wieferich and TripleFactorial.first_failure_at_square_plus_one give the all-index test and least unexcluded failure. TripleFactorial.at_1006003 verifies the positive example in the table.
