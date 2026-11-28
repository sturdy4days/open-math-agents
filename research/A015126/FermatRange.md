# When an odd number is its own least totient preimage

Write $a(x)$ for the least nonnegative integer $y$ with $\varphi(y)=\varphi(x)$. If $x$ is odd and $\varphi(x)=2^m$, then **$a(x)=x$**. For example, $\varphi(255)=128$, and its unique odd preimage is $255=3\cdot5\cdot17$. This gives a positive case of Jianing Song’s conjecture alongside the signed counterexample to its unrestricted form. [OEIS A015126](https://oeis.org/A015126) · [Original counterexample](https://github.com/sturdy4days/open-math-agents/blob/5ed21d3956316fa845be1a797ecaf97d6feff6a4/proofs/oeis-a015126.lean)

For an odd prime power $p^e$ dividing $x$ exactly, $(p-1)p^{e-1}$ divides $\varphi(x)$. Thus $e=1$ and $p=2^u+1$. The primality of $p$ forces $u=2^i$ for some $i$. Consequently $x$ is a product of distinct Fermat primes $F_i=2^{2^i}+1$. If $S$ is their index set, then $m=\sum_{i\in S}2^i$. The binary expansion of $m$ determines $S$, so there is at most one odd preimage of $2^m$.

To compare that preimage with even ones, take $h$ larger than every index in $S$. Each factor below exceeds one, and the product over the entire range telescopes.

$$
\frac{x}{\varphi(x)}
=\prod_{i\in S}(1+2^{-2^i})
\leq \prod_{i=0}^{h-1}(1+2^{-2^i})
=2(1-2^{-2^h})<2.
$$

For even $y$, at most half the residues modulo $y$ are coprime to $y$. In particular, any even preimage of $\varphi(x)$ satisfies $y\geq 2\varphi(x)>x$. Together with uniqueness among odd preimages, this proves the claim, including $x=1$.

The standalone Lean proof uses the registered definition of `aSeq`. Its main theorem is `OMA.S_oeis_a015126.aSeq_eq_self_of_odd_totient_dvd_two_pow`, stated with the equivalent hypothesis that the positive totient divides some power of two. The nine axiom audits at the end of the file check the named results using only `propext`, `Classical.choice`, and `Quot.sound`. [Lean proof](FermatRange.lean)
