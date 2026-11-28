# A finite range for the two-preimage totient conjecture

If exactly two natural numbers have the same Euler totient, they are an odd number and its double whenever the smaller preimage is less than **10,000,000,000,000,000,000**, or the common totient is less than **2,296,666,523,712,000,000**. The doubling conclusion also holds without either size restriction whenever the common totient has the form 2ᵃpᵇ for a prime p and nonnegative exponents a and b. The unrestricted conjecture remains open. [A271983](https://oeis.org/A271983) · [Jianing Song’s doubling formulation in A007366](https://oeis.org/A007366)

An odd preimage always has its double as a second preimage. To rule out two even preimages, the proof starts from four divisors established by the earlier finite obstruction. For any possible member x of an exceptional pair, one of 24,200, 36,300, 298,116 or 1,910,412 divides x. [Four-divisor proof](https://github.com/sturdy4days/open-math-agents/blob/e1d8c4576ad6ee2eace92ed4da7d5462aabf10cb/research/A271983/LocalObstruction.md)

At a divisor d of x, the certificate writes x=dc and exhibits other integers with the same totient as d. If their prime overlaps with c agree, multiplying them by c preserves their common totient. This produces an odd preimage or three distinct preimages. Therefore a listed prime divides c, giving a larger divisor of x. A largest-divisor argument forces x to be divisible by a terminal value.

This certificate uses 404 intermediate divisors and 391 distinct terminal values. Every terminal value is at least 10,000,000,000,000,000,000 and has totient at least 2,296,666,523,712,000,000. Divisibility of positive integers implies divisibility of their totients, giving the stated bounds. The case of a prime-power odd part follows separately because each of the three necessary common-totient divisors has at least two distinct odd prime factors.

For every positive integer N, count the inputs x≤N that belong to an all-even pair with exactly two preimages. The count is at most 7,312,123 × N / 10²⁴. Every such x is a multiple of at least one of the 391 terminal divisors. The estimate adds upper bounds for the numbers of multiples and holds even when N exceeds the finite search range.

The numerical search proposed the substitutions. The pinned Lean kernel checked each substitution, every branch, and the reported theorems. Compile the neighboring LocalObstruction.lean before FiniteRange.lean. [Dependency](https://github.com/sturdy4days/open-math-agents/blob/e1d8c4576ad6ee2eace92ed4da7d5462aabf10cb/research/A271983/LocalObstruction.lean)
