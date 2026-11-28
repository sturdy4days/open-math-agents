# A bound for Noe’s distinct totient preimage

T. D. Noe conjectured that every positive integer n has a different integer m ≤ 2n with φ(m)=φ(n). A failure of this bound could still have a second preimage larger than 2n. The proof below checks the size of each replacement that it uses. [A074987](https://oeis.org/A074987)

## The mathematical bound from Ford’s computation

Applying the factor-two replacement rules to Kevin Ford’s published prime lists gives the following conclusion. **Any exception to Noe’s conjecture exceeds 10^(10,003,700,000).** The numerical products in this deduction come from Ford’s 1996 computation, described in Section 7.3 of *The Distribution of Totients*. The Lean proof verifies the transfer of the rules. The smaller computation below has its own complete kernel certificate. [Ford, Section 7.3, especially after Lemmas 7.2 and 7.4](https://www.ford126.web.illinois.edu/wwwpapers/totients.pdf)

Suppose n is exceptional, write n=d·e·u with gcd(d,eu)=1, and assume every prime divisor of e divides u. For a prime p=1+eφ(d) absent from n, the replacement pu has the same totient. Indeed φ(n)=φ(d)eφ(u)=(p−1)φ(u)=φ(pu). Moreover pu≤2n since φ(d)≤d and e≥1. The two integers are different because p does not divide n.

For the other case, suppose p divides n exactly once and every prime of p−1 divides n. Write n=pv. Each prime of p−1 still divides v, so (p−1)v has totient (p−1)φ(v)=φ(n). This replacement is smaller than n. These two steps force p² to divide an exceptional n under the hypotheses of Ford’s Lemma 7.2. This is an adaptation of the prime-square criterion of Carmichael and Klee that controls the size of the equal-totient witness. [Carmichael, 1922](https://doi.org/10.1090/S0002-9904-1922-03504-5) · [Klee, 1947](https://doi.org/10.1090/S0002-9904-1947-08940-0) · [Schlafly and Wagon, 1994](https://doi.org/10.1090/S0025-5718-1994-1226815-3)

In particular, 2², 3², 7² and 43² divide n. Let k be a product of distinct primes other than 2 or 3 whose squares already divide n. In either case a prime 6k+1 has its square dividing n. When 27 does not divide n the same holds for a prime 12k+1, starting with k=1 and p=13. When 27 divides n it holds for a prime 18k+1, starting with p=19. Ford gives precisely these starting conditions and generation rules. In the first case his computation found 126,520,174 primes, and in the second it found 104,942,148. On page 39 he records that the two products a and b each exceed 10^(5,001,850,000). In the corresponding branch their squares divide n, which gives the displayed bound. [Ford, pp. 38–39](https://www.ford126.web.illinois.edu/wwwpapers/totients.pdf)

## Independent Lean certificate

The accompanying file derives a smaller set of prime squares from the same rules and checks every one inside Lean. It proves the factor-two conjecture for every positive n up to 10^1000. It uses Lucas primality certificates, binary modular exponentiation and multiplication of pairwise coprime divisors. The two forced divisors have 1,020 and 1,026 decimal digits. Every exception is a multiple of one of them. Hence for every N the number of positive inputs up to N that could be exceptions is at most 2⌊N/10^1000⌋. The theorems `NoeCensus.bounded_twin` and `NoeCensus.nontwin_count` express the witness and count directly in the terms of the registered conjecture.

Running `python generate_forcing_tree.py` with SymPy installed reproduces `prime-tree-1000.json`. The standalone Lean source includes the prime certificates and the branches of the divisibility proof. It compiles against the project’s pinned Lean and Mathlib with the registered statement module on the import path.

The unrestricted conjecture remains open. Ford’s result was about unique preimages. The factor-two conclusion here uses the additional bounds on the replacements at every stage.
