# Distinct totient witnesses within a factor of two

Every integer n with 0 < n < 1,005,812,286,886,445,360,864,113,179,310,319,650,005,270,228 has an integer m ≠ n with m ≤ 2n and φ(m) = φ(n). For every N, the number of exceptions up to N is at most 435·⌊N/1005812286886445360864113179310319650005270228⌋. The companion Lean source verifies these bounds. No statement in it assumes the unrestricted conjecture.

Prime-square forcing adapted from the classical argument for Carmichael’s totient conjecture, first proves that every exception is divisible by 2²·3²·7²·43² = 3,261,636. More explicitly, if p is prime and both p−1 and its radical occur as factors as prescribed in `Noe.square_from_radical`, replacing p−1 by p or vice versa yields an equal-totient witness within the required factor of two unless p² already divides the input.

For the remaining argument, take an exceptional multiple n=a·c. A move a→b certifies b ≠ a, b ≤ 2a, and φ(a)=φ(b). The equality persists after multiplying a and b by c whenever every prime dividing c occurs in both a and b or in neither. Otherwise a prime p from the displayed exceptional list divides c, and the known divisor of n increases from a to ap. The Lean proof verifies the finite tree using explicit prime factorizations, reducing it to 435 terminal divisors, all at least 1,005,812,286,886,445,360,864,113,179,310,319,650,005,270,228. A union bound on their positive multiples gives the counting estimate.

T. D. Noe conjectured this bound in OEIS A074987, an entry by Joseph L. Pe. The registered project statement is by @FFD-007. For the classical divisibility argument and the distinct problem of finding arbitrary equal-totient witnesses, see A. Schlafly and S. Wagon, *Carmichael's conjecture on the Euler function is valid below 10^10,000,000* (1994).

* https://oeis.org/A074987
* https://doi.org/10.1090/S0025-5718-1994-1226815-3

With the original module `OMAStatements.S_oeis_a074987` compiled against the project’s pinned Mathlib and on LEAN_PATH, compile `Noe45Research.lean`. Its declarations `Noe45.bounded`, `Noe45.covered` and `Noe45.exceptional_count` give the pointwise bound, divisor cover, and uniform count. All eight audited endpoints use only propext, Classical.choice, and Quot.sound.
