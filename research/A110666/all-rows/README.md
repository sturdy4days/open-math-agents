# All rows of Quet’s A110665 array

Let a(m,n) be the array obtained from the initial binomial recurrence of A110665 by taking m partial sums. The Lean proof recovers the defining Pascal rule and identifies row one termwise with the project’s registered A110666.

Let F_m(X) denote the ordinary series of row m. The coefficient of Y^m in T(X,Y) is F_m(X). The file verifies both identities in formal power series over the integers.

    (1-X)^m (1-X+X²)² F_m(X) = X(1-2X)
    (1-X-Y) (1-X+X²)² T(X,Y) = (1-X)X(1-2X)

It also verifies that a(0,n) = n v(n), where v repeats 1,1,0,−1,−1,0. For each m ≥ 1, the entry a(m,n) is the sum over 0 ≤ k ≤ n of binom(n−k+m−1, m−1) k v(k).

Leroy Quet introduced these rows in 2005. Franklin T. Adams-Watters gave the periodic initial row and its generating function in 2006. R. J. Mathar conjectured the generating functions of rows 1, 2 and 3 in 2013. Colin Barker recorded empirical generating functions for rows 4 through 6 in 2014 and row 7 in 2016. Substituting these row numbers into the single identity above gives the corresponding ordinary generating functions, each starting at n = 0. The file also derives the initial row from its defining recurrence. [Initial row](https://oeis.org/A110665) · [Mathar’s row 3](https://oeis.org/A110668) · [Barker’s row 7](https://oeis.org/A110672)

ArrayFull.lean imports only the registered statement OMAStatements.S_oeis_a110666. In the project’s pinned Lean 4.33.1 environment with that statement built, compile the proof, then add the current directory to the project’s Lean search path for the independent axiom audit.

    lake env lean -o ArrayFull.olean ArrayFull.lean
    lake env bash -c 'LEAN_PATH="$PWD:$LEAN_PATH" lean ArrayAudit.lean'

[Registered statement](https://github.com/lefttosolve2/open-math-agents/blob/b4070ceef26613861013efd469bebc35eb86ebc4/statements/oeis-a110666.lean) · [Signed A110666 proof](https://github.com/sturdy4days/open-math-agents/blob/015ee5865f9802bbf12a6e8f7d5235a3b12de0c1/proofs/oeis-a110666.lean)
