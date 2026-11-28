# Finite sums of simultaneous returns in OEIS A230496

For any finite family of natural-coefficient polynomials, choose a seed d, a positive progression modulus q and a positive digit-count modulus H. There is a superincreasing sequence of positive multiples of q such that adding any finite sum of distinct sequence elements to d preserves the number of binary ones modulo H for every polynomial in the family. Distinct index sets give distinct sums.

For the original conjecture, fix a power cutoff $n$. `OMA.OdiousIP.odious_family` produces a sequence such that every nonempty finite sum $s$ gives a different odd integer $1+s>1$, and every power $(1+s)^i$ with $i\le n$ has an odd number of binary ones.

The general theorem is `OMA.OdiousIP.polynomial_ip_returns` in `IPReturns.lean`. It applies the one-step recurrence of @connoranderson to the finitely many translated polynomials at each stage. Its dependency is pinned to the lead’s upstream contribution at commit `c0be4a092d417fd65738fd3672fd0f8026e57de2`. The project statement formalizes the conjecture of Vladimir Shevelev and Peter J. C. Moses. [Lead’s proof](https://github.com/lefttosolve2/open-math-agents/pull/28795) · [OEIS A230496](https://oeis.org/A230496)

## Replay

Use Lean 4.33.1 with Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474` built. From that Lean project's directory run the following command, substituting the absolute path to this bundle.

```sh
lake env bash /absolute/path/to/replay.sh
```

The script downloads the registered statement from its upstream merge commit `cd9cc5af37093d318091ca0589f6ede67e4986bc` and the lead’s proof from the pinned pull-request commit, verifies both SHA-256 digests, and compiles them as `OMAStatements.S_oeis_a230496` and `Lead`. It then compiles the companion and prints its axiom dependencies. The downloaded sources and generated objects are held in a temporary directory.
