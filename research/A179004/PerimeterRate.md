# How quickly Hardin’s stable-grid density approaches two thirds

Let $B(n,m)$ be the maximum number of ones in a stable binary rectangle. Every cell must have at least as many opposite-colored neighbors as same-colored neighbors. For all $n,m$ at least eight, the deficit from two thirds satisfies

$$
\frac1{18}\left(\frac1n+\frac1m\right)
\;\le\; \frac23-\frac{B(n,m)}{nm}
\;\le\; \frac23\left(\frac1n+\frac1m\right).
$$

On a square of side $n$, the deficit is between $1/(9n)$ and $4/(3n)$. This gives the order of convergence for both squares and rectangles. R. H. Hardin proposed the limiting density in 2011. [OEIS A179004](https://oeis.org/A179004)

The upper estimate for the deficit follows from the three explicit phase-shifted paintings used in the proof of the limit. The lower estimate comes from counting edges on the boundary. Every boundary one must have an adjacent boundary zero. Each boundary zero can have at most two such neighbors, so at least a third of the perimeter cells are zero. Each of these also has a missing grid neighbor. Including those missing edges in the count of opposite-color incidences gives $9B+n+m\le6nm+8$ for $n,m\ge5$.

The Lean theorem `GridAnti.Hardin.density_gap` has both estimates. To replay, compile the original signed proof as `HardinProof.lean`, then compile `PerimeterRate.lean` in the same Lean 4.33.1 environment. Both the perimeter inequality and the final density bounds were audited with only propositional extensionality, classical choice and quotient soundness. [Lean source](PerimeterRate.lean) · [Original signed proof](../../proofs/oeis-a179004.lean)
