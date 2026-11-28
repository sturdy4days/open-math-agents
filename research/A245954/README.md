# Counts for every word length with four-entry windows

Consider words over $0,\ldots,n$. In each consecutive group of four entries, two different positions must contain numbers summing to $n$. For every word length $k$, the count is given by two polynomials of degree at most $k$, one for even $n$ and one for odd $n$. The registered seven-entry instance is OEIS A245954. [OEIS A245954](https://oeis.org/A245954)

The Lean theorem supplies the polynomials in the variable $m=\lfloor(n+1)/2\rfloor$, the number of two-letter complementary pairs. A middle letter is also available when $n$ is even. Each term in the falling-factorial basis $(m)_j$ has a nonnegative integer coefficient. That coefficient counts the valid signed words which use exactly $j$ named pairs when pair names are assigned in order of first occurrence. There are $(m)_j$ ways to replace the names by distinct actual alphabet pairs. An existing pair contributes its two labeled choices. A new pair receives the next name and its chosen orientation. A midpoint, when present, uses no name. This makes the coefficient independent of $m$.

The proof checks the bijection between numbers and their signed labels, the four-entry window test, and the evaluation of each length’s polynomial on the actual finite word count. At length seven it also proves equality with the original public definition. [Lean proof](AllWindowLengths.lean) · [Nine-declaration axiom audit](Audit.txt)

## An independent seven-entry calculation

There are 15 pairs of positions whose separation is at most three. Inclusion-exclusion over all $2^{15}=32768$ edge sets gives an independent calculation of the two degree-five polynomials. An edge $ij$ imposes $x_j=n-x_i$. Each bipartite connected component, including each isolated position, allows $n+1$ choices for its first entry. On a component with an odd cycle, the equation forces the middle letter, available only for even $n$. Combining the graph counts with the inclusion-exclusion weights gives

* $1+34n+6n^2-16n^3+66n^4+15n^5$ for even $n$.
* $58+57n-80n^2-28n^3+66n^4+15n^5$ for odd $n$.

The calculation also recovers the two formulas for the one-window sequence A246893 at length five and window width five. [Independent computation](window-polynomials.py) · [Coefficient tables](window-polynomials.json)
