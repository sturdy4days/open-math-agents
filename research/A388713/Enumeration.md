# Counting superdiagonal partitions in A388713

Let $T(n,k)$ count partitions of $n$ whose largest part is $k$. Keep a partition when its parts in increasing order satisfy $y_i\ge i$ at every position, starting at $i=1$. The empty partition is excluded, as in the registered OEIS statement.

**Distinct representatives.** Gus Wiseman’s conjectured description counts the same objects. For nested sets of sizes $y_1\le\cdots\le y_\ell$, the number of ways to choose one distinct representative from each, with the sets in this fixed order, is

$$
\prod_{i=1}^{\ell}\max(0,y_i-i+1).
$$

For a partition, the sets are the intervals from $1$ to its parts. This product is positive exactly when the partition is superdiagonal. Clément Garrot gave the pigeonhole argument for necessity in the related OEIS entry A387112. [A388713](https://oeis.org/A388713) · [A387112](https://oeis.org/A387112)

**Which entries vanish.** The exact support is $T(n,k)>0$ if and only if $0<k\le n\le k^2$. In a positive row $n$, the missing columns are $0$ through $\lceil\sqrt n\rceil-1$. This proves the row-zero count suggested in the OEIS entry. Row zero consists of a single zero. If the number of parts $\ell$ is fixed as well, every total from $k+\binom{\ell}{2}$ through $k\ell$ occurs, provided $1\le\ell\le k$. [A003059](https://oeis.org/A003059)

**Column totals.** With $C_k$ the $k$th Catalan number,

$$
\sum_{n=0}^{k^2} T(n,k) = C_{k+1}-C_k.
$$

This identifies the column totals as A000245. The positive columns start $1,3,9,28,90,297$. The proof counts weakly increasing arrays with a fixed ceiling $k$ and length $\ell$. Their count is $\binom{k+\ell}{\ell}-\binom{k+\ell}{k+1}$ for $0\le\ell\le k$. Splitting on whether the last entry reaches the ceiling gives the ballot recurrence. A bijection then identifies these arrays with the partitions used in the registered triangle. [A000245](https://oeis.org/A000245)

**Computing the triangle.** Let $B(k,\ell;n)$ count weakly increasing superdiagonal arrays of length $\ell$, with entries at most $k$ and total $n$. For $1\le\ell\le k$,

$$
B(k,\ell;n)=B(k-1,\ell;n)+\begin{cases}B(k,\ell-1;n-k),& n\ge k,\\0,&n<k.\end{cases}
$$

The first term counts arrays that do not reach the ceiling. The second appends a final part equal to the ceiling. Removing that part gives the original column coefficient $T(n,k)=\sum_{\ell=0}^{k-1}B(k,\ell;n-k)$ when $1\le k\le n$. The empty array has total zero, and lengths greater than the ceiling contribute zero.

The standalone Lean source imports the registered article and Mathlib. A separate calculation checked the supplied 78 OEIS entries, compared all rows through 40 with direct partition enumeration, and counted all partitions in the first eleven positive columns independently.
