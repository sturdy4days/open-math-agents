# Complementary pairs in words of any length

Pick a word of length $k$ over $0,\ldots,n$. How many words have two entries in distinct positions whose sum is $n$? At $k=5$ this is the sequence in OEIS A246893. Its first four terms, starting at $n=1$, are $30,231,900,2701$. The canonical proof establishes the two parity polynomials and rational generating function recorded by Colin Barker in the entry formalized by @clementtrecourt. [OEIS A246893](https://oeis.org/A246893)

## A formula for every length

Let $m=\lfloor(n+1)/2\rfloor$ be the number of two-element complementary pairs in the alphabet. Write $(m)_r=m(m-1)\cdots(m-r+1)$ and let $S(k,r)$ be a Stirling number of the second kind. Define
$$
P(m,k)=\sum_{r=0}^m (m)_r\,2^r\,S(k,r).
$$

To avoid a complementary pair, a word can use at most one of the two letters in each pair. Partition its positions into $r$ nonempty blocks, one for each letter used. Assign distinct alphabet pairs to the blocks and choose which of the two letters each block uses. This gives $P(m,k)$ words when all letters belong to two-element pairs.

For even $n$, the middle letter $n/2$ may occur once. There are $k$ choices for its position, after which the other positions again contribute $P(m,k-1)$. The number of words **containing** a complementary pair is therefore

| Endpoint of alphabet | Number of words |
|---|---|
| Odd $n$ | $(n+1)^k-P(m,k)$ |
| Even $n$ | $(n+1)^k-P(m,k)-kP(m,k-1)$ |

At $k=0$ the term multiplied by $k$ is zero. At general $k$ the two positions may be anywhere in the word. Taking $k=5$ recovers exactly the five-position window in the registered OEIS statement.

Each two-letter pair contributes $2e^z-1$ to the exponential generating function for avoiding words. There is one empty choice, or a nonempty set of positions all carrying one of two possible letters. The middle letter contributes $1+z$ when present. Thus the generating function in length is $(2e^z-1)^m$ for odd $n$ and $(2e^z-1)^m(1+z)$ for even $n$.

The Lean file proves the formulas directly for the finite set of words, including empty alphabets of complementary pairs and empty words. The separate import-only audit checks ten endpoints. An independent enumeration tested every word with $0\le n,k\le6$, totaling 219,463 words. [Lean proof](AllLengths.lean) · [Axiom audit](Audit.txt) · [Enumeration](brute-counts.json)
