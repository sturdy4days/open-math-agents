# The complete positive complement of OEIS A325618

OEIS A325618 lists the positive integers $m$ admitting a partition $m=y_1+\cdots+y_s$ with $\sum_i 1/y_i!=1$. The first sequence value is 1, the second is 4. The classification below concerns the possible values of $m$. Charlie Neder conjectured in 2019 that 137 is the largest omitted value. The original Lean contribution proves that claim. [OEIS A325618](https://oeis.org/A325618) · [Original proof](https://github.com/sturdy4days/open-math-agents/blob/6d2b2312f62263b84df882247543f3df1b529365/proofs/oeis-a325618.lean)

Exactly 78 positive integers are omitted. The ranges include both endpoints.

> 2–3, 5–10, 12–17, 19–23, 25–30, 32–36, 38–43, 46–49, 51, 53–56, 59–64, 67–69, 72, 74–75, 77, 80–82, 84–85, 88, 90, 93, 95, 98, 101, 103, 105–106, 111, 116, 124, 129, 136–137.

The Lean predicate accepts any nonnegative input. Its complement also contains 0, whose only partition is empty and has reciprocal factorial sum 0. Thus the formal list has 79 entries. Among the positive integers from 1 through 137, exactly 59 admit a partition. Every integer from 138 onward admits one.

## How to decide membership

At a search step, the remaining parts must each be at least $k$. Write $m$ for their total weight and $u$ for their remaining reciprocal factorial sum multiplied by $k!$. Start at $(k,m,u)=(1,m,1)$. A nonempty valid remainder has $u>0$ and $ku\le m$, because each remaining part $y\ge k$ satisfies $k\,k!/y!\le y$.

If a part $k$ is used, the new state is $(k,m-k,u-1)$. If every remaining part is larger, the new state is $(k+1,m,(k+1)u)$. With positive $k$, each choice decreases $2m-k$ while a nonempty partition remains. A successful branch reaches $m=u=0$. Reading the chosen parts along that branch constructs a genuine partition. These two directions prove that the integer recursion decides membership.

Lean checks each input through 137 with that procedure. The original interval construction supplies all larger weights. The standalone source imports the registered statement and proves both the decision theorem and the complete classification. The two declarations in namespace `OMA.S_oeis_a325618` are `isTerm_iff_decision` and `exact_complement`. Their axiom audits list only `propext`, `Classical.choice`, and `Quot.sound`. [Lean proof](CompleteClassification.lean) · [Registered statement](https://github.com/lefttosolve2/open-math-agents/blob/284fc1757da9a14930f2e15f28b58e54d1cf1afa/statements/oeis-a325618.lean)
