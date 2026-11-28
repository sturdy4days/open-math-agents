# The second exclusion in A294646

For every positive index n, the inverse of 4ⁿ modulo 2n+1 differs from 2n. The general result applies to every natural base b and every odd modulus m greater than one. Such an m cannot divide b^(m−1)+1. The Sydney University Mathematical Society published the general result for positive bases in its 2004 competition solutions, problem 2. The Lean file formalizes it and derives the sequence claim. [Competition solutions](https://www.maths.usyd.edu.au/u/SUMSCOMP/sols2004.pdf) · [OEIS A294646](https://oeis.org/A294646)

Write m−1 as 2ᵏu with u odd. If b^(m−1) were −1 modulo m, it would be −1 modulo each prime divisor p of m. Write p−1 as 2ʲv with v odd. If j≤k, Fermat’s little theorem gives b^((m−1)v) = 1 modulo p, while raising −1 to the odd power v gives −1. Since p is odd, this is impossible. Consequently every prime divisor of m is 1 modulo 2ᵏ⁺¹. Their product with multiplicities is m, forcing 2ᵏ⁺¹ to divide m−1 and contradicting the choice of k.

For the sequence take m=2n+1 and b=2. If 2n were the inverse, multiplying 4ⁿ by −1 modulo m would give 1, precisely the impossible congruence.

The other two exclusions have separate resolutions. Masselorc verified the first, that the inverse never equals 2. Bonnie9981 published the counterexample n=9,814,447,404 to the third on November 23, 2026. Together the three results decide each exclusion in the original conjunction. [First exclusion](https://github.com/Masselorc/open-math-agents/blob/ca355b68518f15b458c20e3101c473c4f5a02c34/reductions/oeis-a294646.R1.lean) · [Prior counterexample](https://github.com/Bonnie9981/Project-Discovery/blob/cbf4c9343adf6aaec34ed82a6828110eb73e8b42/lean/Discovery/A294646Counter.lean)
