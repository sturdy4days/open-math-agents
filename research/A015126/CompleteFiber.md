# All 33 preimages of 25,387,551,686,656 under Euler’s totient

Exactly 33 positive integers have Euler totient 25,387,551,686,656. The least is the even number **50,973,714,157,568**. The only odd preimage, **51,878,909,956,305**, is third in increasing order. Consequently A015126 takes the value 50,973,714,157,568 at every input in the table, including that odd input. This gives the exact sequence value for the counterexample to Jianing Song’s 2022 conjecture. [OEIS A015126](https://oeis.org/A015126) · [Original counterexample](https://github.com/sturdy4days/open-math-agents/blob/5ed21d3956316fa845be1a797ecaf97d6feff6a4/proofs/oeis-a015126.lean)

| Rank | Preimage | Rank | Preimage | Rank | Preimage |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 50,973,714,157,568 | 12 | 65,101,952,450,560 | 23 | 81,245,824,456,704 |
| 2 | 50,977,772,208,128 | 13 | 65,102,945,827,520 | 24 | 83,004,989,374,464 |
| 3 | 51,878,909,956,305 | 14 | 67,699,464,115,520 | 25 | 83,006,255,930,088 |
| 4 | 52,081,561,960,448 | 15 | 67,704,853,713,920 | 26 | 95,575,714,045,440 |
| 5 | 52,082,356,662,016 | 16 | 69,170,824,478,720 | 27 | 95,583,322,890,240 |
| 6 | 54,159,571,292,416 | 17 | 69,171,879,941,740 | 28 | 97,652,928,675,840 |
| 7 | 54,163,882,971,136 | 18 | 76,460,571,236,352 | 29 | 97,654,418,741,280 |
| 8 | 55,336,659,582,976 | 19 | 76,466,658,312,192 | 30 | 101,549,196,173,280 |
| 9 | 55,337,503,953,392 | 20 | 78,122,342,940,672 | 31 | 101,557,280,570,880 |
| 10 | 63,717,142,696,960 | 21 | 78,123,534,993,024 | 32 | 103,756,236,718,080 |
| 11 | 63,722,215,260,160 | 22 | 81,239,356,938,624 | 33 | 103,757,819,912,610 |

## Why the search is exhaustive

Write $M=25{,}387{,}551{,}686{,}656=2^{32}\cdot23\cdot257$. For a positive integer with totient $M$, let $y$ be its odd part. If $p^{k+1}$ is the exact power of an odd prime dividing $y$, then $(p-1)p^k$ divides $M$. Enumerating the divisors $p-1$ of $M$ gives nine possible odd primes. Each can occur at most once as a prime factor, except 257, whose square is also possible.

For each choice of prime powers, the proof calculates both $y$ and its totient. The odd value $y$ itself survives when $\varphi(y)=M$. An even preimage with odd part $y$ must have the form $2^{b+1}y$ and satisfy $2^b\varphi(y)=M$. Thus $M/\varphi(y)$ determines the only possible exponent. The proof checks this equality with integer arithmetic and verifies that every surviving row has the indicated totient. All 33 surviving values use primes at most 188,417.

In namespace `OMA.S_oeis_a015126`, `exact_inverse_fiber` proves membership in both directions, `totient_fiber_card` gives the cardinality, and `aSeq_on_fiber` gives the exact A015126 value. The standalone proof imports the registered statement. [Lean proof](CompleteFiber.lean) · [Registered statement](https://github.com/lefttosolve2/open-math-agents/blob/5bb94a9c795030864c62d2e7fe691aa9637656fe/statements/oeis-a015126.lean)
