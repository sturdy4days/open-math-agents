# Two-element fibers of Euler’s totient

If a totient value has exactly two preimages and is divisible by none of 72, 120 and 200, then its two preimages are an odd integer and its double. An all-even two-element fiber has every member divisible by 36 or 100. The unrestricted conjecture remains open.

To see the square obstruction, strip from a positive preimage its full power of two and at most one copy each of 3 and 5. Unless 9 or 25 divided the original preimage, its totient becomes φ(c)·2ᵗ with c coprime to 30. For t equal to 0 or 1 there is an odd inverse, respectively c or 3c. For t ≥ 2, the three distinct preimages 8d, 10d, and 12d, where d=c·2^(t−2), all have this totient. Separately, if an even inverse were twice an odd integer, removing its factor 2 would give an odd inverse. Thus every inverse in the putative all-even pair is divisible by 4 and by at least one of 9 and 25. The induced totient divisibilities follow from φ(36)=12 and φ(100)=40.

A second pair of substitutions sharpens the restriction on the common totient N. Suppose 5 does not divide N and 9 does not divide N. Every preimage must contain a factor 9, hence is 9y. The cofactor y is divisible by neither 3 nor 7: otherwise 27 or 63 would divide the preimage and 9 would divide N. Replacing 9 by 7 leaves the totient unchanged and gives a preimage without its required factor 9. Thus 5 does not divide N only if 9 divides N. Similarly, when 3 and 25 do not divide N, every preimage is 25y; the even y is divisible by neither 5 nor 11. Replacing 25y by 2·11·y preserves the totient and removes the required factor 25. Combining these cases with the multiples of 12 and 40 above gives the stronger necessary condition that 36, 60 or 200 divides N.

One more restriction gives the final moduli. Suppose 8 does not divide the common totient. No preimage can be a multiple of 100, since φ(100)=40. Write each preimage as 36·3ᵃ·u where 3 does not divide u. An even u gives 72 dividing the preimage and 24 dividing its totient. For an odd u greater than 1, multiplicativity gives φ(36u)=12φ(u), a multiple of 8 because φ(u) is even. Thus u=1, and x=36·3ᵃ=3φ(x) for every preimage. This is incompatible with two distinct preimages. Therefore 8 divides N. Together with the pair of substitutions above, this restricts N to the multiples of 72, 120 or 200. These are 41 residue classes modulo 1800 among all integers.

The entry A271983 is due to Geoffrey Critzer, and the A007366 comment by Jianing Song states the equivalent doubling formulation. The registered Lean statement is due to @darealpandaboi.

* https://oeis.org/A271983
* https://oeis.org/A007366

The companion Lean file imports only the original registered statement. Compile it in the project’s pinned Lean/Mathlib environment and then run the audit module below with that file available as module Structural.

```lean
import Structural
#print axioms OMA.S_oeis_a271983.multiple_of_36_or_100
#print axioms OMA.S_oeis_a271983.common_multiple_12_or_40
#print axioms OMA.S_oeis_a271983.common_multiple_36_60_200
#print axioms OMA.S_oeis_a271983.eight_dvd
#print axioms OMA.S_oeis_a271983.doubling_outside_72_120_200
```

Pinned repository commit 648420f6ed927051f9dc2f28718aaffb50f04d59. All fourteen audited endpoints use only propext, Classical.choice and Quot.sound.
