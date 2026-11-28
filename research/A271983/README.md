# Two-element fibers of Euler’s totient

If a totient value has exactly two preimages and is divisible by neither 12 nor 40, then its two preimages are an odd integer and its double. An all-even two-element fiber has every member divisible by 36 or 100. The unrestricted conjecture remains open.

To see the square obstruction, strip from a positive preimage its full power of two and at most one copy each of 3 and 5. Unless 9 or 25 divided the original preimage, its totient becomes φ(c)·2ᵗ with c coprime to 30. For t equal to 0 or 1 there is an odd inverse, respectively c or 3c. For t ≥ 2, the three distinct preimages 8d, 10d, and 12d, where d=c·2^(t−2), all have this totient. Separately, if an even inverse were twice an odd integer, removing its factor 2 would give an odd inverse. Thus every inverse in the putative all-even pair is divisible by 4 and by at least one of 9 and 25. The induced totient divisibilities follow from φ(36)=12 and φ(100)=40.

The entry A271983 is due to Geoffrey Critzer, and the A007366 comment by Jianing Song states the equivalent doubling formulation. The registered Lean statement is due to @darealpandaboi.

* https://oeis.org/A271983
* https://oeis.org/A007366

The companion Lean file imports only the original registered statement. Compile it in the project’s pinned Lean/Mathlib environment and then run the audit module below with that file available as module Structural.

```lean
import Structural
#print axioms OMA.S_oeis_a271983.multiple_of_36_or_100
#print axioms OMA.S_oeis_a271983.common_multiple_12_or_40
#print axioms OMA.S_oeis_a271983.doubling_outside_12_and_40
```

Pinned repository commit 648420f6ed927051f9dc2f28718aaffb50f04d59. All nine audited endpoints use only propext, Classical.choice and Quot.sound.
