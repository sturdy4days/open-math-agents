# The ten-vertex Ramsey target

The Lean census now covers every host order from 0 through 13. At order 13, every maximal triangle-free host whose complement avoids the specified ten-vertex target is isomorphic to a graph in the explicit 310-element catalogue. The proof also covers arbitrary triangle-free avoiding hosts by spanning containment. The order-12 extension step checked all 565,248 neighborhoods of the new vertex over 138 parents.

At order 18, separate Lean proofs show that the three graphs from the computational census are pairwise nonisomorphic, maximal triangle-free, and each avoids the target in its complement. For two graphs, a certificate rules out every embedding by bounding the number of available host vertices for a subset of target vertices. The third complement has maximum degree eight and the target has degree nine.

The earlier terminal supplement proves that every order-19 extension of the three graphs contains the target. Five intermediate transitions, from parent orders 13 through 17, are still needed to connect the kernel-checked prefix to that terminal result. The computational census covering those orders is already available on the parent branch.

Both archives include replay instructions for Lean 4.33.1 and mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. The prefix endpoints are EarlyRamsey.complete13_code and EarlyRamsey.spanning13. The survivor endpoint is Terminal18.three_obstructions, and its separate archive replay regenerated the input and recompiled all 50 modules.
