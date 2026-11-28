# The fourteen-vertex catalogue for Erdős 1182

Lean theorem `FiniteTen.complete14` proves that every maximal triangle-free graph on fourteen vertices whose complement avoids the prescribed ten-vertex graph is isomorphic to a graph in the explicit list `Production13.children`. The target is `ICXmt~~~w` in graph6 notation and has 33 edges. The source checks the transition from every one of the 310 order-thirteen parents. The fourteen-vertex catalogue has 728 entries. The subsequent transitions to orders fifteen through eighteen are separate theorems.

## Reproduction

Use Lean 4.33.1 and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. In its Lake project, run the following command. The proof requires Python 3.11+ and the transitive Mathlib packages.

    lake env python3 /absolute/path/order14/replay.py --build /absolute/path/order14-build

The default replays every local Lean module in dependency order with one kernel worker and a 4,200 MiB Lean limit. Each `.lean` file and its order are recorded in `manifest.json`. For repeated invocations the driver checks input and output digests before accepting a saved verification receipt. The final check is a separately compiled import of the theorem and reports the axioms for the order-thirteen classification, its transition, the induction step, and the order-fourteen classification.

The optional `--reuse-dir` flag imports previously checked proof objects only if they match the SHA-256 digests recorded at packaging. Supply it multiple times for separate directories holding verified modules. The flag `--fresh MODULE` forces the listed module to recompile. The default full build needs zero prebuilt local objects. Pass an already pinned Mathlib environment to the driver.

## Sources and credits

The greedy maximal triangle-free construction follows the Ramsey graph generation work of Stephan Brandt, Gunnar Brinkmann and Thomas Harmuth. The proposed catalogue labels were generated with Triangleramsey by Gunnar Brinkmann, Jan Goedgebeur and Jan-Christoph Schlage-Puchta and with nauty. Lean checks the labelled witnesses and the completeness argument. Earlier signed research by sturdy4days supplied the entire precursor classification through order thirteen. The archive includes each of its source files needed here, byte for byte, along with the next transition and the new endpoint.

[Signed order-thirteen source](https://github.com/sturdy4days/open-math-agents/blob/78dfa447bc058eac30e497deaa0a3f3275d4edfc/research/Erdos1182/order-ten/early-prefix-13.tar.gz)
