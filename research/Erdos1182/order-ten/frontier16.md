# The order-16 Ramsey catalogue for Erdős 1182

`FiniteTen.complete16` proves that every maximal triangle-free graph on 16 vertices whose complement avoids the prescribed ten-vertex target is isomorphic to a member of `Production15.children`. The 1,461 parents at order 15 have 1,716 listed representatives at order 16. The ten-vertex target has graph6 code `ICXmt~~~w`, 33 edges, triangular code 35184366705032 and missing-edge mask 72057645653176374.

## Kernel replay

Use Lean 4.33.1 with Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474` and Python 3.11 or later. From that Mathlib project, run

    lake env python3 /path/order16/replay.py --build /path/new-build

This checks every local source in topological order using a single Lean worker, then imports the endpoint for a fresh axiom audit. The driver resumes a partial replay after comparing its source, imported objects and output with the stored receipts. `--reuse-dir DIR` optionally accepts previously checked objects with the manifest SHA-256. `--fresh MODULE` always re-elaborates that source. The independent frontier check re-elaborates two complete joined groups of the newest level, every combined level and milestone after order fifteen, and the final audit. All other objects in that check match the manifest. The accompanying replay report lists the newly built and reused modules.

## Source and provenance

The archive contains Lean sources, kernel input/output fingerprints, axiom reports and group membership data. For each joined group, the twelve or fewer parent proofs retain their original theorem bodies and axiom checks. The join removes redundant imports and imports the common data module once. To check every byte against the two earlier archives, run

    python3 /path/order16/provenance.py /path/mixed-source-snapshot.tar.gz /path/frontier15.tar.gz

The snapshot of 5,480 standalone source files has SHA-256 `28fa9f0762a3d2e1e9d025fb0ef1de267547bd112147ae79d59707a50f0e61c6`. The preceding signed order-fifteen source archive has SHA-256 `254f5b3b01fddf843ec7cf1cfeb2bc6c6a72d9245dc497ce4e60f3fc1b0b75b6`. The archive is self-contained for a kernel replay on the pinned Mathlib environment. [Signed frontier fifteen](https://github.com/sturdy4days/open-math-agents/blob/ab42a3bca3d1ad08f65c4deada552819a5e4e75b/research/Erdos1182/order-ten/frontier15.tar.gz)

The maximal triangle-free construction follows work of Stephan Brandt, Gunnar Brinkmann and Thomas Harmuth. Triangleramsey by Gunnar Brinkmann, Jan Goedgebeur and Jan-Christoph Schlage-Puchta, and nauty, provided candidate catalogue labels. The Lean sources check the witnesses and the completeness theorem. The signed prefix and the subsequent certificate production are credited to sturdy4days and collaborators.
