# Robin’s inequality through 720719

`RobinInline.startup` proves the strict inequality
σ(n) < exp(γ) n log(log n) for every integer n with 5040 < n < 720720.
The proof has no hypothesis about the Riemann hypothesis. It uses complementary
divisor pairs for the initial interval and the colossally abundant tangent
estimate for n ≥ 7560. The registered Robin criterion quantifies over all n
greater than 5040 and asserts an equivalence with the Riemann hypothesis.

## Replay

Use Lean 4.33.1 and Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474.
In a checkout of that Mathlib revision, run `lake exe cache get`, then
`lake env python3 /absolute/path/to/replay.py`. The script checks each
archived content hash and the Lean version, compiles the single source
file, and audits the resulting theorem. Its expected axioms are
`propext`, `Classical.choice`, and `Quot.sound`. Verified runs and the
pinned Mathlib source revision are recorded in `verification.json`.
All Lean imports are standard Mathlib modules.

## Source and attribution

Jonas Whidden formalized the tangent argument in Robin1984, based on Guy
Robin’s 1984 work. This archive inlines the indicated 13 modules at commit
e3697139babfe0f6cc7a76a08bf41a92aa7a2978. Exact original file digests and the
order of assembly are in `sources.json`. The arithmetic bridge from the
donor’s divisor sum to Mathlib’s σ follows Sky’s FCRobinLagarias.Robin
interface. The complementary divisor-pairing argument in the finite part
adapts Sky’s LeanClassics.RobinCheck at dc12df6aaf4fa88fc9e6534b81ed67b89c99d8e4.
[Robin1984](https://github.com/kimihiro64/Robin1984/tree/e3697139babfe0f6cc7a76a08bf41a92aa7a2978) · [RobinCheck](https://github.com/ChironTheCentaur/rh-lab-robin-lagarias/blob/dc12df6aaf4fa88fc9e6534b81ed67b89c99d8e4/LeanClassics/RobinCheck.lean) · [Guy Robin’s paper](https://mathscinet.ams.org/mathscinet-getitem?mr=774171)

The package includes original Apache 2.0 licence texts, Sky’s original
NOTICE file, Whidden’s CITATION.cff and the upstream licensing scope. The
combined source annotates its origin and the finite proof’s adaptations.
The donor’s sealed finite-event package is implemented by ordinary classical
witness selection. Each of the 79 finite computation proofs sets its own
recursion depth. The original Lean namespaces are retained.
