# A compensated-primitive proof of the Robin converse

The Lean file proves that if every integer n > 5040 satisfies σ(n) < exp(γ) n log(log n), then the Riemann hypothesis follows. Jonas Whidden had already formalized this implication. The new contribution here is the replacement of a quantitative prime number theorem in the Mellin transform argument, together with a standalone proof for the exact Formal Conjectures target.

For x ≥ 3, let W(t) = (1/log t + 1/log² t)/t². The proof uses Mertens’s theorem to construct a function J with J(x) → 0 and J(x) − J(y) = ∫ₓʸ (ψ(t)−t)W(t) dt. The finite Euler-product comparison uses this same J. Integration over 3 < t < x gives its Mellin transform on the negative half-plane. An Abel limit at zero and a damped Frullani integral identify the result with the analytic continuation used in the positivity and rightmost-zero arguments. A zero with real part above one half would imply incompatible analytic continuations under the divisor-sum hypothesis.

## Sources and attribution

- G. Robin, *Grandes valeurs de la fonction somme des diviseurs et hypothèse de Riemann*, J. Math. Pures Appl. 63 (1984), 187–213. J.-L. Nicolas, *Petites valeurs de la fonction d’Euler*, J. Number Theory 17 (1983), 375–388.
- Jonas Whidden’s Apache-2.0 **Robin1984** supplies the Landau positivity argument and the zeta-zero singularity, including the compact and large parameter estimates. We adapted these to the compensated primitive and its boundary value. The published prior proof uses the same divisor-sum hypothesis, normalization and cutoff. [Published prior theorem, August 2026](https://github.com/kimihiro64/Robin1984/blob/208b44750090b7b0e2254e3d511b4d119052cd03/Robin1984/NicolasLandau/NicolasLandauRobinBridge.lean#L35-L41) · [Source revision](https://github.com/kimihiro64/Robin1984/tree/e3697139babfe0f6cc7a76a08bf41a92aa7a2978)
- The Mertens estimates are adapted from **PrimeNumberTheoremAnd** by its contributors, including Terence Tao, A. J. Irving, Giuseppe Sorge, Robby Sneiderman and Yan Yablonovskiy. The Lean source credits the port by marcusbuffett reused in the OMA Mertens proof. The source retains those notices and the accompanying Apache-2.0 license. [Original Mertens source](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/55270df80721) · [OMA Mertens proof](https://github.com/lefttosolve2/open-math-agents/pull/12357)
- The exact Euler-factor and least-common-multiple estimates use the earlier OMA work on the Lagarias criterion. The project’s Robin criterion reduction is by ihateSAS. [Lagarias arithmetic](https://github.com/lefttosolve2/open-math-agents/blob/1f440931e1c42a28fc6a6c07fa067f06f58cd2bd/proofs/RiemannHypothesis.lagarias_criterion.R1.H2.R1.H1.R1.H2.lean) · [Robin reduction](https://github.com/lefttosolve2/open-math-agents/pull/3261)

## Reproduction

Use Lean 4.33.1, the project’s pinned Mathlib, the Formal Conjectures article from commit 9097e2f90e66d2f6244209cb1c07f7120d17ec53, and the byte-identical registered reduction from PR 3261. With those modules on LEAN_PATH, run these commands in this directory.

    cp RobinConverse.lean Submission.lean
    lean -j1 -o Submission.olean Submission.lean
    LEAN_PATH=.:$LEAN_PATH lean Audit.lean

The attached verification receipt records the exact source and the six audited declarations.
