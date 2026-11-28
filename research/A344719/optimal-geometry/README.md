# The interior of a minimum fair painting

A fair painting of the square grid leaves every unpainted cell with exactly two painted horizontal or vertical neighbors. For every minimum fair painting of an n-by-n board with n ≥ 7, at most four painted-to-painted neighbor incidences originate in the square obtained by removing five rows or columns from each edge. A painted edge with both endpoints in that square contributes two incidences. For n congruent to 1 modulo 3, the number of incidences is zero.

For n ≥ 15 in that congruence class, there is exactly one pair (s,c), with s equal to 1 or 2 and c in {0,1,2}, such that a cell (x,y) is painted exactly when x+sy ≡ c modulo 3 throughout the inset square except its four corners. Coordinates start at zero. The result applies to every minimizer.

The first assertion follows by applying the four boundary estimates after dropping the entire inset square from the discharging sum. In the second assertion, a run of three interior cells contains exactly one painted cell whenever neighboring painted cells have been excluded in the surrounding patch. The row and column periods then force a single diagonal congruence class. A 3-by-3 patch determines its slope and phase uniquely.

## Replay

Use the A344719 direct proof as the module `Submission`, pinned at SHA-256 `7e62bfb0cd0193b061be185fd790ad3a9396d1396ece5e2c231d0d584274bd5a`. The registered statement has SHA-256 `2b9b5e82aaff869cdf3ce66e9107c4469fb51421685ec70d2ad0e857f1cc0190`. In a Lean 4.33.1 project with the pinned Mathlib dependencies, fetch these two sources, put the statement in `OMAStatements/S_oeis_a344719.lean` and the proof in `Submission.lean`, and run:

    export LEAN_PATH=".:$(lake env printenv LEAN_PATH)"
    lean -j1 -o OMAStatements/S_oeis_a344719.olean OMAStatements/S_oeis_a344719.lean
    lean -j1 -o Submission.olean Submission.lean
    lean -j1 -o OptimalGeometry.olean OptimalGeometry.lean

The final file prints the axiom reports for both structural statements and their supporting defect estimate. A verification report records the exact SHA-256 of the companion and the kernel output.

[Signed A344719 proof](https://github.com/sturdy4days/open-math-agents/blob/f4054c0e2fd68cc652086579cf895ca6bffc3d0a/proofs/oeis-a344719.lean) · [Registered statement](https://github.com/lefttosolve2/open-math-agents/blob/67b54e5583bb2748180a1384edb8e33ef46bf0e5/statements/oeis-a344719.lean)
