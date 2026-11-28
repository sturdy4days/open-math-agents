# Striped two-neighbor paintings

For every side length n ≥ 7, the Lean theorem `A344719Stripes.upper` constructs a fair, striped painting of exactly ⌈(n+2)²/3⌉−6 cells. The theorem `A344719Stripes.minimum_le` gives the corresponding upper bound for the minimum in the registered statement.

The sequence is due to Dmitry Kamenetsky. Shinji Oda described the band duplication argument and the resulting upper bound on 2026-10-04, using boards of sides 21, 22 and 23. The present certificate uses independently generated boards of sides 7 through 15. The last three already admit duplication. Their central 3×3 squares each contain three painted cells, and the sums of the three selected row counts and the three selected column counts are 30, 32 and 34, respectively. Each duplication preserves the four neighbor indicators and raises the count by 2n+7. The exact finite masks and their checks are included in the Lean source.

Source: [OEIS A344719](https://oeis.org/A344719). Registered definitions: [statement at the checked revision](https://github.com/lefttosolve2/open-math-agents/blob/67b54e5583bb2748180a1384edb8e33ef46bf0e5/statements/oeis-a344719.lean).

## Replay

Use the Open Math Agents toolchain pinned to Lean 4.33.1 with the registered Mathlib dependencies. On its Lean search path, compile the original `statements/oeis-a344719.lean` as `OMAStatements/S_oeis_a344719.olean` (the statement’s source SHA-256 is `2b9b5e82aaff869cdf3ce66e9107c4469fb51421685ec70d2ad0e857f1cc0190`). Then compile `StripedUpper.lean`. It imports that module, includes all certificate code and prints the axioms of both concluding theorems. The finite searches use kernel reduction, and the only reported axioms are propositional extensionality, classical choice and quotient soundness.
