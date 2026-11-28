# The generating function for the grid-painting conjecture

Lean proves that the proposed A344719 generating function is equivalent to the first seven coefficients $0,1,2,5,8,11,17$, followed by $a(n)=\lceil(n+2)^2/3\rceil-6$ for $n\ge7$. Consequently the quantitative tail and those seven initial values suffice for the generating-function part of the project. The existence of striped optimal paintings and the sharp geometric lower bound remain separate questions. [Shinji Oda’s formula and stripe conjecture](https://oeis.org/A344719) · [Registered Lean statement](https://github.com/lefttosolve2/open-math-agents/blob/67b54e5583bb2748180a1384edb8e33ef46bf0e5/statements/oeis-a344719.lean)

The denominator factors as $(1-x)^2(1-x^3)$. Increasing $n$ by three increases the proposed tail by $2n+7$. Two further finite differences annihilate this linear expression, leaving the twelve low-order coefficients to check directly. The denominator has constant term one, so equality of its products forces equality of the two coefficient sequences.

`OMA.A344719Series.formula_iff` works for any natural-number sequence. `OMA.A344719Series.original_iff` applies this result to the precise registered conjunction, including striped optimality. Its audit and those of the three supporting theorems returned `propext`, `Classical.choice`, and `Quot.sound`.

## Replay

Use Lean 4.33.1 with Mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. Compile the linked statement as `OMAStatements/S_oeis_a344719.lean` in a local import directory, then compile `GridSeries.lean` and `GridSeriesAudit.lean` with that directory on `LEAN_PATH`.
