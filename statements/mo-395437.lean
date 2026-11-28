import Mathlib

/-!
# The Robin score along colossally abundant numbers

Source: https://mathoverflow.net/questions/395437, asked by ntessore (2021, CC BY-SA 4.0).
Formalization: @sturdy4days.

For a positive parameter, the prime-exponent floor formula of Alaoglu and Erdős
in the question picks the largest maximizing integer at ties. We use this
equivalent extremal description to specify the same integer. The original
question asks whether its score increases as the parameter decreases below
0.01. The edit also asks about the right-hand limit superior at zero and
whether the proposed monotonicity is equivalent to the Riemann hypothesis.
-/

namespace OMA.S_mo_395437

open Filter Real Topology
open scoped ArithmeticFunction.sigma

/-- The abundancy index σ(n)/n. -/
noncomputable def abundancy (n : ℕ) : ℝ := (σ 1 n : ℝ) / n

/-- The greatest integer maximizing σ(n)/n^(1+e) over positive integers. -/
noncomputable def candidate (e : ℝ) : ℕ :=
  sSup {n : ℕ | 0 < n ∧ ∀ m : ℕ, 0 < m →
    abundancy m / (m : ℝ) ^ e ≤ abundancy n / (n : ℝ) ^ e}

/-- Grönwall's normalized divisor sum and its natural logarithm. -/
noncomputable def ratio (n : ℕ) : ℝ := abundancy n / log (log n)

noncomputable def score (e : ℝ) : ℝ := log (ratio (candidate e))

/-- Monotonic increase toward zero allows intervals on which the candidate is constant. -/
def monotonicity : Prop := AntitoneOn score (Set.Ioo 0 (1 / 100 : ℝ))

theorem main :
    monotonicity ∧
    (limsup ratio atTop = exp eulerMascheroniConstant →
      limsup score (𝓝[>] 0) = eulerMascheroniConstant) ∧
    (monotonicity ↔ RiemannHypothesis) := by
  sorry

end OMA.S_mo_395437
