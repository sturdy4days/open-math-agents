import OMAReductions.R_RiemannHypothesis_robin_criterion_R1_H1_R1

/-!
# The startup interval for the finite Robin bound

Jonas Whidden’s Robin1984 development treats integers below 720720 by its
startup estimates. The second hypothesis starts at the same endpoint.
-/

namespace OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H1_R1
open Real
open scoped ArithmeticFunction.sigma

/-- The unconditional finite startup range in Jonas Whidden's Robin1984 development. -/
def H1 : Prop := ∀ n : ℕ, 5040 < n → n < 720720 →
  σ 1 n < exp eulerMascheroniConstant * n * log (log n)

/-- The remainder up to the published logarithmic cutoff. -/
def H2 : Prop := ∀ n : ℕ, 720720 ≤ n → log n ≤ exp 30 →
  σ 1 n < exp eulerMascheroniConstant * n * log (log n)

theorem main : H1 → H2 → OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1.H1 := by
  intro first rest n lower upper
  by_cases small : n < 720720
  · exact first n lower small
  · exact rest n (Nat.le_of_not_gt small) upper

end OMA.R_RiemannHypothesis_robin_criterion_R1_H1_R1_H1_R1
