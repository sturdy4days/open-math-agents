import OMAStatements.S_mo_138446
import Mathlib.Tactic

/-!
# Rational Mordell points at infinitely many nonsquarefree parameters

The x-coordinate remains 5 in this family. Each parameter is divisible by
25 and congruent to 19 modulo 24. The obstruction is already visible in
the residue ring modulo 25.
-/

namespace MordellObstruction

def parameter (n : ℕ) := 25*(144*n^2+288*n+139)

/-- The parameters are distinct positive integers. -/
theorem increasing : StrictMono parameter := by
  apply strictMono_nat_of_lt_succ
  intro n
  unfold parameter
  nlinarith

theorem not_squarefree (n : ℕ) : ¬ Squarefree (parameter n) := by
  intro sq
  exact (Nat.squarefree_iff_prime_squarefree.mp sq 5 (by decide)) (dvd_mul_right 25 _)

private theorem nonsquare (n : ℕ) : ¬ IsSquare (5 : ZMod (parameter n)) := by
  have dv : 25 ∣ parameter n := dvd_mul_right _ _
  let f := ZMod.castHom dv (ZMod 25)
  rintro ⟨z,hz⟩
  have q := congrArg f hz
  rw [map_ofNat,map_mul] at q
  have impossible : ∀ x : ZMod 25, (5 : ZMod 25) ≠ x*x := by decide
  exact impossible _ q

/-- The point satisfies the curve equation, the denominator hypothesis, and
the congruence hypothesis, while its reduced x-coordinate is a nonsquare. -/
theorem rational_family (n : ℕ) :
    let k : ℤ := parameter n
    let x : ℚ := 5
    let y : ℚ := 60*(n+1)
    0 < k ∧ ¬ Squarefree k.natAbs ∧ Int.ModEq 24 (k^2) 1 ∧ y^2 = x^3+(k:ℚ) ∧
    x.den.Coprime k.natAbs ∧
    ¬ IsSquare ((x.num : ZMod k.natAbs)*(x.den : ZMod k.natAbs)⁻¹) := by
  dsimp only
  have repr : (parameter n : ℤ) = 24*(150*((n:ℤ)+1)^2-6)+19 := by
    unfold parameter
    push_cast
    ring
  have hk : (parameter n : ℤ) ≡ 19 [ZMOD 24] := by rw [repr]; simp [Int.ModEq]
  refine ⟨?_, not_squarefree n, (hk.pow 2).trans (by decide), ?_, by simp, ?_⟩
  · unfold parameter
    positivity
  · unfold parameter
    push_cast
    ring
  · simpa using nonsquare n

end MordellObstruction
#print axioms MordellObstruction.increasing
#print axioms MordellObstruction.rational_family
