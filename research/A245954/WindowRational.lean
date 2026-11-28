import AllWindowLengths
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.PowerSeries.Trunc

namespace WindowFour
open PowerSeries

/-- The ordinary generating function in the alphabet endpoint, starting at n=0. -/
noncomputable def alphabetSeries (k : ℕ) : PowerSeries ℚ :=
  mk (fun n => ((∑ x : Fin k → Fin (n+1), if validWord n k [] x then 1 else 0 : ℕ):ℚ))

private theorem stride (f : PowerSeries ℚ) (p : Polynomial ℚ) (d : ℕ) (b : ℚ)
    (h : ∀ m : ℕ, coeff (2*m+d) f = p.eval ((m:ℚ)+b)) (r m : ℕ) :
    coeff (2*(m+r)+d) (f*((1-X^2)^r)) =
      (fwdDiff (1:ℚ))^[r] p.eval ((m:ℚ)+b) := by
  induction r generalizing m with
  | zero => simpa using h m
  | succ r ih =>
    rw [pow_succ,←mul_assoc,mul_sub,mul_one,map_sub]
    have top := ih (m+1)
    have bottom := ih m
    have eq1 : 2*(m+(r+1))+d = 2*((m+1)+r)+d := by omega
    have eq2 : 2*(m+(r+1))+d = (2*(m+r)+d)+2 := by omega
    rw [eq2,coeff_mul_X_pow,bottom,←eq2,eq1,top,Function.iterate_succ_apply']
    simp [fwdDiff, add_assoc, add_comm]

private theorem tails (k : ℕ) (m : ℕ) :
    coeff (2*(m+(k+1))) (alphabetSeries k * (1-X^2)^(k+1)) = 0 ∧
    coeff (2*(m+(k+1))+1) (alphabetSeries k * (1-X^2)^(k+1)) = 0 := by
  have even (i : ℕ) : coeff (2*i+0) (alphabetSeries k) =
      (windowPolynomial k true).eval ((i:ℚ)+0) := by
    rw [Nat.add_zero,alphabetSeries,coeff_mk,sliding_four_all_lengths (2*i) k]
    simp [show (2*i+1)/2=i by omega]
  have odd (i : ℕ) : coeff (2*i+1) (alphabetSeries k) =
      (windowPolynomial k false).eval ((i:ℚ)+1) := by
    rw [alphabetSeries,coeff_mk,sliding_four_all_lengths]
    rw [show (2*i+1)%2=1 by omega,show (2*i+1+1)/2=i+1 by omega]
    simp
  have last (mid : Bool) := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
    (Nat.lt_succ_of_le (degree_bound k mid))
  constructor
  · simpa [last] using stride (alphabetSeries k) _ 0 0 even (k+1) m
  · simpa [last] using stride (alphabetSeries k) _ 1 1 odd (k+1) m

/-- A common denominator (1-X²)^(k+1) works for every word length, and its numerator
has degree strictly below 2(k+1). -/
theorem rational_all_lengths (k : ℕ) :
    ∃ p : Polynomial ℚ, p.natDegree < 2*(k+1) ∧
      alphabetSeries k * (1-X^2)^(k+1) = (p : PowerSeries ℚ) := by
  let f := alphabetSeries k * (1-X^2)^(k+1)
  refine ⟨trunc (2*(k+1)) f, ?_, ?_⟩
  · rw [show 2*(k+1)=(2*k+1)+1 by omega]
    exact natDegree_trunc_lt _ _
  · apply PowerSeries.ext
    intro n
    change coeff n f = _
    rw [Polynomial.coeff_coe,coeff_trunc]
    split
    · rfl
    · rename_i hn
      let m := n/2-(k+1)
      rcases (show n=2*(m+(k+1)) ∨ n=2*(m+(k+1))+1 by dsimp [m]; omega) with eq|eq
      · simpa only [eq] using (tails k m).1
      · simpa only [eq] using (tails k m).2

end WindowFour
#print axioms WindowFour.rational_all_lengths
