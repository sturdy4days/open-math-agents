import OMAStatements.S_oeis_a154142
import Mathlib.Tactic

/-!
# Triangular numbers nine below a square

We prove the recurrence and the rational generating function recorded in
R. J. Mathar's OEIS A154142. Robert Israel identified the Pell mechanism;
we follow the explicit descent in @SPatel2133's formalization plan.
The intermediate recurrence is the one given by Ctibor O. Zizka.
-/

namespace TrianglePell

/-- The positive Pell step for a triangular index and its square root. -/
def step (p : ℕ × ℕ) : ℕ × ℕ := (3*p.1+4*p.2+1,2*p.1+3*p.2+1)

end TrianglePell

namespace TrianglePell

/-- The affine Pell step preserves the equation for a triangular number plus nine. -/
theorem step_solution (k m : ℕ) (eq : k ^ 2 + k + 18 = 2 * m ^ 2) :
    (step (k,m)).1 ^ 2 + (step (k,m)).1 + 18 = 2 * (step (k,m)).2 ^ 2 := by
  dsimp [step]
  nlinarith only [eq]

private theorem small_solutions : ∀ k m : Fin 13,
    k.val ^ 2 + k.val + 18 = 2 * m.val ^ 2 →
    (k.val = 0 ∧ m.val = 3) ∨ (k.val = 10 ∧ m.val = 8) := by decide +kernel

/-- Past the two seeds, the inverse affine step is nonnegative and reduces the
triangular index, so the forward iterates exhaust all solutions. -/
theorem classify (k m : ℕ) (eq : k ^ 2 + k + 18 = 2 * m ^ 2) :
    ∃ i : ℕ, (step^[i]) (0,3) = (k,m) ∨ (step^[i]) (10,8) = (k,m) := by
  induction k using Nat.strong_induction_on generalizing m with
  | h k ih =>
    by_cases hk : k ≤ 12
    · have hm : m < 13 := by
        by_contra! hn
        nlinarith only [eq, hk, Nat.pow_le_pow_left hk 2, Nat.pow_le_pow_left hn 2]
      obtain h | h := small_solutions ⟨k, by omega⟩ ⟨m, hm⟩ eq
      · exact ⟨0, Or.inl (Prod.ext h.1.symm h.2.symm)⟩
      · exact ⟨0, Or.inr (Prod.ext h.1.symm h.2.symm)⟩
    · have large : 13 ≤ k := by omega
      have posU : 4 * m ≤ 3 * k + 1 := by
        apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
        nlinarith only [eq, large, Nat.mul_le_mul_left k large]
      have posV : 2 * k + 1 ≤ 3 * m := by
        apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
        nlinarith only [eq, Nat.zero_le (k ^ 2), Nat.zero_le k]
      have short : 2 * k + 1 < 4 * m := by
        apply (Nat.pow_lt_pow_iff_left (by decide : 2 ≠ 0)).mp
        nlinarith only [eq, Nat.zero_le (k ^ 2), Nat.zero_le k]
      let u := 3 * k + 1 - 4 * m
      let v := 3 * m - (2 * k + 1)
      have hu : u + 4 * m = 3 * k + 1 := Nat.sub_add_cancel posU
      have hv : v + (2 * k + 1) = 3 * m := Nat.sub_add_cancel posV
      have back : step (u,v) = (k,m) := by
        apply Prod.ext <;> dsimp [step] <;> omega
      have euv : u ^ 2 + u + 18 = 2 * v ^ 2 := by
        obtain ⟨hk',hm'⟩ := Prod.ext_iff.mp back
        dsimp [step] at hk' hm'
        rw [← hk', ← hm'] at eq
        nlinarith only [eq]
      obtain ⟨i, hi | hi⟩ := ih u (by omega) v euv
      · exact ⟨i+1, Or.inl (by rw [Function.iterate_succ_apply', hi, back])⟩
      · exact ⟨i+1, Or.inr (by rw [Function.iterate_succ_apply', hi, back])⟩

end TrianglePell

namespace TrianglePell

/-- Apply the same positive step to the two interleaved seed orbits. -/
def pair : ℕ → ℕ × ℕ
  | 0 => (0,3)
  | 1 => (10,8)
  | n+2 => step (pair n)

def start (n : ℕ) : ℕ := (pair n).1

private theorem pair_even (r : ℕ) : pair (2*r) = (step^[r]) (0,3) := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Nat.mul_succ,pair,ih,Function.iterate_succ_apply']

private theorem pair_odd (r : ℕ) : pair (2*r+1) = (step^[r]) (10,8) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [show 2*(r+1)+1=(2*r+1)+2 by omega,pair,ih,Function.iterate_succ_apply']

private theorem pair_grows (n : ℕ) :
    (pair n).1 < (pair (n+1)).1 ∧ (pair n).2 < (pair (n+1)).2 := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h _ =>
    change 3*(pair n).1+4*(pair n).2+1 < 3*(pair (n+1)).1+4*(pair (n+1)).2+1 ∧
      2*(pair n).1+3*(pair n).2+1 < 2*(pair (n+1)).1+3*(pair (n+1)).2+1
    omega

private theorem increasing : StrictMono start := strictMono_nat_of_lt_succ fun n => (pair_grows n).1

private theorem triangular_square (k : ℕ) : IsSquare (9 + k*(k+1)/2) ↔
    ∃ m : ℕ, k^2+k+18=2*m^2 := by
  have h := Nat.div_mul_cancel (Nat.two_dvd_mul_add_one k)
  constructor
  · rintro ⟨m,hm⟩
    exact ⟨m,by nlinarith only [hm,h]⟩
  · rintro ⟨m,hm⟩
    exact ⟨m,by nlinarith only [hm,h]⟩

private theorem pair_solution (n : ℕ) :
    (pair n).1^2 + (pair n).1 + 18 = 2*(pair n).2^2 := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h _ =>
    change (3*(pair n).1+4*(pair n).2+1)^2+(3*(pair n).1+4*(pair n).2+1)+18=
      2*(2*(pair n).1+3*(pair n).2+1)^2
    nlinarith only [h]

/-- Eliminate the second coordinate of the positive Pell step. -/
theorem recurrence (n : ℕ) :
    (start (n+4):ℤ) + start n = 6*(start (n+2):ℤ) + 2 := by
  have h : start (n+4)+start n = 6*start (n+2)+2 := by
    change 3*(3*(pair n).1+4*(pair n).2+1)+4*(2*(pair n).1+3*(pair n).2+1)+1+
      (pair n).1=6*(3*(pair n).1+4*(pair n).2+1)+2
    ring
  exact_mod_cast h

/-- The increasing forward orbit enumeration agrees with the registered `Nat.nth`. -/
theorem original_eq (covers : ∀ k m : ℕ, k^2+k+18=2*m^2 →
    ∃ r, (step^[r]) (0,3)=(k,m) ∨ (step^[r]) (10,8)=(k,m)) (n : ℕ) :
    OMA.S_oeis_a154142.a (n+1)=start n := by
  let P (k : ℕ) := IsSquare (9+k*(k+1)/2)
  have eqrange : Set.range start = Set.ofPred P := by
    ext k
    change (∃ r, start r=k) ↔ IsSquare _
    rw [triangular_square]
    constructor
    · rintro ⟨r,rfl⟩
      exact ⟨(pair r).2,pair_solution r⟩
    · rintro ⟨m,hm⟩
      obtain ⟨r,h | h⟩ := covers k m hm
      · exact ⟨2*r,by simp [start,pair_even,h]⟩
      · exact ⟨2*r+1,by simp [start,pair_odd,h]⟩
  have infinite : (Set.ofPred P).Infinite := eqrange ▸ Set.infinite_range_of_injective increasing.injective
  have nth : Nat.nth P=start := ((Nat.nth_strictMono infinite).range_inj increasing).mp
    ((Nat.range_nth_of_infinite infinite).trans eqrange.symm)
  simpa [OMA.S_oeis_a154142.a,P] using congrFun nth n

end TrianglePell

namespace TrianglePell
open PowerSeries

/-- The six index values through degree five determine the numerator. The
recurrence is needed only in degrees at least six. -/
theorem series (a : ℕ → ℤ) (h0 : a 0 = 0) (h1 : a 1 = 0) (h2 : a 2 = 10)
    (h3 : a 3 = 13) (h4 : a 4 = 63) (h5 : a 5 = 80)
    (recurrence : ∀ n : ℕ, 5 < n →
      a n = a (n-1) + 6*a (n-2) - 6*a (n-3) - a (n-4) + a (n-5)) :
    (1-X) * (X^2-2*X-1) * (X^2+2*X-1) * mk a =
      (X^2 * (10+3*X-10*X^2-X^3) : PowerSeries ℤ) := by
  let A := mk a
  calc
    _ = A - X^1*A - (6 : ℕ) • (X^2*A) + (6 : ℕ) • (X^3*A) + X^4*A - X^5*A := by
          dsimp [A]; simp only [nsmul_eq_mul]; ring
    _ = (10 : ℕ) • X^2 + (3 : ℕ) • X^3 - (10 : ℕ) • X^4 - X^5 := by
      apply PowerSeries.ext
      intro n
      simp only [A, map_sub, map_add, map_nsmul, coeff_X_pow_mul', coeff_X_pow, coeff_mk]
      simp only [nsmul_eq_mul]
      by_cases small : n ≤ 5
      · interval_cases n <;> norm_num [h0,h1,h2,h3,h4,h5]
      · have r := recurrence n (by omega)
        simp (disch := omega)
        omega
    _ = _ := by simp only [nsmul_eq_mul]; ring

end TrianglePell

open TrianglePell OMA.S_oeis_a154142

theorem OMA.solution : type_of% @OMA.S_oeis_a154142.main := by
  have terms := original_eq classify
  have rec5 (n : ℕ) (hn : 5 < n) : (a n : ℤ) = a (n-1) + 6*a (n-2) - 6*a (n-3) - a (n-4) + a (n-5) := by
    obtain ⟨r,rfl⟩ : ∃ r, n=r+6 := ⟨n-6,by omega⟩
    change (a ((r+5)+1) : ℤ) = a ((r+4)+1) + 6*a ((r+3)+1) - 6*a ((r+2)+1) - a ((r+1)+1) + a (r+1)
    simp only [terms]
    have h₀ := recurrence r
    have h₁ := recurrence (r+1)
    change (start (r+5):ℤ) + start (r+1) = 6*(start (r+3):ℤ) + 2 at h₁
    linarith
  refine ⟨rec5, series (fun n => (a n:ℤ)) ?_ ?_ ?_ ?_ ?_ ?_ rec5⟩
  · simp [a]
  · change (a (0+1):ℤ)=0
    rw [terms]; decide
  · change (a (1+1):ℤ)=10
    rw [terms]; decide
  · change (a (2+1):ℤ)=13
    rw [terms]; decide
  · change (a (3+1):ℤ)=63
    rw [terms]; decide
  · change (a (4+1):ℤ)=80
    rw [terms]; decide
