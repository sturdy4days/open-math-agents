import OMAStatements.S_oeis_a106521
import Mathlib.Tactic

/-!
# Eleven consecutive squares whose sum is a square

This proves Vladeta Jovovic's generating function for OEIS A106521 with
Bruno Berselli's index shift. We follow the Pell descent suggested by
@SPatel2133 when formalizing the statement: the positive solutions come
from two seeds under multiplication by the norm-one unit `10+3√11`.
Their interleaving gives the increasing enumeration and its recurrence.
-/

namespace SquareRun

/-- Multiplication by the fundamental Pell unit `10+3√11`. -/
def step (p : ℕ×ℕ) : ℕ×ℕ := (10*p.1+33*p.2,3*p.1+10*p.2)

end SquareRun

namespace SquareRun

/-- Multiplication by `10 + 3√11` preserves the Pell equation of norm `−10`. -/
theorem step_solution (w t : ℕ) (eq : w ^ 2 + 10 = 11 * t ^ 2) :
    (step (w, t)).1 ^ 2 + 10 = 11 * (step (w, t)).2 ^ 2 := by
  dsimp [step]
  nlinarith only [eq]

private theorem small_pell : ∀ t : Fin 33, ∀ w : Fin 110,
    5 ≤ w.val → w.val ^ 2 + 10 = 11 * t.val ^ 2 →
    (w.val = 23 ∧ t.val = 7) ∨ (w.val = 43 ∧ t.val = 13) := by decide +kernel

/-- Inverse multiplication by the fundamental positive unit decreases the second
coordinate until the solution lies among the two starting pairs. -/
theorem classify (w t : ℕ) (hw : 5 ≤ w) (eq : w ^ 2 + 10 = 11 * t ^ 2) :
    ∃ i : ℕ, (step^[i]) (23, 7) = (w, t) ∨ (step^[i]) (43, 13) = (w, t) := by
  induction t using Nat.strong_induction_on generalizing w with
  | h t ih =>
    by_cases ht : t ≤ 32
    · have hbound : w < 110 := by
        by_contra! hn
        nlinarith only [eq, Nat.pow_le_pow_left ht 2, Nat.pow_le_pow_left hn 2]
      obtain h | h := small_pell ⟨t, by omega⟩ ⟨w, hbound⟩ hw eq
      · exact ⟨0, Or.inl (Prod.ext h.1.symm h.2.symm)⟩
      · exact ⟨0, Or.inr (Prod.ext h.1.symm h.2.symm)⟩
    · have posU : 33 * t + 5 ≤ 10 * w := by
        by_contra! hn
        have hs := Nat.pow_le_pow_left (Nat.le_of_lt hn) 2
        nlinarith only [eq, hs, Nat.zero_le ((t - 33) ^ 2), Nat.mul_le_mul (show 33 ≤ t by omega) (show 33 ≤ t by omega), Nat.mul_le_mul_left t (show 33 ≤ t by omega), (show 33 ≤ t by omega)]
      have posV : 3 * w ≤ 10 * t := by
        by_contra! hn
        nlinarith only [eq, Nat.pow_le_pow_left (Nat.le_of_lt hn) 2]
      have drops : 10 * t - 3 * w < t := by
        have hh : 3 * t < w := by
          by_contra! hn
          nlinarith only [eq, Nat.pow_le_pow_left hn 2,
            Nat.pow_le_pow_left (show 33 ≤ t by omega) 2]
        omega
      let u := 10 * w - 33 * t
      let v := 10 * t - 3 * w
      have hu : u + 33 * t = 10 * w := by dsimp [u]; omega
      have hv : v + 3 * w = 10 * t := by dsimp [v]; omega
      have back : step (u, v) = (w, t) := by
        apply Prod.ext <;> dsimp [step] <;> omega
      have euv : u ^ 2 + 10 = 11 * v ^ 2 := by
        obtain ⟨hw', ht'⟩ := Prod.ext_iff.mp back
        dsimp [step] at hw' ht'
        rw [← hw', ← ht'] at eq
        nlinarith only [eq]
      obtain ⟨i, hi | hi⟩ := ih v drops u (by dsimp [u]; omega) euv
      · exact ⟨i+1, Or.inl (by rw [Function.iterate_succ_apply', hi, back])⟩
      · exact ⟨i+1, Or.inr (by rw [Function.iterate_succ_apply', hi, back])⟩

end SquareRun

namespace SquareRun

def pair : ℕ → ℕ×ℕ
  | 0 => (23,7)
  | 1 => (43,13)
  | n+2 => step (pair n)

def start (n : ℕ) : ℕ := (pair n).1 - 5

theorem pair_even (r : ℕ) : pair (2*r) = (step^[r]) (23,7) := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Nat.mul_succ,pair,ih,Function.iterate_succ_apply']

theorem pair_odd (r : ℕ) : pair (2*r+1) = (step^[r]) (43,13) := by
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
    change 10*(pair n).1+33*(pair n).2 < 10*(pair (n+1)).1+33*(pair (n+1)).2 ∧
      3*(pair n).1+10*(pair n).2 < 3*(pair (n+1)).1+10*(pair (n+1)).2
    omega

theorem lower (n : ℕ) : 5 ≤ (pair n).1 :=
  le_trans (by decide : 5 ≤ (pair 0).1)
    ((strictMono_nat_of_lt_succ fun i => (pair_grows i).1).monotone (Nat.zero_le n))

theorem increasing : StrictMono start := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := (pair_grows n).1
  have bound := lower n
  unfold start
  omega

theorem recurrence (n : ℕ) :
    (start (n+4):ℤ) + start n = 20*(start (n+2):ℤ) + 90 := by
  simp only [start,Nat.cast_sub (lower _), Nat.cast_ofNat]
  have next : (pair (n+4)).1+(pair n).1=20*(pair (n+2)).1 := by
    change (10*(10*(pair n).1+33*(pair n).2)+33*(3*(pair n).1+10*(pair n).2))+
      (pair n).1=20*(10*(pair n).1+33*(pair n).2)
    ring
  have eq : ((pair (n+4)).1:ℤ)+(pair n).1=20*((pair (n+2)).1:ℤ) := by exact_mod_cast next
  linarith

theorem isSquare_run (m : ℕ) : IsSquare (∑ k ∈ Finset.range 11, (m+k)^2) ↔
    ∃ t : ℕ, (m+5)^2+10=11*t^2 := by
  have total : (∑ k ∈ Finset.range 11,(m+k)^2)=11*((m+5)^2+10) := by
    norm_num [Finset.sum_range_succ]
    ring
  rw [total]
  constructor
  · rintro ⟨y,hy⟩
    have dv0 : 11 ∣ y*y := hy ▸ dvd_mul_right _ _
    have dv : 11 ∣ y := ((Nat.Prime.dvd_mul (by decide : Nat.Prime 11)).mp dv0).elim id id
    obtain ⟨t,rfl⟩ := dv
    refine ⟨t,?_⟩
    nlinarith
  · rintro ⟨t,ht⟩
    exact ⟨11*t,by rw [ht]; ring⟩

end SquareRun

namespace SquareRun
open OMA.S_oeis_a106521

private theorem pair_solution (n : ℕ) :
    (pair n).1^2+10=11*(pair n).2^2 := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h _ =>
    change (10*(pair n).1+33*(pair n).2)^2+10=11*(3*(pair n).1+10*(pair n).2)^2
    nlinarith only [h]

/-- The ordered Pell list enumerates exactly the square runs. -/
theorem original_eq (covers : ∀ w t : ℕ, 5≤w → w^2+10=11*t^2 →
    ∃ r, (step^[r]) (23,7)=(w,t) ∨ (step^[r]) (43,13)=(w,t))
    (n : ℕ) : a (n+1)=start n := by
  let P (m : ℕ) := IsSquare (∑ k ∈ Finset.range 11,(m+k)^2)
  have eqrange : Set.range start=Set.ofPred P := by
    ext m
    change (∃ r, start r=m) ↔ IsSquare _
    rw [isSquare_run]
    constructor
    · rintro ⟨r,rfl⟩
      refine ⟨(pair r).2,?_⟩
      simpa [start,Nat.sub_add_cancel (lower r)] using pair_solution r
    · rintro ⟨t,ht⟩
      obtain ⟨r,h | h⟩ := covers (m+5) t (by omega) ht
      · exact ⟨2*r,by simp [start,pair_even,h]⟩
      · exact ⟨2*r+1,by simp [start,pair_odd,h]⟩
  have inf : (Set.ofPred P).Infinite := eqrange ▸ Set.infinite_range_of_injective increasing.injective
  have nth : Nat.nth P=start := ((Nat.nth_strictMono inf).range_inj increasing).mp
    ((Nat.range_nth_of_infinite inf).trans eqrange.symm)
  simpa [a,P] using congrFun nth n

end SquareRun

namespace SquareRun

open PowerSeries

/-- Subtracting successive instances of the inhomogeneous recurrence makes every
coefficient from degree six onward vanish. The six initial coefficients give the numerator. -/
theorem series (b : ℕ → ℤ) (h0 : b 0 = 0) (h1 : b 1 = 18) (h2 : b 2 = 38)
    (h3 : b 3 = 456) (h4 : b 4 = 854)
    (recurrence : ∀ n, b (n+5) + b (n+1) = 20 * b (n+3) + 90) :
    (1 - X) * (1 - 20 * X ^ 2 + X ^ 4) * mk b =
      (2 * X * (9 + 10 * X + 29 * X ^ 2 - X ^ 3 - 2 * X ^ 4) : PowerSeries ℤ) := by
  let B := mk b
  calc
    _ = B - X^1 * B - (20 : ℕ) • (X^2 * B) + (20 : ℕ) • (X^3 * B) +
        X^4 * B - X^5 * B := by dsimp [B]; simp only [nsmul_eq_mul]; ring
    _ = (18 : ℕ) • X^1 + (20 : ℕ) • X^2 + (58 : ℕ) • X^3 -
        (2 : ℕ) • X^4 - (4 : ℕ) • X^5 := by
      apply PowerSeries.ext
      intro n
      simp only [B, map_sub, map_add, map_nsmul, coeff_X_pow_mul', coeff_X_pow,
        coeff_mk]
      simp only [nsmul_eq_mul]
      by_cases small : n ≤ 5
      · have h5 := recurrence 0
        norm_num [h1, h3] at h5
        interval_cases n <;> norm_num [h0, h1, h2, h3, h4]
        omega
      · obtain ⟨k, rfl⟩ : ∃ k, n = k+6 := ⟨n-6, by omega⟩
        have r₀ := recurrence k
        have r₁ := recurrence (k+1)
        simp only [Nat.add_assoc] at r₁
        simp (disch := omega) [Nat.add_sub_assoc]
        change b (k+6) + b (k+2) = 20 * b (k+4) + 90 at r₁
        omega
    _ = _ := by simp only [nsmul_eq_mul]; ring

end SquareRun

open SquareRun OMA.S_oeis_a106521

theorem OMA.solution : type_of% @OMA.S_oeis_a106521.main := by
  have terms := original_eq classify
  apply series
  · simp [a]
  · change (a (0+1):ℤ)=18
    rw [terms]
    decide
  · change (a (1+1):ℤ)=38
    rw [terms]
    decide
  · change (a (2+1):ℤ)=456
    rw [terms]
    decide
  · change (a (3+1):ℤ)=854
    rw [terms]
    decide
  · intro n
    change (a ((n+4)+1) : ℤ) + a (n+1) = 20*(a ((n+2)+1) : ℤ)+90
    simp only [terms]
    exact recurrence n
