import OMAStatements.S_oeis_a344719
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic

/-! The proposed generating series for A344719 uniquely encodes the seven
initial values and the ceiling formula. The geometric optimization problem is
concentrated in those exact values and the striped witnesses. -/

namespace OMA.A344719Series
open PowerSeries

/-- Coefficient sequence specified by the conjectured series. -/
def target (n : ℕ) : ℕ :=
  if n < 7 then [0,1,2,5,8,11,17][n]! else ((n+2)^2+2)/3-6

private noncomputable def den : PowerSeries ℤ := (1-X)^3 * (1+X+X^2)
private noncomputable def num : PowerSeries ℤ := X * (1+2*X^2-X^3+X^5-2*X^6+3*X^7-3*X^8+2*X^9-X^10)

def Formula (f : ℕ → ℕ) : Prop := den * PowerSeries.mk (fun n => (f n : ℤ)) = num

private theorem add_three (n : ℕ) (hn : 7 ≤ n) : target (n+3) = target n + 2*n+7 := by
  have h₁ : (n+3+2)^2+2 = (n+2)^2+2+(2*n+7)*3 := by ring
  have h₂ : (n+2)^2 ≥ 64 := by nlinarith [Nat.zero_le ((n-7)*(n-7))]
  simp only [target, if_neg (by omega : ¬n+3<7), if_neg (by omega : ¬n<7), h₁,
    Nat.add_mul_div_right _ _ (by decide : 0<3)]
  omega

private theorem den_apply (s : PowerSeries ℤ) : den*s =
    s-X^1*s-X^1*s+X^2*s-X^3*s+X^4*s+X^4*s-X^5*s := by unfold den; ring

private theorem num_expand : num = ((X^1 + X^3 + X^3 - X^4 + X^6 - X^7 - X^7
    + X^8 + X^8 + X^8 - X^9 - X^9 - X^9 + X^10 + X^10 - X^11) : PowerSeries ℤ) := by
  unfold num; ring

theorem series_target : Formula target := by
  unfold Formula
  ext n
  rw [den_apply, num_expand]
  simp only [map_add, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  by_cases small : n < 12
  · interval_cases n <;> norm_num [target]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m+5 := ⟨n-5, by omega⟩
    have h₁ := add_three m (by omega)
    have h₂ := add_three (m+1) (by omega)
    have h₃ := add_three (m+2) (by omega)
    rw [show m+1+3=m+4 by omega] at h₂
    rw [show m+2+3=m+5 by omega] at h₃
    simp (disch := omega) only [if_pos, if_neg,
      show m+5-1=m+4 by omega, show m+5-2=m+3 by omega, show m+5-3=m+2 by omega,
      show m+5-4=m+1 by omega, show m+5-5=m by omega]
    omega

/-- The generating function is equivalent to term-by-term equality, in both
directions and without any enumeration of paintings. -/
theorem formula_iff (f : ℕ → ℕ) : Formula f ↔ ∀ n, f n = target n := by
  constructor
  · intro hf n
    have hden : den ≠ 0 := by
      intro hh
      have h := congrArg PowerSeries.constantCoeff hh
      norm_num [den] at h
    have he := mul_left_cancel₀ hden (hf.trans series_target.symm)
    have h := congrArg (PowerSeries.coeff (R := ℤ) n) he
    simpa using h
  · intro hf
    rw [show f = target from funext hf]
    exact series_target

end OMA.A344719Series

/-! An exact reduction of the three conjunctions in the registered A344719
conjecture to striped optimality, the seven initial values and the tail formula. -/

namespace OMA.A344719Series
open OMA.S_oeis_a344719

def StripedOptimal : Prop := ∀ n : ℕ, 6 ≤ n → ∃ painted : Finset (Cell n),
  Fair painted ∧ Striped painted ∧ painted.card = a n

def InitialValues : Prop := ∀ n : Fin 7, a n = [0,1,2,5,8,11,17][n.val]!

def TailValues : Prop := ∀ n : ℕ, 7 ≤ n → a n = ((n+2)^2+2)/3-6

/-- The formal power-series identity by itself forces the entire numerical
claim, including seven initial coefficients that are absent from the tail. -/
theorem series_iff_initial_and_tail : Formula a ↔ InitialValues ∧ TailValues := by
  rw [formula_iff]
  constructor
  · intro h
    constructor
    · intro n
      simpa only [target, if_pos n.isLt] using h n
    · intro n hn
      simpa only [target, if_neg (by omega : ¬n<7)] using h n
  · rintro ⟨hi, ht⟩ n
    by_cases hn : n < 7
    · simpa only [target, if_pos hn] using hi ⟨n,hn⟩
    · simpa only [target, if_neg hn] using ht n (by omega)

/-- Exact equivalence with the project statement. -/
theorem original_iff : (type_of% @OMA.S_oeis_a344719.main) ↔
    StripedOptimal ∧ InitialValues ∧ TailValues := by
  constructor
  · rintro ⟨hs, _, hf⟩
    exact ⟨hs, series_iff_initial_and_tail.mp hf⟩
  · rintro ⟨hs, hi, ht⟩
    exact ⟨hs, ht, series_iff_initial_and_tail.mpr ⟨hi, ht⟩⟩

end OMA.A344719Series
