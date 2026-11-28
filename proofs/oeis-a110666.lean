import OMAStatements.S_oeis_a110666

/-!
# Mathar's two formulas for A110666

R. J. Mathar conjectured the row-one generating function and the coefficient
identity at OEIS A110666 in 2013. Franklin T. Adams-Watters gave the rational
generating function of the initial row at A110665 in 2006. We derive it directly
from the defining recurrence. The coefficient of degree l in
(1-2X)/(1-X)^(l+1) vanishes for positive l by central binomial symmetry.
This diagonal identity inverts the triangular system at every finite degree.
-/

namespace Mathar
open PowerSeries

theorem diagonal (l : ℕ) : coeff l ((1 - 2 * X) * (invOneSubPow ℤ (l + 1)).val) =
    (if l = 0 then 1 else 0) := by
  rw [sub_mul, one_mul, two_mul, add_mul, map_sub, map_add,
    invOneSubPow_val_succ_eq_mk_add_choose]
  cases l with
  | zero => simp
  | succ l =>
    simp only [coeff_succ_X_mul, coeff_mk, Nat.succ_ne_zero, if_false]
    have symmetry : (l + 1 + l).choose (l + 1) = (l + 1 + l).choose l :=
      Nat.choose_symm_add
    rw [show l.succ + l.succ = (l + 1 + l) + 1 by omega, Nat.choose_succ_succ',
      ← symmetry, Nat.cast_add]
    exact sub_self _

theorem row_coeff {n k : ℕ} (hk : k ≤ n + 1) :
    coeff (n + 1 - k) (invOneSubPow ℤ (n + 1)).val =
      ((2 * (n + 1) - k - 1).choose n : ℤ) := by
  rw [invOneSubPow_val_succ_eq_mk_add_choose, coeff_mk,
    show n + (n + 1 - k) = 2 * (n + 1) - k - 1 by omega]

end Mathar

namespace Mathar
open PowerSeries

/-- Truncate the derivative of the geometric series after substituting t = X(1-X). -/
noncomputable def approx (m : ℕ) : PowerSeries ℤ :=
  ∑ j ∈ Finset.range m, C ((j : ℤ)+1) *
    (X ^ (j+1) * ((1-2*X) * (1-X)^j))

private lemma finite_deriv [CommRing R] (t : R) (m : ℕ) :
    (1-t)^2 * (∑ j ∈ Finset.range m, ((j:R)+1)*t^j) =
      1 - ((m:R)+1)*t^m + (m:R)*t^(m+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

private lemma approx_factor (m : ℕ) :
    approx m = X*(1-2*X) *
      ∑ j ∈ Finset.range m, ((j : PowerSeries ℤ)+1) * (X*(1-X))^j := by
  unfold approx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_add, map_natCast, map_one, mul_pow, pow_succ]
  ring

/-- The discrepancy from the rational numerator starts in degree m+1. -/
theorem approx_series (m : ℕ) : coeff m ((1-X+X^2)^2 * approx m) =
    coeff m (X*(1-2*X) : PowerSeries ℤ) := by
  rw [approx_factor]
  let t : PowerSeries ℤ := X*(1-X)
  have h : (1-X+X^2:PowerSeries ℤ)=1-t := by dsimp [t]; ring
  rw [h]
  change coeff m ((1-t)^2 * (X*(1-2*X) *
    ∑ j ∈ Finset.range m, ((j:PowerSeries ℤ)+1)*t^j)) = _
  rw [show (1-t)^2 * (X*(1-2*X) * ∑ j ∈ Finset.range m, ((j:PowerSeries ℤ)+1)*t^j) =
      X*(1-2*X) * ((1-t)^2 * ∑ j ∈ Finset.range m, ((j:PowerSeries ℤ)+1)*t^j) by ring,
      finite_deriv]
  have van (f : PowerSeries ℤ) : coeff m (X * t^m * f)=0 := by
    dsimp [t]
    rw [mul_pow, show X * (X^m*(1-X)^m) * f = X^(m+1) * ((1-X)^m*f) by ring]
    simp [coeff_X_pow_mul']
  have hh : X*(1-2*X)*(1-((m:PowerSeries ℤ)+1)*t^m+(m:PowerSeries ℤ)*t^(m+1)) =
      X*(1-2*X) - X*t^m*((1-2*X)*((m:PowerSeries ℤ)+1)) +
      X*t^m*((1-2*X)*(m:PowerSeries ℤ)*t) := by ring
  rw [hh, map_add, map_sub, van, van, sub_zero, add_zero]

/-- Multiplication up to degree n only depends on the coefficients through n. -/
theorem coeff_congr_right (d f g : PowerSeries ℤ) (n : ℕ)
    (h : ∀ k ≤ n, coeff k f = coeff k g) : coeff n (d*f) = coeff n (d*g) := by
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro x hx
  have hh := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rw [h x.2 (by omega)]

end Mathar

namespace Mathar
open PowerSeries

private theorem contribution (j n : ℕ) :
    coeff n (C ((j:ℤ)+1) * (X^(j+1)*((1-2*X)*(1-X)^j)) * (invOneSubPow ℤ n).val) =
    (if j+1=n then (n:ℤ) else 0) := by
  rw [show C ((j:ℤ)+1) * (X^(j+1)*((1-2*X)*(1-X)^j)) * (invOneSubPow ℤ n).val =
    C ((j:ℤ)+1) * (X^(j+1) * ((1-2*X)*((1-X)^j * (invOneSubPow ℤ n).val))) by ring,
    coeff_C_mul, coeff_X_pow_mul']
  by_cases h : j+1 ≤ n
  · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [if_pos (by omega), Nat.add_sub_cancel_left,
      show j+1+l=(l+1)+j by omega,
      one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val, diagonal]
    cases l <;> simp <;> omega
  · rw [if_neg h, if_neg (by omega), mul_zero]

/-- Under the triangular binomial transform the truncated row is n up to its cutoff. -/
theorem inversion (m n : ℕ) (hn : n ≤ m) :
    coeff n (approx m * (invOneSubPow ℤ n).val) = (n:ℤ) := by
  simp only [approx, Finset.sum_mul, map_sum, contribution]
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.add_right_cancel_iff, Finset.sum_ite_eq', Finset.mem_range,
      if_pos (show n < m by omega)]

end Mathar

namespace Mathar
open PowerSeries OMA.S_oeis_a110666

theorem recovers (f : PowerSeries ℤ) (M : ℕ)
    (h : ∀ n ≤ M, coeff n (f*(invOneSubPow ℤ n).val)=(n:ℤ)) :
    ∀ k ≤ M, coeff k f = row0 k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hM
    have conv := h k hM
    cases k with
    | zero =>
      rw [row0]
      simpa [invOneSubPow_zero] using conv
    | succ j =>
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun k l => coeff k f * coeff l (invOneSubPow ℤ (j+1)).val),
        Finset.sum_range_succ] at conv
      simp only [Nat.sub_self,invOneSubPow_val_succ_eq_mk_add_choose,coeff_mk,
        Nat.add_zero,Nat.choose_self,Nat.cast_one,mul_one] at conv
      rw [row0]
      have eq : (∑ k ∈ Finset.range (j+1), coeff k f * ((j+(j+1-k)).choose j : ℤ)) =
          ∑ k : Fin (j+1), ((2*(j+1)-k.val-1).choose j : ℤ)*row0 k.val := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i _
        have ar : j+(j+1-i.val) = 2*(j+1)-i.val-1 := by have := i.isLt; omega
        rw [ih i.val i.isLt (by have := i.isLt; omega), ar,mul_comm]
      rw [eq] at conv
      simp only [Nat.add_sub_cancel]
      omega

end Mathar

namespace Mathar
open PowerSeries OMA.S_oeis_a110666

/-- The A110665 generating function follows from its defining triangular system. -/
theorem initial_row : (1-X+X^2)^2 * mk row0 = X*(1-2*X) := by
  ext n
  calc
    _ = coeff n ((1-X+X^2)^2 * approx n) := by
      apply coeff_congr_right
      intro k hk
      simpa using (recovers (approx n) n (inversion n) k hk).symm
    _ = _ := approx_series n

end Mathar

namespace A110666Final
open PowerSeries OMA.S_oeis_a110666

private theorem first_difference :
    (1 - X) * mk a = mk row0 := by
  rw [sub_mul, one_mul]
  ext n
  cases n with
  | zero =>
    simp only [map_sub,coeff_mk,coeff_zero_X_mul,sub_zero]
    rw [a, row0]
    simp
  | succ k =>
    simp only [map_sub,coeff_succ_X_mul,coeff_mk]
    rw [a]
    abel

theorem from_row
    (hR : (1-X+X^2)^2 * mk row0 = X*(1-2*X)) :
    type_of% @OMA.S_oeis_a110666.main := by
  intro B C hB hC
  let G : PowerSeries ℤ := mk (fun _ => 1)
  have hG : (1-X)*G = 1 := by
    rw [sub_mul,one_mul]
    ext n
    cases n with
    | zero => simp [G]
    | succ k => simp [G,coeff_succ_X_mul,coeff_one]
  have hA : (1-X)*(1-X+X^2)^2 * mk a = X*(1-2*X) := by
    calc
      _ = (1-X+X^2)^2 * ((1-X)*mk a) := by ring
      _ = _ := by rw [first_difference,hR]
  constructor
  · linear_combination -hA
  have hn : (1-X)*(1-X+X^2)^2 ≠ (0 : PowerSeries ℤ) := by
    intro h
    have c := congrArg (PowerSeries.constantCoeff) h
    simp at c
  have he : mk a = -(X*B)+C-G := by
    apply mul_left_cancel₀ hn
    rw [hA]
    linear_combination (1-X)*(1-X+X^2)*X*hB - (1-X)*hC + (1-X+X^2)^2*hG
  intro n hp
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have c := congrArg (coeff (k+1)) he
  simpa [G,coeff_succ_X_mul] using c

end A110666Final

theorem OMA.solution : type_of% @OMA.S_oeis_a110666.main :=
  A110666Final.from_row Mathar.initial_row
