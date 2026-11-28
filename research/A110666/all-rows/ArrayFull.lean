import OMAStatements.S_oeis_a110666

/-!
# All rows of Leroy Quet’s array A110665

Franklin T. Adams-Watters gave the initial-row formula and generating function
in May 2006. R. J. Mathar conjectured the rational forms for rows one through
three in October 2013. Colin Barker recorded the next four empirical row
generating functions in July 2014 and July 2016. The uniform row formula and
two-variable identity below use the source convention of indexing every row at zero.

The inversion lemmas are taken from the checked A110666 proof in commit
015ee5865f9802bbf12a6e8f7d5235a3b12de0c1. This file compiles directly
against OMAStatements.S_oeis_a110666.
-/

namespace MatharArraySource

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

end MatharArraySource

open MatharArraySource

/-
The complete array of iterated partial sums of A110665

The initial row and first cumulative row are the registered A110665 and A110666
sequences. The two-variable identity packages the successive cumulative rows
in a new variable Y, with coefficients that are power series in X.
-/
namespace MatharArray
open PowerSeries OMA.S_oeis_a110666

/-- Row zero of A110665 and its successive cumulative sums, each starting at index zero. -/
def row : ℕ → ℕ → ℤ
  | 0 => row0
  | m+1 => fun n => ∑ i ∈ Finset.range (n+1), row m i

/-- The construction has the two boundary conditions and Pascal rule of the source array. -/
theorem pascal (m n : ℕ) : row m 0 = 0 ∧
    row (m+1) (n+1) = row m (n+1) + row (m+1) n := by
  constructor
  · induction m with
    | zero => rw [row, row0]; simp
    | succ m ih => simp [row, ih]
  · change (∑ i ∈ Finset.range (n+1+1), row m i) = row m (n+1) + ∑ i ∈ Finset.range (n+1), row m i
    rw [Finset.sum_range_succ, add_comm]

theorem registered_row (n : ℕ) : row 1 n = a n := by
  induction n with
  | zero => simpa [a] using (pascal 1 0).1
  | succ n ih => rw [(pascal 0 n).2, ih, a]; rfl

private theorem row_diff (m : ℕ) : (1-X) * mk (row (m+1)) = mk (row m) := by
  rw [sub_mul, one_mul]
  ext n
  cases n with
  | zero => simp [(pascal (m+1) 0).1, (pascal m 0).1]
  | succ n => simp [coeff_succ_X_mul, (pascal m n).2]

/-- Every row is obtained by multiplying the initial series by (1−X) to power −m. -/
theorem row_series (m : ℕ) :
    mk (row m) = (invOneSubPow ℤ m).val * mk row0 := by
  induction m with
  | zero => simp [row, invOneSubPow_zero]
  | succ m ih =>
    calc
      _ = (invOneSubPow ℤ 1).val * ((1-X) * mk (row (m+1))) := by
        rw [← mul_assoc]
        have h := (invOneSubPow ℤ 1).val_inv
        rw [invOneSubPow_inv_eq_one_sub_pow, pow_one] at h
        simp [h]
      _ = _ := by rw [row_diff, ih, invOneSubPow_add, Units.val_mul]; ring

/-- The rational ordinary generating function of every cumulative row. -/
theorem row_rational (m : ℕ) :
    (1-X)^m * (1-X+X^2)^2 * mk (row m) = X * (1-2*X) := by
  rw [row_series, show (1-X)^m * (1-X+X^2)^2 * ((invOneSubPow ℤ m).val * mk row0) =
      (1-X+X^2)^2 * (((1-X)^m * (invOneSubPow ℤ m).val) * mk row0) by ring,
    ← invOneSubPow_inv_eq_one_sub_pow ℤ m, Units.inv_val, one_mul, Mathar.initial_row]

/-- Row index is the outer series variable. -/
noncomputable def table : PowerSeries (PowerSeries ℤ) := mk (fun m => mk (row m))

/-- (1−X−Y)(1−X+X²)² times the bivariate generating function equals
(1−X)X(1−2X). The outer X in Lean's notation is the row-index variable Y. -/
theorem bivariate :
    (C (1-X) - X) * C ((1-X+X^2)^2) * table =
      C ((1-X)*X*(1-2*X) : PowerSeries ℤ) := by
  have step : (C (1-X) - X)*table = C ((1-X)*mk row0) := by
    rw [sub_mul]
    ext1 m
    cases m with
    | zero => rw [map_sub, coeff_C_mul, coeff_zero_X_mul, sub_zero, coeff_zero_C, table, coeff_mk]; rfl
    | succ m =>
      rw [map_sub, coeff_C_mul, coeff_succ_X_mul, table, coeff_mk, coeff_mk, row_diff, sub_self, coeff_C]
      simp
  calc
    _ = C ((1-X+X^2)^2) * ((C (1-X) - X)*table) := by ring
    _ = _ := by
      rw [step, ← map_mul]
      apply congrArg C
      calc
        _ = (1-X) * ((1-X+X^2)^2 * mk row0) := by ring
        _ = _ := by rw [Mathar.initial_row]; ring

end MatharArray

namespace MatharArray
open PowerSeries OMA.S_oeis_a110666

/-- Coefficients of a generating series after `m` rounds of prefix summation. -/
theorem entries_of_series {a b : ℕ → ℤ} {m : ℕ} (hm : 1 ≤ m)
    (series : mk a = (invOneSubPow ℤ m).val * mk b) (n : ℕ) :
    a n = ∑ k ∈ Finset.range (n + 1), ((n - k + m - 1).choose (m - 1) : ℤ) * b k := by
  rw [mul_comm] at series
  have c := congrArg (coeff n) series
  rw [coeff_mk, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k j => coeff k (mk b) * coeff j (invOneSubPow ℤ m).val),
    invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℤ m hm] at c
  simp only [coeff_mk] at c
  refine c.trans (Finset.sum_congr rfl ?_)
  intro k _
  rw [show m - 1 + (n - k) = n - k + m - 1 by omega, mul_comm]

/-- Each entry is a binomially weighted sum of entries in row zero. -/
theorem entry (m n : ℕ) (hm : 1 ≤ m) :
    row m n = ∑ k ∈ Finset.range (n + 1), ((n - k + m - 1).choose (m - 1) : ℤ) * row0 k :=
  entries_of_series hm (row_series m) n

end MatharArray

namespace MatharArray
open PowerSeries OMA.S_oeis_a110666

/-- Periodic signs in the first row of A110665, as given by Franklin T. Adams-Watters. -/
def phase (n : ℕ) : ℤ :=
  match n % 6 with
  | 0 | 1 => 1
  | 3 | 4 => -1
  | _ => 0

private theorem phase_recurrence (n : ℕ) :
    let f := fun k : ℕ => (k : ℤ) * phase k
    f (n+4) - (f (n+3) + f (n+3)) + (f (n+2) + f (n+2) + f (n+2)) -
      (f (n+1) + f (n+1)) + f n = 0 := by
  dsimp only
  unfold phase
  have shift (k : ℕ) : (n + k) % 6 = (n % 6 + k) % 6 := (Nat.mod_add_mod n 6 k).symm
  rw [shift 4, shift 3, shift 2, shift 1]
  have h := Nat.mod_lt n (by decide : 0 < 6)
  generalize n % 6 = j at *
  interval_cases j <;> norm_num <;> ring

/-- The periodic candidate satisfies the initial row's inhomogeneous series equation. -/
theorem phase_series :
    (1-X+X^2)^2 * mk (fun n : ℕ => (n : ℤ) * phase n) = X*(1-2*X) := by
  let F := mk (fun n : ℕ => (n : ℤ) * phase n)
  change (1-X+X^2)^2 * F = X*(1-2*X)
  rw [show (1-X+X^2)^2 * F = F + X * (-(F+F) + X * (F+F+F + X * (-(F+F) + X*F))) by ring,
    show (1-2*X : PowerSeries ℤ) = 1-(X+X) by ring]
  ext n
  rcases n with _ | (_ | (_ | (_ | n)))
  all_goals simp only [map_add, map_sub, map_neg, coeff_zero_X_mul, coeff_succ_X_mul,
    coeff_X, coeff_one, F, coeff_mk, Nat.succ_ne_zero, if_false]
  · decide
  · decide
  · decide
  · decide
  · simp only [Nat.reduceEqDiff, if_false, sub_self, add_zero]
    rw [show n+1+1+1+1 = n+4 by omega]
    have h := phase_recurrence n
    dsimp only at h
    omega

/-- Adams-Watters's 2006 row-zero formula for A110665. -/
theorem row0_phase (n : ℕ) : row0 n = (n : ℤ) * phase n := by
  have q : (1-X+X^2)^2 ≠ (0 : PowerSeries ℤ) := by
    intro hz
    have h := congrArg constantCoeff hz
    simp at h
  have eq : mk row0 = mk (fun n : ℕ => (n : ℤ) * phase n) :=
    mul_left_cancel₀ q (Mathar.initial_row.trans phase_series.symm)
  simpa using congrArg (coeff n) eq

/-- A finite sum for every entry of a positive row using only its row and column indices. -/
theorem entry_closed (m n : ℕ) (hm : 1 ≤ m) :
    row m n = ∑ k ∈ Finset.range (n+1), ((n-k+m-1).choose (m-1) : ℤ) * (k * phase k) := by
  simpa only [row0_phase] using entry m n hm

end MatharArray
