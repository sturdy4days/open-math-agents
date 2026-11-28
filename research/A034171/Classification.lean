import OMAStatements.S_oeis_a034171
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic

/-!
# The corrected prime-square congruence for OEIS A034171

For every prime p congruent to one modulo three, the registered sequence satisfies
a(pn) ≡ a(p)^n a(n) modulo p² for every positive n. The formula determines
exactly when a(pn) and a(n) differ modulo p² in terms of a(p), the divisibility
of n by p, and the base-p digits of n.

The arithmetic proof splits the numerator and the denominator into blocks of
length p. Within each block, pairing positions on either side of its excluded
multiple of p shows that the unit product is invariant under translation
by p modulo p². A product formula modulo p for the base-p digits follows
from the cubic generating function of the normalized coefficients.

The concrete counterexample p = 7, n = 50 to Peter Bala's stated congruence
was recorded during the formalization stage by @Solfanbtc. This file also gives
the multiplier 22 at p = 7 and the unbounded family n = 7^(s+2)+1.
-/

namespace TripleFactorial
open Finset

/-- An inverse to three modulo a modulus coprime to three. -/
private theorem inverse_three (d : ℕ) (h : Nat.Coprime 3 d) :
    ∃ x : ℕ, 3*x ≡ 1 [MOD d] := by
  have nd := (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mp h
  have ne : d % 3 ≠ 0 := fun s => nd (Nat.dvd_of_mod_eq_zero s)
  by_cases one : d % 3 = 1
  · refine ⟨(2*d+1)/3,?_⟩
    rw [show 3*((2*d+1)/3) = 2*d+1 by omega]
    simp [Nat.ModEq]
  · refine ⟨(d+1)/3,?_⟩
    rw [show 3*((d+1)/3) = d+1 by omega]
    simp [Nat.ModEq]

/-- The progression product becomes a rising factorial up to a power of three
after an invertible translation modulo any modulus coprime to three. -/
private theorem progression_mod {d x : ℕ} (hx : 3*x ≡ 1 [MOD d]) (n : ℕ) :
    (∏ i ∈ range n, (3*i+1)) ≡ 3^n * x.ascFactorial n [MOD d] := by
  induction n with
  | zero => simp [Nat.ModEq]
  | succ n ih =>
    rw [prod_range_succ,Nat.ascFactorial_succ,pow_succ]
    have term : 3*n+1 ≡ 3*(x+n) [MOD d] := by
      have h := hx.symm.add_left (3*n)
      convert h using 1; ring
    convert ih.mul term using 1; ring

/-- The natural division in the offset-one sequence is exact at every index. -/
theorem factorial_divides (n : ℕ) (hn : 0 < n) :
    n.factorial ∣ 3^(n-1) * ∏ i ∈ range n, (3*i+1) := by
  let d := n.factorial / 3^(n.factorial.factorization 3)
  have hc : Nat.Coprime 3 d := Nat.coprime_ordCompl (by decide) (Nat.factorial_ne_zero _)
  obtain ⟨x,hx⟩ := inverse_three d hc
  have hd : d ∣ n.factorial := Nat.ordCompl_dvd _ _
  have dv := hd.trans (Nat.factorial_dvd_ascFactorial x n)
  have hp : d ∣ ∏ i ∈ range n, (3*i+1) := Nat.modEq_zero_iff_dvd.mp
    ((progression_mod hx n).trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right dv _)))
  have exp := Nat.factorization_factorial_le_div_pred (by decide : Nat.Prime 3) n
  have e : n.factorial.factorization 3 ≤ n-1 := by omega
  have hprod : 3^(n.factorial.factorization 3)*d = n.factorial :=
    Nat.ordProj_mul_ordCompl_eq_self _ _
  rw [← hprod]
  exact Nat.mul_dvd_mul (pow_dvd_pow 3 e) hp
end TripleFactorial

namespace TripleFactorial
open Finset

def prog (n : ℕ) : ℕ := ∏ j ∈ range n, (3*j+1)
def up (j : ℕ) : ℕ := (21*j+1)*(21*j+4)*(21*j+10)*(21*j+13)*(21*j+16)*(21*j+19)
def down (j : ℕ) : ℕ := (7*j+1)*(7*j+2)*(7*j+3)*(7*j+4)*(7*j+5)*(7*j+6)

theorem blocks_up (n : ℕ) : prog (7*n) = 7^n * prog n * ∏ j ∈ range n, up j := by
  induction n with
  | zero => simp [prog]
  | succ n ih =>
    have step (k : ℕ) : prog (k+1) = prog k * (3*k+1) := Finset.prod_range_succ _ _
    rw [show 7*(n+1) = 7*n+7 by omega]
    simp only [show 7*n+7 = (7*n+6)+1 from rfl, step,prod_range_succ,pow_succ, ih,up]
    ring

theorem blocks_down (n : ℕ) : (7*n).factorial = 7^n * n.factorial * ∏ j ∈ range n, down j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 7*(n+1) = 7*n+7 by omega]
    simp only [show 7*n+7 = (7*n+6)+1 from rfl,Nat.factorial_succ,prod_range_succ,pow_succ,ih,down]
    ring

theorem block_residues (j : ℕ) : up j ≡ 6 [MOD 49] ∧ down j ≡ 34 [MOD 49] := by
  have h : ∀ k : ZMod 49,
      (21*k+1)*(21*k+4)*(21*k+10)*(21*k+13)*(21*k+16)*(21*k+19) = 6 ∧
      (7*k+1)*(7*k+2)*(7*k+3)*(7*k+4)*(7*k+5)*(7*k+6) = 34 := by decide
  obtain ⟨u,v⟩ := h j
  constructor
  · apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa [up] using u
  · apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa [down] using v

end TripleFactorial

namespace TripleFactorial
open Finset

theorem product_residues (n : ℕ) :
    (∏ j ∈ range n, up j) ≡ 6^n [MOD 49] ∧
    (∏ j ∈ range n, down j) ≡ 34^n [MOD 49] := by
  induction n with
  | zero => simp [Nat.ModEq]
  | succ n ih =>
    simp only [prod_range_succ,pow_succ]
    exact ⟨ih.1.mul (block_residues n).1, ih.2.mul (block_residues n).2⟩

/-- Removing the multiples of seven in each block of seven leaves a copy
of the original factorial quotient. The remaining factors have unit denominator. -/
theorem lift_seven {a : ℕ → ℕ} (repr : ∀ n, 0 < n →
    a n * n.factorial = 3^(n-1)*prog n) {n : ℕ} (hn : 0 < n) :
    a (7*n) ≡ 22^n * a n [MOD 49] := by
  let U := ∏ j ∈ range n, up j
  let V := ∏ j ∈ range n, down j
  have power : 3^(7*n-1) = 3^(n-1)*(3^6)^n := by
    rw [← pow_mul,← pow_add]
    congr 1; omega
  have cert : (a (7*n)*V)*(7^n*n.factorial) =
      (a n*(3^6)^n*U)*(7^n*n.factorial) := calc
    _ = a (7*n)*(7*n).factorial := by rw [blocks_down]; dsimp [V]; ring
    _ = 3^(7*n-1)*prog (7*n) := repr _ (by omega)
    _ = (a n*n.factorial)*((3^6)^n*7^n*U) := by
      rw [repr n hn,power,blocks_up]; dsimp [U]; ring
    _ = _ := by ring
  have pos : 0 < 7^n*n.factorial := by positivity
  have eq := Nat.eq_of_mul_eq_mul_right pos cert
  obtain ⟨u,v⟩ := product_residues n
  have single : (3^6*6 : ℕ) ≡ 22*34 [MOD 49] := by decide
  have multiplier : (3^6)^n * 6^n ≡ 22^n*34^n [MOD 49] := by
    simpa only [mul_pow] using single.pow n
  apply Nat.ModEq.cancel_right_of_coprime (show Nat.Coprime 49 (34^n) from
      (by decide : Nat.Coprime 49 34).pow_right n)
  calc
    a (7*n)*34^n ≡ a (7*n)*V [MOD 49] := v.symm.mul_left _
    _ = a n*(3^6)^n*U := eq
    _ ≡ a n*(3^6)^n*6^n [MOD 49] := u.mul_left _
    _ = a n*((3^6)^n*6^n) := by ring
    _ ≡ a n*(22^n*34^n) [MOD 49] := multiplier.mul_left _
    _ = 22^n*a n*34^n := by ring

end TripleFactorial

namespace TripleFactorial
open Finset

theorem adjacent {a : ℕ → ℕ} (repr : ∀ n, 0 < n →
    a n * n.factorial = 3^(n-1)*prog n) {n : ℕ} (hn : 0 < n) :
    a (n+1)*(n+1) = a n*(9*n+3) := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos n)
  calc
    _ = a (n+1)*(n+1).factorial := by rw [Nat.factorial_succ]; ring
    _ = 3^n * (prog n*(3*n+1)) := by
      rw [repr (n+1) (by omega)]; simp [prog,prod_range_succ]
    _ = (a n*n.factorial)*(9*n+3) := by
      have p : (3 : ℕ)^n = 3^(n-1)*3 := by rw [← pow_succ]; congr 1; omega
      rw [p,repr n hn]; ring
    _ = _ := by ring

private theorem pow_mod (n : ℕ) : 22^(7*n) ≡ 1 [MOD 49] := by
  have b : (22 : ℕ)^7 ≡ 1 [MOD 49] := by decide
  simpa only [pow_mul,one_pow] using b.pow n

theorem at_powers {a : ℕ → ℕ} (repr : ∀ n, 0 < n →
    a n * n.factorial = 3^(n-1)*prog n) (a1 : a 1=1) (s : ℕ) :
    a (7^(s+1)) ≡ 22 [MOD 49] := by
  induction s with
  | zero => simpa only [Nat.zero_add, pow_one, mul_one, a1] using
      (lift_seven repr (n:=1) (by decide))
  | succ s ih =>
    have b : 22^(7^(s+1)) ≡ 1 [MOD 49] := by
      simpa only [pow_succ', mul_comm 7] using pow_mod (7^s)
    have l := lift_seven repr (n:=7^(s+1)) (by positivity)
    rw [pow_succ' 7 (s+1)]
    exact l.trans (by simpa only [one_mul] using b.mul ih)

/-- For every s the indices 7^(s+2)+1 and seven times that index have
different residues modulo 49. -/
theorem infinite_pattern {a : ℕ → ℕ} (repr : ∀ n, 0 < n →
    a n * n.factorial = 3^(n-1)*prog n) (a1 : a 1=1) (s : ℕ) :
    a (7^(s+2)+1) ≡ 17 [MOD 49] ∧ a (7*(7^(s+2)+1)) ≡ 31 [MOD 49] := by
  let t := 7^(s+2)
  have ht : 0 < t := by dsimp [t]; positivity
  have z : t ≡ 0 [MOD 49] := Nat.modEq_zero_iff_dvd.mpr
    ⟨7^s,by dsimp [t]; rw [pow_add]; ring⟩
  have z1 : t+1 ≡ 1 [MOD 49] := by simpa only [zero_add] using z.add_right 1
  have aT : a t ≡ 22 [MOD 49] := at_powers repr a1 (s+1)
  have factor : 9*t+3 ≡ 3 [MOD 49] := by simpa only [mul_zero,zero_add] using (z.mul_left 9).add_right 3
  have first : a (t+1) ≡ 17 [MOD 49] := calc
    _ = a (t+1)*1 := by simp
    _ ≡ a (t+1)*(t+1) [MOD 49] := z1.symm.mul_left _
    _ = a t*(9*t+3) := adjacent repr ht
    _ ≡ 22*3 [MOD 49] := aT.mul factor
    _ ≡ 17 [MOD 49] := by decide
  have p : 22^t ≡ 1 [MOD 49] := by
    dsimp [t]; rw [pow_succ' 7 (s+1)]; exact pow_mod _
  have c : 22^(t+1) ≡ 22 [MOD 49] := by simpa only [pow_succ,one_mul] using p.mul_right 22
  exact ⟨first, (lift_seven repr (n:=t+1) (by omega)).trans ((c.mul first).trans (by decide))⟩

end TripleFactorial

namespace TripleFactorial

theorem power_linear (n : ℕ) : 22^n ≡ 1+21*n [MOD 49] := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [pow_succ]
    apply (ih.mul_right 22).trans
    have eq : (1+21*n)*22 = 49*(9*n)+(1+21*(n+1)) := by ring
    rw [eq]
    simp [Nat.ModEq]

theorem lift_criterion {a : ℕ → ℕ} (repr : ∀ n, 0 < n →
    a n * n.factorial = 3^(n-1)*prog n) (n : ℕ) (hn : 0 < n) :
    a (7*n) ≡ a n [MOD 49] ↔ 7 ∣ n ∨ 7 ∣ a n := by
  have lift := (lift_seven repr hn).trans ((power_linear n).mul_right (a n))
  have eq : (1+21*n)*a n = a n + 7*(3*(n*a n)) := by ring
  rw [eq] at lift
  have bridge : a (7*n) ≡ a n [MOD 49] ↔ a n ≡ a n+7*(3*(n*a n)) [MOD 49] :=
    ⟨fun h => h.symm.trans lift,fun h => lift.trans h.symm⟩
  rw [bridge,Nat.modEq_iff_dvd' (Nat.le_add_right _ _),Nat.add_sub_cancel_left,
    show (49 : ℕ) = 7*7 from rfl, Nat.mul_dvd_mul_iff_left (by decide : 0 < 7)]
  simp only [Nat.Prime.dvd_mul (by decide : Nat.Prime 7), show ¬(7:ℕ) ∣ 3 by decide,false_or]
end TripleFactorial

namespace TripleFactorial
open OMA.S_oeis_a034171 Finset

theorem representation (n : ℕ) (hn : 0 < n) : a n * n.factorial = 3^(n-1)*prog n := by
  unfold a entry prog
  rw [Nat.sub_add_cancel hn]
  exact Nat.div_mul_cancel (factorial_divides n hn)

theorem a_one : a 1 = 1 := by decide

theorem original_lift (n : ℕ) (hn : 0 < n) : a (7*n) ≡ 22^n * a n [MOD 49] :=
  lift_seven representation hn

theorem family (s : ℕ) :
    ¬ excluded 7 (7^(s+2)+1) ∧
    a (7^(s+2)+1) % 49 = 17 ∧ a (7*(7^(s+2)+1)) % 49 = 31 := by
  obtain ⟨first,second⟩ := infinite_pattern representation a_one s
  refine ⟨?_, first, second⟩
  rintro ⟨m,k,hm,hk,hk',h⟩
  have p : 0 < (7:ℕ)^s := by positivity
  rw [pow_add] at h
  omega
theorem full_criterion (n : ℕ) (hn : 0 < n) :
    a (7*n) ≡ a n [MOD 49] ↔ 7 ∣ n ∨ 7 ∣ a n := lift_criterion representation n hn

theorem unbounded_failures (bound : ℕ) :
    ∃ n, bound < n ∧ ¬ excluded 7 n ∧ a n % 49 = 17 ∧ a (7*n) % 49 = 31 := by
  refine ⟨7^(bound+2)+1,?_, family bound⟩
  have h : ∀ k : ℕ, k < 7^(k+2) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+2 = (k+2)+1 by omega,pow_succ]
      omega
  exact Nat.lt_succ_of_lt (h bound)

end TripleFactorial

namespace BalaLucas
open PowerSeries

/-- Over the prime field, Frobenius replaces the variable by its p-th power. -/
theorem expand_eq_power {p : ℕ} (prime : p.Prime) (B : PowerSeries (ZMod p)) :
    expand p prime.ne_zero B = B^p := by
  let _ : Fact p.Prime := ⟨prime⟩
  have h := MvPowerSeries.map_frobenius_expand p prime.ne_zero (f := B)
  simpa [PowerSeries.expand] using h

/-- A cubic equation yields a one-digit functional equation. -/
theorem cubic_expand {p : ℕ} (prime : p.Prime) (res : p ≡ 1 [MOD 3])
    (B : PowerSeries (ZMod p)) (cubic : (1-9*X)*B^3 = 1) :
    B = (1-9*X)^((p-1)/3) * expand p prime.ne_zero B := by
  have r : p%3 = 1 := res
  have e : p = 3*((p-1)/3)+1 := by omega
  rw [expand_eq_power prime B]
  have power := congrArg (fun t : ℕ => B^t) e
  change B^p = B^(3*((p-1)/3)+1) at power
  rw [power, pow_succ, pow_mul, ← mul_assoc, ← mul_pow, cubic, one_pow, one_mul]

/-- The coefficients of the binomial factor, including those beyond its degree. -/
theorem coeff_binomial {R : Type*} [CommRing R] (c : R) (d j : ℕ) :
    coeff j ((1+C c*X)^d) = (d.choose j : R)*c^j := by
  have bin : coeff j ((1+X)^d : PowerSeries R) = (d.choose j : R) := by
    simpa only [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X] using
      (Polynomial.coeff_coe ((1+Polynomial.X)^d : Polynomial R) j).trans
        (Polynomial.coeff_one_add_X_pow R d j)
  rw [← rescale_X, ← map_one (rescale c), ← map_add, ← map_pow, coeff_rescale, bin, mul_comm]

/-- A factor of degree less than p selects a single summand from the convolution. -/
theorem coeff_mul_expand {R : Type*} [CommRing R] {p : ℕ} (hp : p ≠ 0)
    (A B : PowerSeries R) (support : ∀ i : ℕ, p ≤ i → coeff i A = 0)
    (k r : ℕ) (hr : r<p) :
    coeff (p*k+r) (A*expand p hp B) = coeff r A * coeff k B := by
  rw [coeff_mul, Finset.sum_eq_single_of_mem (r,p*k) (by simp [add_comm])]
  · rw [coeff_expand_mul]
  · rintro ⟨a,b⟩ hab ne
    have sum : a+b = p*k+r := by simpa using hab
    by_cases large : p ≤ a
    · simp [support a large]
    by_cases dv : p∣b
    · have rem := congrArg (fun x : ℕ => x%p) sum
      have bm := Nat.mod_eq_zero_of_dvd dv
      simp [Nat.add_mod, bm, Nat.mod_eq_of_lt (show a<p by omega), Nat.mod_eq_of_lt hr] at rem
      exact (ne (Prod.ext rem (by dsimp; omega))).elim
    · simp [coeff_expand_of_not_dvd p hp B dv]

/-- Each base-p digit contributes a binomial coefficient; choose is zero above the cutoff. -/
theorem digit {p : ℕ} (prime : p.Prime) (res : p ≡ 1 [MOD 3])
    (B : PowerSeries (ZMod p)) (cubic : (1-9*X)*B^3 = 1)
    (k r : ℕ) (hr : r<p) :
    coeff (p*k+r) B = ((((p-1)/3).choose r : ZMod p)*(-9)^r)*coeff k B := by
  let d := (p-1)/3
  let A := ((1-9*X)^d : PowerSeries (ZMod p))
  have form : ∀ j, coeff j A = (d.choose j : ZMod p)*(-9)^j := by
    intro j
    have h := coeff_binomial (-9 : ZMod p) d j
    have nine : C (9 : ZMod p) = (9 : PowerSeries (ZMod p)) := map_natCast _ 9
    simpa [A,sub_eq_add_neg,nine] using h
  have support (i : ℕ) (le : p ≤ i) : coeff i A = 0 := by
    have pos := prime.pos
    have hi : d < i := by dsimp [d]; omega
    rw [form, Nat.choose_eq_zero_of_lt hi]
    simp
  calc
    coeff (p*k+r) B = coeff (p*k+r) (A*expand p prime.ne_zero B) :=
      congrArg (coeff (p*k+r)) (cubic_expand prime res B cubic)
    _ = coeff r A * coeff k B := coeff_mul_expand prime.ne_zero A B support k r hr
    _ = _ := by rw [form]

end BalaLucas

namespace BalaLucas
open PowerSeries

theorem digit_above {p : ℕ} (prime : p.Prime) (res : p ≡ 1 [MOD 3])
    (B : PowerSeries (ZMod p)) (cubic : (1 - 9*X)*B^3 = 1)
    (k r : ℕ) (above : (p-1)/3 < r) (hr : r < p) :
    coeff (p*k+r) B = 0 := by
  simp [digit prime res B cubic k r hr, Nat.choose_eq_zero_of_lt above]

/-- The digit-product identity also permits empty lists and leading zeroes. -/
theorem ofDigits_product {p : ℕ} (prime : p.Prime) (res : p ≡ 1 [MOD 3])
    (B : PowerSeries (ZMod p)) (cubic : (1 - 9*X)*B^3 = 1) (first : coeff 0 B = 1)
    (ds : List ℕ) (valid : ∀ r ∈ ds, r < p) :
    coeff (Nat.ofDigits p ds) B =
      (ds.map fun r => (((p-1)/3).choose r : ZMod p)*(-9)^r).prod := by
  induction ds with
  | nil => simpa using first
  | cons r ds ih =>
    rw [Nat.ofDigits_cons, Nat.add_comm, digit prime res B cubic _ r (valid r (by simp))]
    simp [ih (fun a ha => valid a (by simp [ha]))]

/-- A coefficient is the product of the binomial factors of its usual base-p digits. -/
theorem digit_product {p : ℕ} (prime : p.Prime) (res : p ≡ 1 [MOD 3])
    (B : PowerSeries (ZMod p)) (cubic : (1 - 9*X)*B^3 = 1)
    (first : coeff 0 B = 1) (n : ℕ) :
    coeff n B =
      ((p.digits n).map fun r => (((p-1)/3).choose r : ZMod p)*(-9)^r).prod := by
  simpa only [Nat.ofDigits_digits] using ofDigits_product prime res B cubic first (p.digits n)
    (fun _ h => Nat.digits_lt_base prime.one_lt h)

end BalaLucas

namespace TripleFactorial
open Finset PowerSeries

/-- Normalization with constant term one used in the generating function. -/
def b : ℕ → ℕ
  | 0 => 1
  | n+1 => 3*((3^n * ∏ i ∈ range (n+1), (3*i+1)) / (n+1).factorial)

theorem factorial_mul_b (n : ℕ) :
    n.factorial*b n = 3^n * ∏ i ∈ range n, (3*i+1) := by
  cases n with
  | zero => simp [b]
  | succ n =>
    have dv := factorial_divides (n+1) (by omega)
    simp only [Nat.add_sub_cancel] at dv
    rw [b, mul_left_comm, Nat.mul_div_cancel' dv, pow_succ]
    ring

theorem recurrence (n : ℕ) : (n+1)*b (n+1) = (9*n+3)*b n := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos n)
  calc
    n.factorial*((n+1)*b (n+1)) = (n+1).factorial*b (n+1) := by rw [Nat.factorial_succ]; ring
    _ = 3^(n+1) * ∏ i ∈ range (n+1), (3*i+1) := factorial_mul_b _
    _ = (9*n+3)*(n.factorial*b n) := by rw [factorial_mul_b, pow_succ,prod_range_succ]; ring
    _ = _ := by ring

noncomputable def B : PowerSeries ℤ := mk fun n => (b n : ℤ)

@[simp] theorem coeff_B (n : ℕ) : coeff n B = (b n : ℤ) := coeff_mk _ _

private theorem differential : (1-9*X)*derivative ℤ B = 3*B := by
  have nine : C (9 : ℤ) = (9 : PowerSeries ℤ) := by norm_num
  have three : C (3 : ℤ) = (3 : PowerSeries ℤ) := by norm_num
  rw [sub_mul, one_mul, mul_assoc, ← nine, ← three]
  ext n
  rw [map_sub, coeff_C_mul, coeff_C_mul]
  cases n with
  | zero =>
    simp [coeff_derivative,b]
  | succ n =>
    rw [coeff_succ_X_mul,coeff_derivative,coeff_derivative,coeff_B,coeff_B]
    have hr : ((n+1:ℕ)+1:ℤ)*(b (n+1+1):ℤ) = (9*(n+1:ℕ)+3:ℤ)*(b (n+1):ℤ) := by
      exact_mod_cast recurrence (n+1)
    push_cast at *
    linarith

/-- Integral cubic identity for the registered integer sequence. -/
theorem cubic : (1-9*X)*B^3 = 1 := by
  have hd : derivative ℤ ((1-9*X)*B^3) = 0 := by
    have dn : derivative ℤ (9 : PowerSeries ℤ) = 0 := by
      rw [← show C (9 : ℤ) = (9 : PowerSeries ℤ) by norm_num, PowerSeries.derivative_C]
    rw [Derivation.leibniz, PowerSeries.derivative_pow]
    simp only [Nat.cast_ofNat, Nat.reduceSub, map_sub, Derivation.map_one_eq_zero,
      Derivation.leibniz, PowerSeries.derivative_X, dn, smul_eq_mul, mul_one, mul_zero, add_zero, zero_sub]
    linear_combination (3 * B^2) * differential
  ext n
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff_apply, B, constantCoeff_mk, b]
  | succ n =>
    have h := congrArg (coeff n) hd
    rw [coeff_derivative, map_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (by positivity) |>.trans (by simp [coeff_one])

end TripleFactorial

namespace TripleFactorial
open PowerSeries

/-- A base-p digit relation for the normalized triple-factorial sequence. -/
theorem digit_law {p : ℕ} (hp : Nat.Prime p) (res : p ≡ 1 [MOD 3])
    (k r : ℕ) (hr : r < p) :
    (b (p*k+r) : ZMod p) = (((p-1)/3).choose r : ZMod p)*(-9)^r*(b k : ZMod p) := by
  let φ := Int.castRingHom (ZMod p)
  let T := PowerSeries.map φ B
  have hc : (1-9*X)*T^3 = 1 := by
    have h := congrArg (PowerSeries.map φ) cubic
    have nine : PowerSeries.map φ (9 : PowerSeries ℤ) = 9 := map_ofNat _ _
    simpa [T,nine] using h
  have ht (i : ℕ) : coeff i T = (b i : ZMod p) := by simp [T,φ,coeff_map]
  simpa only [ht] using BalaLucas.digit hp res T hc k r hr

end TripleFactorial

namespace TripleFactorial
open OMA.S_oeis_a034171

/-- The normalization agrees with three times the registered sequence at positive indices. -/
theorem b_pos {n : ℕ} (hn : 0 < n) : b n = 3*a n := by
  cases n with
  | zero => omega
  | succ n => rfl

/-- The registered supercongruence always holds to first order, without exceptional indices. -/
theorem first_order {p n : ℕ} (prime : p.Prime) (res : p ≡ 1 [MOD 3]) (hn : 0 < n) :
    a (p*n) ≡ a n [MOD p] := by
  let _ : Fact p.Prime := ⟨prime⟩
  have d := digit_law prime res n 0 prime.pos
  simp only [Nat.add_zero,Nat.choose_zero_right,Nat.cast_one,pow_zero,one_mul] at d
  rw [b_pos (Nat.mul_pos prime.pos hn), b_pos hn,Nat.cast_mul,Nat.cast_mul] at d
  have np : p ≠ 3 := by intro h; subst p; exact (by decide : ¬ (3 ≡ 1 [MOD 3])) res
  have nz : (3 : ZMod p) ≠ 0 := by
    have nd : ¬ p ∣ 3 := fun dv => np ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp dv |>.resolve_left prime.ne_one)
    exact_mod_cast (show ((3 : ℕ) : ZMod p) ≠ 0 from fun h => nd ((ZMod.natCast_eq_zero_iff _ _).mp h))
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (mul_left_cancel₀ nz d)

end TripleFactorial

namespace TripleFactorial
open PowerSeries

/-- Complete product formula for the base-p digits of the index. -/
theorem product_law {p : ℕ} (hp : Nat.Prime p) (res : p ≡ 1 [MOD 3]) (n : ℕ) :
    (b n : ZMod p) =
      ((p.digits n).map fun r => (((p-1)/3).choose r : ZMod p)*(-9)^r).prod := by
  let φ := Int.castRingHom (ZMod p)
  let T := PowerSeries.map φ B
  have hc : (1-9*X)*T^3 = 1 := by
    have nine : PowerSeries.map φ (9 : PowerSeries ℤ) = 9 := map_ofNat _ _
    simpa [T,nine] using congrArg (PowerSeries.map φ) cubic
  have ht (i : ℕ) : coeff i T = (b i : ZMod p) := by simp [T,φ,coeff_map]
  simpa only [ht] using BalaLucas.digit_product hp res T hc (by rw [ht]; simp [b]) n

/-- A term is nonzero modulo p exactly when each digit falls below the binomial cutoff. -/
theorem nonzero_iff_digits {p n : ℕ} (prime : Nat.Prime p) (res : p ≡ 1 [MOD 3]) :
    (b n : ZMod p) ≠ 0 ↔ ∀ r ∈ p.digits n, r ≤ (p-1)/3 := by
  let _ : Fact p.Prime := ⟨prime⟩
  let d := (p-1)/3
  have dp : d < p := by dsimp [d]; have := prime.pos; omega
  have np : p ≠ 3 := by intro h; subst p; exact (by decide : ¬ (3 ≡ 1 [MOD 3])) res
  have z3 : ((3 : ℕ) : ZMod p) ≠ 0 := by
    intro h
    exact np (((Nat.dvd_prime (by decide : Nat.Prime 3)).mp ((ZMod.natCast_eq_zero_iff _ _).mp h)).resolve_left prime.ne_one)
  have zn : (-9 : ZMod p) ≠ 0 := by
    have t := mul_ne_zero z3 z3
    norm_num at t ⊢
    exact t
  have factor (r : ℕ) : (d.choose r : ZMod p)*(-9)^r ≠ 0 ↔ r ≤ d := by
    rw [mul_ne_zero_iff]
    constructor
    · rintro ⟨hr,_⟩
      by_contra! bad
      simp [Nat.choose_eq_zero_of_lt bad] at hr
    · intro hr
      refine ⟨?_,pow_ne_zero _ zn⟩
      intro h
      have div := (ZMod.natCast_eq_zero_iff _ _).mp h
      have fd : p ∣ d.factorial := by
        rw [← Nat.choose_mul_factorial_mul_factorial hr]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left div _) _
      exact dp.not_ge (prime.dvd_factorial.mp fd)
  rw [product_law prime res]
  generalize p.digits n = ds
  induction ds with
  | nil => simp
  | cons r ds ih => simpa only [List.map_cons, List.prod_cons, mul_ne_zero_iff, List.forall_mem_cons] using
                      (and_congr (factor r) ih)

open OMA.S_oeis_a034171 in
/-- The support criterion in the indexing of the registered OEIS article. -/
theorem original_nonzero_iff {p n : ℕ} (prime : Nat.Prime p) (res : p ≡ 1 [MOD 3]) (hn : 0 < n) :
    ¬ p ∣ a n ↔ ∀ r ∈ p.digits n, r ≤ (p-1)/3 := by
  rw [← nonzero_iff_digits prime res, b_pos hn, Nat.cast_mul]
  have np : p ≠ 3 := by intro h; subst p; exact (by decide : ¬ (3 ≡ 1 [MOD 3])) res
  have nc : ((3 : ℕ) : ZMod p) ≠ 0 := fun h => np
    (((Nat.dvd_prime (by decide : Nat.Prime 3)).mp ((ZMod.natCast_eq_zero_iff _ _).mp h)).resolve_left prime.ne_one)
  let _ : Fact p.Prime := ⟨prime⟩
  rw [mul_ne_zero_iff, and_iff_right nc]
  exact (not_congr (ZMod.natCast_eq_zero_iff (a n) p)).symm

end TripleFactorial

namespace BalaBlocks
open Finset

/-- Split a product into blocks and extract their distinguished factors. -/
theorem split (p n e : ℕ) (he : e < p) (f g : ℕ → ℕ)
    (factor : ∀ j, f (p*j+e) = p*g j) :
    (∏ i ∈ range (p*n), f i) =
      p^n * (∏ j ∈ range n, g j) *
        ∏ j ∈ range n, ∏ i ∈ (range p).erase e, f (p*j+i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have block : (∏ i ∈ range p, f (p*n+i)) =
        p*g n * ∏ i ∈ (range p).erase e, f (p*n+i) := by
      rw [← mul_prod_erase (range p) (fun i => f (p*n+i)) (mem_range.mpr he), factor]
    rw [Nat.mul_succ, prod_range_add, ih, block, pow_succ, prod_range_succ,
      prod_range_succ]
    ring

theorem progression (p n : ℕ) (hp : 0 < p) (h : p%3 = 1) :
    (∏ i ∈ range (p*n), (3*i+1)) =
      p^n * (∏ j ∈ range n, (3*j+1)) *
        ∏ j ∈ range n, ∏ i ∈ (range p).erase ((p-1)/3), (3*(p*j+i)+1) := by
  apply split p n ((p-1)/3) (by omega) (fun i => 3*i+1) (fun j => 3*j+1)
  intro j
  have : 3*((p-1)/3)+1 = p := by omega
  nlinarith

theorem factorial (p n : ℕ) (hp : 0 < p) :
    (p*n).factorial =
      p^n * n.factorial * ∏ j ∈ range n, ∏ i ∈ (range p).erase (p-1), (p*j+i+1) := by
  rw [Nat.factorial_eq_prod_range_add_one, Nat.factorial_eq_prod_range_add_one]
  apply split p n (p-1) (by omega) (fun i => i+1) (fun j => j+1)
  intro j
  have : p-1+1=p := by omega
  nlinarith

end BalaBlocks

namespace TripleFactorial
open Finset

private theorem pair_product {ι : Type*} [DecidableEq ι] (m : ℕ)
    (f g : ι → ℕ) (swap : ι → ι) (s : Finset ι)
    (mates : ∀ i∈s, swap i∈s ∧ swap (swap i)=i ∧ swap i≠i)
    (pairs : ∀ i∈s, f i*f (swap i) ≡ g i*g (swap i) [MOD m]) :
    (∏ i∈s,f i) ≡ ∏ i∈s,g i [MOD m] := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl|⟨i,hi⟩
    · rfl
    let j := swap i
    obtain ⟨hj,hji,ne⟩ := mates i hi
    have hj' : j∈s.erase i := mem_erase.mpr ⟨ne,hj⟩
    let t := (s.erase i).erase j
    have sub : t ⊂ s := lt_of_le_of_lt (erase_subset _ _) (erase_ssubset hi)
    have tmem (a) : a∈t ↔ a≠j ∧ a≠i ∧ a∈s := by simp [t]
    have mt : ∀ a∈t, swap a∈t ∧ swap (swap a)=a ∧ swap a≠a := by
      intro a ha
      obtain ⟨an,an',ins⟩ := (tmem a).mp ha
      obtain ⟨b,inv,neq⟩ := mates a ins
      refine ⟨(tmem _).mpr ⟨?_,?_,b⟩,inv,neq⟩
      · intro eq
        exact an' (inv.symm.trans ((congrArg swap eq).trans hji))
      · intro eq
        exact an (inv.symm.trans (congrArg swap eq))
    have small := ih t sub mt (fun a ha => pairs a ((tmem a).mp ha).2.2)
    have eq (h : ι → ℕ) : (∏ a∈s,h a) = (h i*h j) * ∏ a∈t,h a := by
      rw [← mul_prod_erase s h hi,← mul_prod_erase (s.erase i) h hj',mul_assoc]
    rw [eq f,eq g]
    exact (pairs i hi).mul small

/-- Translating all noncentral terms of an affine progression by a multiple
of an odd modulus leaves their product unchanged modulo its square. -/
theorem unit_translate (p r a b c : ℕ) (hp : 0 < p) (two : Nat.Coprime p 2)
    (hr : r < p) (center : p ∣ a*r+b) :
    (∏ i ∈ (range p).erase r, (a*i+b+p*c)) ≡
      ∏ i ∈ (range p).erase r, (a*i+b) [MOD p^2] := by
  let s := (range p).erase r
  let flip (i : ℕ) := (p+2*r-i)%p
  have bound (i) : flip i < p := Nat.mod_lt _ hp
  have reflect (i) (hi : i < p) : i+flip i ≡ 2*r [MOD p] := calc
    _ ≡ i+(p+2*r-i) [MOD p] := (Nat.mod_modEq _ _).add_left _
    _ = p+2*r := by omega
    _ ≡ 2*r [MOD p] := by simp [Nat.ModEq]
  have back (i) (hi : i < p) : flip (flip i)=i := by
    have h := (reflect (flip i) (bound _)).trans (reflect i hi).symm
    rw [add_comm i (flip i)] at h
    exact (Nat.ModEq.add_left_cancel' _ h).eq_of_lt_of_lt (bound _) hi
  have fixes : flip r = r := by
    have h := reflect r hr
    rw [two_mul] at h
    exact (Nat.ModEq.add_left_cancel' _ h).eq_of_lt_of_lt (bound _) hr
  apply pair_product (swap:=flip)
  · intro i hi
    obtain ⟨nr,hrange⟩ := mem_erase.mp hi
    have lt := mem_range.mp hrange
    refine ⟨mem_erase.mpr ⟨?_,mem_range.mpr (bound i)⟩,back i lt,?_⟩
    · intro eq
      exact nr ((back i lt).symm.trans ((congrArg flip eq).trans fixes))
    · intro eq
      have h := reflect i lt
      rw [eq,←two_mul] at h
      exact nr ((Nat.ModEq.cancel_left_of_coprime two h).eq_of_lt_of_lt lt hr)
  · intro i hi
    have lt := mem_range.mp (mem_erase.mp hi).2
    have sums : p ∣ (a*i+b)+(a*flip i+b) := by
      apply Nat.modEq_zero_iff_dvd.mp
      calc
        _ = a*(i+flip i)+2*b := by ring
        _ ≡ a*(2*r)+2*b [MOD p] := ((reflect i lt).mul_left a).add_right _
        _ = 2*(a*r+b) := by ring
        _ ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right center _)
    obtain ⟨v,hv⟩ := sums
    have expand : (a*i+b+p*c)*(a*flip i+b+p*c) =
        (a*i+b)*(a*flip i+b) + p^2*(c*v+c^2) := calc
      _ = (a*i+b)*(a*flip i+b) + (p*c)*((a*i+b)+(a*flip i+b)) + (p*c)^2 := by ring
      _ = _ := by rw [hv]; ring
    rw [expand]; simp [Nat.ModEq]
end TripleFactorial

namespace TripleFactorial
open Finset

private theorem product_const {p : ℕ} (U : ℕ → ℕ) (eq : ∀ j, U j ≡ U 0 [MOD p]) (n : ℕ) :
    (∏ j∈range n, U j) ≡ (U 0)^n [MOD p] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [prod_range_succ,pow_succ]; exact ih.mul (eq n)

/-- Uniform lift modulo p². The exact multiplier is the original coefficient
at p, determined by the single block of length p. -/
theorem prime_lift_general {a : ℕ → ℕ} (repr : ∀ n, 0 < n →
    a n*n.factorial = 3^(n-1)*prog n) (a1 : a 1=1) (p : ℕ)
    (hp : p.Prime) (res : p%3=1) (n : ℕ) (hn : 0 < n) :
    a (p*n) ≡ (a p)^n*a n [MOD p^2] := by
  let U (j : ℕ) := ∏ i∈(range p).erase ((p-1)/3), (3*(p*j+i)+1)
  let D (j : ℕ) := ∏ i∈(range p).erase (p-1), (p*j+i+1)
  have pos := hp.pos
  have two : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr <| by
    intro dvd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp dvd with h|h
    · exact hp.ne_one h
    · omega
  have Ueq (j) : U j ≡ U 0 [MOD p^2] := by
    have center : 3*((p-1)/3)+1=p := by omega
    have shift (i : ℕ) : 3*(p*j+i)+1=3*i+1+p*(3*j) := by ring
    simp only [U,Nat.mul_zero,Nat.zero_add,shift]
    exact unit_translate p ((p-1)/3) 3 1 (3*j) pos two (by omega) (by rw [center])
  have Deq (j) : D j ≡ D 0 [MOD p^2] := by
    have center : 1*(p-1)+1=p := by omega
    have h := unit_translate p (p-1) 1 1 j pos two (by omega) (by rw [center])
    simpa only [D,Nat.mul_zero,Nat.zero_add,one_mul,add_assoc,add_left_comm,add_comm] using h
  have cop : Nat.Coprime p (D 0) := by
    apply Nat.Coprime.prod_right
    intro i hi
    obtain ⟨ne,ins⟩ := mem_erase.mp hi
    have lt := mem_range.mp ins
    simp only [Nat.mul_zero,Nat.zero_add]
    apply hp.coprime_iff_not_dvd.mpr
    intro dvd
    have := Nat.le_of_dvd (Nat.succ_pos i) dvd
    omega
  have cert (k) (hk : 0 < k) : a (p*k)*(D 0)^k ≡ a k*(3^(p-1)*U 0)^k [MOD p^2] := by
    have expn : p*k-1 = (k-1)+(p-1)*k := by
      rw [Nat.sub_mul,one_mul]
      have := Nat.le_mul_of_pos_left k pos
      omega
    have power : 3^(p*k-1)=3^(k-1)*(3^(p-1))^k := by rw [← pow_mul,← pow_add,expn]
    have raw : (a (p*k)*(∏ j∈range k,D j))*(p^k*k.factorial) =
        (a k*(3^(p-1))^k*(∏ j∈range k,U j))*(p^k*k.factorial) := calc
      _ = a (p*k)*(p*k).factorial := by rw [BalaBlocks.factorial p k pos]; dsimp [D]; ring
      _ = 3^(p*k-1)*prog (p*k) := repr _ (Nat.mul_pos pos hk)
      _ = (a k*k.factorial)*((3^(p-1))^k*p^k*(∏ j∈range k,U j)) := by
        rw [repr k hk,power]; unfold prog; rw [BalaBlocks.progression p k pos res]; dsimp [U]; ring
      _ = _ := by ring
    have eq := Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (pow_pos pos _) (Nat.factorial_pos k)) raw
    calc
      _ ≡ a (p*k)*(∏ j∈range k,D j) [MOD p^2] := (product_const D Deq k).symm.mul_left _
      _ = a k*(3^(p-1))^k*(∏ j∈range k,U j) := eq
      _ ≡ a k*(3^(p-1))^k*(U 0)^k [MOD p^2] := (product_const U Ueq k).mul_left _
      _ = _ := by rw [mul_pow]; ring
  have one : a p*D 0 ≡ 3^(p-1)*U 0 [MOD p^2] := by
    simpa only [mul_one,pow_one,a1,one_mul] using cert 1 (by decide)
  apply Nat.ModEq.cancel_right_of_coprime ((cop.pow_left 2).pow_right n)
  calc
    _ ≡ a n*(3^(p-1)*U 0)^n [MOD p^2] := cert n hn
    _ ≡ a n*(a p*D 0)^n [MOD p^2] := (one.symm.pow n).mul_left _
    _ = _ := by rw [mul_pow]; ring
end TripleFactorial

namespace TripleFactorial

private theorem first_order_power (p q n : ℕ) :
    (1+p*q)^n ≡ 1+p*(q*n) [MOD p^2] := by
  induction n with
  | zero => simp [Nat.ModEq]
  | succ n ih =>
    rw [pow_succ]
    apply (ih.mul_right _).trans
    rw [show (1+p*(q*n))*(1+p*q) = p^2*(q^2*n)+(1+p*(q*(n+1))) by ring]
    simp [Nat.ModEq]

private theorem translation_criterion {p : ℕ} (hp : 0 < p) (x y : ℕ) :
    x+p*y ≡ x [MOD p^2] ↔ p ∣ y := by
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    pow_two,Nat.mul_dvd_mul_iff_left hp]

/-- Sharp equality criterion at the square of an individual prime. -/
theorem prime_criterion_general {a : ℕ → ℕ} (repr : ∀ n, 0 < n →
    a n*n.factorial = 3^(n-1)*prog n) (a1 : a 1=1) (p : ℕ)
    (hp : p.Prime) (res : p%3=1) (base : a p ≡ 1 [MOD p]) (n : ℕ) (hn : 0 < n) :
    a (p*n) ≡ a n [MOD p^2] ↔ a p ≡ 1 [MOD p^2] ∨ p ∣ n ∨ p ∣ a n := by
  have ap : 0 < a p := by
    by_contra! h
    have z : a p=0 := by omega
    have no : (0 : ℕ) = 1 := by
      simpa only [z,Nat.ModEq,Nat.zero_mod,Nat.mod_eq_of_lt hp.one_lt] using base
    omega
  obtain ⟨q,hq⟩ := base.symm.dvd'
  have aq : a p=1+p*q := by omega
  have h := prime_lift_general repr a1 p hp res n hn
  rw [aq] at h
  have all := h.trans ((first_order_power p q n).mul_right (a n))
  rw [show (1+p*(q*n))*a n = a n+p*(q*n*a n) by ring] at all
  have iff : a (p*n) ≡ a n [MOD p^2] ↔ a n+p*(q*n*a n) ≡ a n [MOD p^2] :=
    ⟨fun h => all.symm.trans h,fun h => all.trans h⟩
  rw [iff,aq,translation_criterion hp.pos,translation_criterion hp.pos]
  simp only [hp.dvd_mul,or_assoc]

end TripleFactorial

namespace TripleFactorial
open OMA.S_oeis_a034171

theorem all_prime_lift {p n : ℕ} (prime : p.Prime) (res : p ≡ 1 [MOD 3]) (hn : 0 < n) :
    a (p*n) ≡ (a p)^n*a n [MOD p^2] :=
  prime_lift_general representation a_one p prime res n hn

theorem all_prime_criterion {p n : ℕ} (prime : p.Prime) (res : p ≡ 1 [MOD 3]) (hn : 0 < n) :
    a (p*n) ≡ a n [MOD p^2] ↔ a p ≡ 1 [MOD p^2] ∨ p ∣ n ∨ p ∣ a n := by
  have one : a p ≡ 1 [MOD p] := by
    simpa only [mul_one,a_one] using first_order prime res (n:=1) (by decide)
  exact prime_criterion_general representation a_one p prime res one n hn
end TripleFactorial

namespace TripleFactorial
open OMA.S_oeis_a034171

/-- Exact failure criterion for the original congruence at every positive index. -/
theorem failure_iff_digits {p n : ℕ} (prime : p.Prime) (res : p ≡ 1 [MOD 3]) (hn : 0 < n) :
    (¬ a (p*n) ≡ a n [MOD p^2]) ↔
      (¬ a p ≡ 1 [MOD p^2]) ∧ (¬ p ∣ n) ∧ ∀ d ∈ p.digits n, d ≤ (p-1)/3 := by
  rw [all_prime_criterion prime res hn,← original_nonzero_iff prime res hn]
  tauto
end TripleFactorial

#print axioms TripleFactorial.factorial_divides
#print axioms TripleFactorial.cubic
#print axioms TripleFactorial.digit_law
#print axioms TripleFactorial.product_law
#print axioms TripleFactorial.first_order
#print axioms TripleFactorial.original_nonzero_iff
#print axioms TripleFactorial.original_lift
#print axioms TripleFactorial.unbounded_failures
#print axioms TripleFactorial.unit_translate
#print axioms TripleFactorial.all_prime_lift
#print axioms TripleFactorial.all_prime_criterion
#print axioms TripleFactorial.failure_iff_digits
