import OMAStatements.S_oeis_a034171
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# An exact prime-square law for OEIS A034171

For every prime p congruent to 1 modulo 3 and every positive n, the
multiplier from a(n) to a(pn) modulo p² equals the nth power of
(−3)^((p−1)/2). The proposed congruence, with its stated exclusions,
holds for every admissible index exactly at base-three Wieferich primes.
At any other eligible prime its first nonexcluded failure occurs at p²+1.
The digit criterion, exact counts and an explicit positive instance at
p = 1006003 are included. The earlier counterexample p = 7, n = 50 was
reported by @Solfanbtc. The registered statement was formalized by @Nealanio.
-/

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

/-!
# Counting the failures of the A034171 prime-square congruence

Write d = (p−1)/3. When the multiplier a(p) is nontrivial modulo p², the
units digit has d choices and every higher digit has d+1 choices. The original
exclusion removes exactly the indices with at most two base-p digits from this
set. The calculation includes initial windows and the case of trivial multiplier.
-/


namespace TripleFactorial
open Finset

/-- Count a complete set of quotient–remainder pairs with separately prescribed coordinates. -/
private theorem count_rectangle {p q : ℕ} (hp : 0 < p) (S T : Finset ℕ)
    (hs : ∀ x ∈ S, x < q) (ht : ∀ y ∈ T, y < p) :
    ((range (q*p)).filter (fun n => n / p ∈ S ∧ n % p ∈ T)).card = S.card * T.card := by
  rw [← card_product]
  apply card_nbij' (fun n => (n/p,n%p)) (fun z => z.2 + p*z.1)
  · intro n hn
    exact mem_product.mpr (mem_filter.mp hn).2
  · rintro ⟨x,y⟩ h
    obtain ⟨hx,hy⟩ := mem_product.mp h
    have lo := ht y hy
    have xx : (y+p*x)/p = x := by simp [Nat.add_mul_div_left, hp, Nat.div_eq_of_lt lo]
    have yy : (y+p*x)%p = y := by simp [Nat.mod_eq_of_lt lo]
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_, by simpa [xx,yy] using And.intro hx hy⟩
    change y + p*x < q*p
    exact (Nat.div_lt_iff_lt_mul hp).mp (by rw [xx]; exact hs x hx)
  · intro n _
    exact Nat.mod_add_div n p
  · rintro ⟨x,y⟩ h
    have lo := ht y (mem_product.mp h).2
    exact Prod.ext (by simp [Nat.add_mul_div_left, hp, Nat.div_eq_of_lt lo])
      (by simp [Nat.mod_eq_of_lt lo])

private theorem good_digit_step {p : ℕ} (hp : 1 < p) (d n : ℕ) :
    (∀ r ∈ p.digits n, r ≤ d) ↔
    (∀ r ∈ p.digits (n/p), r ≤ d) ∧ n%p ≤ d := by
  by_cases hn : n = 0
  · simp [hn]
  rw [Nat.digits_eq_cons_digits_div hp hn, List.forall_mem_cons]
  exact and_comm

/-- For `s` freely chosen base-`p` digits, each with maximum `d`, there are `(d+1)^s` choices. -/
theorem bounded_digit_count {p d : ℕ} (hp : 1 < p) (hd : d < p) (s : ℕ) :
    ((range (p^s)).filter (fun n => ∀ r ∈ p.digits n, r ≤ d)).card = (d+1)^s := by
  induction s with
  | zero => simp [Finset.filter_singleton]
  | succ s ih =>
    let S := (range (p^s)).filter (fun n => ∀ r ∈ p.digits n, r ≤ d)
    have hq {n : ℕ} (hn : n < p^s*p) := (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hp)).mpr hn
    rw [pow_succ, pow_succ]
    have sets :
        ((range (p^s*p)).filter (fun n => ∀ r ∈ p.digits n, r ≤ d)) =
          (range (p^s*p)).filter (fun n => n/p ∈ S ∧ n%p ∈ range (d+1)) := by
      apply filter_congr
      intro n hn
      simpa [S,hq (mem_range.mp hn),Nat.lt_succ_iff] using good_digit_step hp d n
    rw [sets, count_rectangle (Nat.zero_lt_of_lt hp)]
    · simp [S,ih]
    · exact fun x hx => mem_range.mp (mem_filter.mp hx).1
    · exact fun y hy => lt_of_le_of_lt (Nat.le_of_lt_succ (mem_range.mp hy)) hd

/-- Count positive admissible digit strings with a nonzero units digit. -/
theorem bounded_unit_count {p d : ℕ} (hp : 1 < p) (hd : d < p) (s : ℕ) :
    ((range (p^(s+1))).filter (fun n => 0 < n ∧ ¬p ∣ n ∧ ∀ r ∈ p.digits n, r ≤ d)).card =
      (d+1)^s*d := by
  let S := (range (p^s)).filter (fun n => ∀ r ∈ p.digits n, r ≤ d)
  have hq {n : ℕ} (hn : n < p^s*p) := (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hp)).mpr hn
  rw [pow_succ]
  have sets : ((range (p^s*p)).filter (fun n => 0 < n ∧ ¬p ∣ n ∧ ∀ r ∈ p.digits n, r ≤ d)) =
      (range (p^s*p)).filter (fun n => n/p ∈ S ∧ n%p ∈ Icc 1 d) := by
    apply filter_congr
    intro n hn
    simp only [S, mem_filter, mem_range, hq (mem_range.mp hn), true_and, mem_Icc,
      good_digit_step hp d n, Nat.dvd_iff_mod_eq_zero]
    by_cases h : n = 0
    · simp [h]
    · have : 0 < n := Nat.pos_of_ne_zero h
      have hr : n % p ≠ 0 ↔ 1 ≤ n % p := by omega
      simp only [this,hr,true_and]
      tauto
  rw [sets, count_rectangle (Nat.zero_lt_of_lt hp)]
  · simp [S,bounded_digit_count hp hd]
  · exact fun x hx => mem_range.mp (mem_filter.mp hx).1
  · exact fun y hy => (mem_Icc.mp hy).2.trans_lt hd

end TripleFactorial

namespace BalaBlocks
open OMA.S_oeis_a034171

/-- Every excluded index is a two-digit index (allowing zero in the leading place). -/
theorem excluded_digits {p n : ℕ} (hp : 0 < p) :
    excluded p n ↔ n < p^2 ∧ 1 ≤ n%p ∧ n%p ≤ (p-1)/3 ∧ n/p ≤ (p-1)/3 := by
  constructor
  · rintro ⟨m,k,hm,hk,hle,rfl⟩
    have km : k < p := by omega
    have mm : m < p := by omega
    have bound : m*p+k < p^2 := by
      calc
        m*p+k < m*p+p := Nat.add_lt_add_left km _
        _ = (m+1)*p := by ring
        _ ≤ p^2 := by rw [pow_two]; exact Nat.mul_le_mul_right p (by omega)
    have modpart : (m*p+k)%p = k := by simp [Nat.add_mod, Nat.mod_eq_of_lt km]
    have divpart : (m*p+k)/p = m := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt km, Nat.zero_add]
    rw [modpart, divpart]
    exact ⟨bound, hk, hle, hm⟩
  · rintro ⟨_,hk,hl,hm⟩
    exact ⟨n/p,n%p,hm,hk,hl,by simpa [Nat.add_comm,Nat.mul_comm] using (Nat.mod_add_div n p).symm⟩

theorem excluded_iff_digits_of_lt_sq {p n : ℕ} (hp : 0 < p) (hn : n < p^2) :
    excluded p n ↔ 1 ≤ n%p ∧ n%p ≤ (p-1)/3 ∧ n/p ≤ (p-1)/3 := by
  rw [excluded_digits hp, and_iff_right hn]

end BalaBlocks

namespace TripleFactorial
open Finset OMA.S_oeis_a034171
open scoped Classical

/-- The number of prime-square failures with at most `s+1` base-p digits. -/
theorem failure_count {p : ℕ} (prime : p.Prime) (res : p ≡ 1 [MOD 3]) (s : ℕ) :
    let d := (p-1)/3
    ((range (p^(s+1))).filter (fun n => 0 < n ∧ ¬ a (p*n) ≡ a n [MOD p^2])).card =
      if a p ≡ 1 [MOD p^2] then 0 else (d+1)^s*d := by
  dsimp only
  by_cases h : a p ≡ 1 [MOD p^2]
  · rw [if_pos h,card_eq_zero,filter_eq_empty_iff]
    rintro n _ ⟨hn,fail⟩
    exact ((failure_iff_digits prime res hn).mp fail).1 h
  · rw [if_neg h,← bounded_unit_count prime.one_lt (d:=(p-1)/3) (by have := prime.pos; omega)]
    congr 1
    refine filter_congr (fun n _ => ?_)
    by_cases hn : 0 < n
    · simp only [hn,true_and,failure_iff_digits prime res hn,h,not_false_eq_true]
    · simp [hn]

/-- The interval with fewer than one base-p digit contains no positive index. -/
theorem failure_count_zero (p : ℕ) :
    ((range (p^0)).filter (fun n => 0 < n ∧ ¬ a (p*n) ≡ a n [MOD p^2])).card = 0 := by
  simp [Finset.filter_singleton]
end TripleFactorial

namespace TripleFactorial
open Finset OMA.S_oeis_a034171
open scoped Classical

/-- Among actual failures, the proposed exceptional set is precisely the initial two-digit range. -/
theorem excluded_iff_lt_sq_of_failure {p n : ℕ} (prime : p.Prime) (res : p ≡ 1 [MOD 3])
    (hn : 0 < n) (bad : ¬ a (p*n) ≡ a n [MOD p^2]) : excluded p n ↔ n < p^2 := by
  rw [BalaBlocks.excluded_digits prime.pos]
  refine ⟨And.left, fun bound => ⟨bound, ?_⟩⟩
  obtain ⟨_,nd,digits⟩ := (failure_iff_digits prime res hn).mp bad
  obtain ⟨hi,lo⟩ := (good_digit_step prime.one_lt ((p-1)/3) n).mp digits
  have pos : 1 ≤ n%p := Nat.pos_of_ne_zero (fun h => nd (Nat.dvd_of_mod_eq_zero h))
  refine ⟨pos,lo,?_⟩
  have lt : n/p < p := (Nat.div_lt_iff_lt_mul prime.pos).mpr (by simpa [pow_two] using bound)
  by_cases z : n/p = 0
  · simp [z]
  · rw [Nat.digits_of_lt p (n/p) z lt] at hi
    exact hi _ (by simp)

/-- Exact count for the quantifiers of Bala's conjecture for a window of at least two digits. -/
theorem unexcluded_failure_count {p : ℕ} (prime : p.Prime) (res : p ≡ 1 [MOD 3]) (s : ℕ) :
    let d := (p-1)/3
    ((range (p^(s+2))).filter (fun n => 0 < n ∧ ¬ excluded p n ∧
      ¬ a (p*n) ≡ a n [MOD p^2])).card =
      if a p ≡ 1 [MOD p^2] then 0 else (d+1)^(s+1)*d - (d+1)*d := by
  dsimp only
  let F := fun (t : ℕ) => (range t).filter (fun n => 0 < n ∧ ¬ a (p*n) ≡ a n [MOD p^2])
  have le : p^2 ≤ p^(s+2) := Nat.pow_le_pow_right prime.pos (by omega)
  have sub : F (p^2) ⊆ F (p^(s+2)) := by
    intro n hn
    obtain ⟨r,h⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp r).trans_le le),h⟩
  have sets : ((range (p^(s+2))).filter (fun n => 0 < n ∧ ¬ excluded p n ∧
      ¬ a (p*n) ≡ a n [MOD p^2])) = F (p^(s+2)) \ F (p^2) := by
    ext n
    simp only [F, mem_filter, mem_range, mem_sdiff]
    by_cases hn : 0 < n <;> simp only [hn, true_and, false_and, and_false, not_false_eq_true, and_true]
    by_cases bad : ¬ a (p*n) ≡ a n [MOD p^2]
    · rw [excluded_iff_lt_sq_of_failure prime res hn bad]
      tauto
    · tauto
  rw [sets,card_sdiff_of_subset sub]
  change _ - _ = _
  have long := failure_count prime res (s+1)
  have short := failure_count prime res 1
  simp only [pow_one] at short
  change (F (p^(s+2))).card = _ at long
  change (F (p^2)).card = _ at short
  rw [long,short]
  split <;> simp_all

/-- Positive windows of length at most two digits have no unexcluded counterexample. -/
theorem unexcluded_failure_count_small {p : ℕ} (prime : p.Prime) (res : p ≡ 1 [MOD 3])
    {M : ℕ} (bound : M ≤ p^2) :
    ((range M).filter (fun n => 0 < n ∧ ¬ excluded p n ∧ ¬ a (p*n) ≡ a n [MOD p^2])).card = 0 := by
  rw [card_eq_zero,filter_eq_empty_iff]
  rintro n h ⟨hn,hex,bad⟩
  exact hex ((excluded_iff_lt_sq_of_failure prime res hn bad).mpr ((mem_range.mp h).trans_le bound))

end TripleFactorial

namespace TripleFactorial
open OMA.S_oeis_a034171

/-- A nontrivial multiplier gives a counterexample by adjoining a units digit to a power of p. -/
theorem power_plus_one_failure {p : ℕ} (prime : p.Prime) (res : p ≡ 1 [MOD 3])
    (nontrivial : ¬ a p ≡ 1 [MOD p^2]) (s : ℕ) :
    let n := p^(s+2)+1
    0 < n ∧ ¬ excluded p n ∧ ¬ a (p*n) ≡ a n [MOD p^2] := by
  dsimp only
  have one : 1 ≤ (p-1)/3 := by
    change p % 3 = 1 % 3 at res
    have := prime.one_lt
    omega
  have eqn : p^(s+2)+1 = 1 + p*p^(s+1) := by rw [pow_succ']; omega
  have fail : ¬ a (p*(p^(s+2)+1)) ≡ a (p^(s+2)+1) [MOD p^2] := by
    apply (failure_iff_digits prime res (by omega)).mpr
    refine ⟨nontrivial,?_,?_⟩
    · rw [Nat.dvd_iff_mod_eq_zero,eqn]
      simp [Nat.mod_eq_of_lt prime.one_lt]
    · rw [eqn,Nat.digits_add p prime.one_lt 1 _ prime.one_lt (Or.inl one_ne_zero)]
      have hp : p.digits (p^(s+1)) = List.replicate (s+1) 0 ++ [1] := by
        simpa [Nat.digits_of_lt p 1 one_ne_zero prime.one_lt] using
          (Nat.digits_base_pow_mul (k:=s+1) prime.one_lt (m:=1) (by decide))
      rw [hp]
      simpa [List.mem_replicate] using one
  have le : p^2 ≤ p^(s+2) := Nat.pow_le_pow_right prime.pos (by omega)
  exact ⟨by omega,fun h => by have := (excluded_iff_lt_sq_of_failure prime res (by omega) fail).mp h; omega,fail⟩

/-- The first failure outside the proposed exclusions occurs exactly at p²+1. -/
theorem least_unexcluded_failure {p : ℕ} (prime : p.Prime) (res : p ≡ 1 [MOD 3])
    (nontrivial : ¬ a p ≡ 1 [MOD p^2]) :
    IsLeast {n : ℕ | 0 < n ∧ ¬ excluded p n ∧ ¬ a (p*n) ≡ a n [MOD p^2]} (p^2+1) := by
  refine ⟨power_plus_one_failure prime res nontrivial 0, ?_⟩
  rintro n ⟨hn,ex,bad⟩
  have le : p^2 ≤ n := Nat.le_of_not_gt (fun lt => ex ((excluded_iff_lt_sq_of_failure prime res hn bad).mpr lt))
  have ne : n ≠ p^2 := by
    rintro rfl
    exact ((failure_iff_digits prime res hn).mp bad).2.1 (dvd_pow_self p (by decide))
  omega

end TripleFactorial

namespace BalaHarmonic
open Finset

/-- Multiplying by the lower index cancels the denominator in the prime-square ring. -/
private theorem signed_choose (p : ℕ) (prime : p.Prime) (j : ℕ) (pos : 0 < j) (ltp : j < p) :
    (-1 : ZMod (p^2))^j * (p.choose j : ZMod (p^2)) = -(p : ZMod (p^2)) * (j : ZMod (p^2))⁻¹ := by

  have square : (p : ZMod (p^2))*(p : ZMod (p^2)) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, ← pow_two]
  have h (i : ℕ) (hi : i+1 < p) :
      ((i+1:ℕ):ZMod (p^2))*(-1:ZMod (p^2))^(i+1)*(p.choose (i+1) : ZMod (p^2)) = -(p:ZMod (p^2)) := by
    induction i with
    | zero => simp
    | succ i ih =>
      let k := i+1
      have hk : k<p := by dsimp [k]; omega
      have hrec := congrArg (fun n : ℕ => (n:ZMod (p^2))) (Nat.choose_succ_right_eq p k)
      change ((p.choose (k+1) * (k+1) : ℕ):ZMod (p^2)) = ((p.choose k * (p-k) : ℕ):ZMod (p^2)) at hrec
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hk.le] at hrec
      obtain ⟨a,ha⟩ := prime.dvd_choose_self (k:=k) (by dsimp [k];omega) hk
      have zero : (p.choose k : ZMod (p^2)) * (p:ZMod (p^2)) = 0 := by
        rw [ha, Nat.cast_mul]
        linear_combination (a:ZMod (p^2))*square
      change ((k+1:ℕ):ZMod (p^2))*(-1:ZMod (p^2))^(k+1)*(p.choose (k+1):ZMod (p^2)) = _
      push_cast
      calc
        _ = -(-1:ZMod (p^2))^k * ((p.choose (k+1):ZMod (p^2))*((k:ZMod (p^2))+1)) := by rw [pow_succ (-1:ZMod (p^2)) k]; ring
        _ = -(-1:ZMod (p^2))^k * ((p.choose k:ZMod (p^2))*((p:ZMod (p^2))-k)) := by rw [hrec]
        _ = (k:ZMod (p^2))*(-1:ZMod (p^2))^k*(p.choose k:ZMod (p^2)) := by linear_combination -(-1:ZMod (p^2))^k * zero
        _ = _ := ih hk
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
  have hi := h i ltp
  have hu : IsUnit ((i+1:ℕ):ZMod (p^2)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (prime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt pos ltp)).symm.pow_right 2
  have hinv := ZMod.mul_inv_of_unit ((i+1:ℕ):ZMod (p^2)) hu
  calc
    _ = (((i+1:ℕ):ZMod (p^2))*(-1:ZMod (p^2))^(i+1)*(p.choose (i+1):ZMod (p^2)))*((i+1:ℕ):ZMod (p^2))⁻¹ := by
      change (-1:ZMod (p^2))^(i+1)*_ = _
      linear_combination -((-1:ZMod (p^2))^(i+1)*(p.choose (i+1):ZMod (p^2)))*hinv
    _ = _ := by rw [hi]

/-- At a cube root of unity, six further factors of (1-x) multiply its positive powers by (-27). -/
private theorem power_six {A : Type*} [CommRing A] (x : A) (hx : x^3=1) (t : ℕ) :
    (1-x)^(6*t+1) = (-27:A)^t*(1-x) := by
  have h : (1-x)^7=(-27:A)*(1-x) := by
    linear_combination (-x^4 + 7*x^3 -21*x^2 +34*x-28)*hx
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 6*(t+1)+1=6*t+1+6 by omega, pow_add, ih, pow_succ (-27:A),
      mul_assoc, ← pow_succ' (1-x) 6, h, mul_assoc]

/-- The coefficient of the identity in the cyclic group algebra gathers indices divisible by three. -/
private theorem grouped {R : Type*} [CommRing R] (t : ℕ) :
    ∑ j ∈ range (6*t+2), (if 3 ∣ j then (-1:R)^j * ((6*t+1).choose j : R) else 0) =
       (-27:R)^t := by
  classical
  let x : AddMonoidAlgebra R (ZMod 3) := AddMonoidAlgebra.single 1 1
  have hx : x^3=1 := by
    rw [show x=AddMonoidAlgebra.single (1:ZMod 3) (1:R) from rfl, AddMonoidAlgebra.single_pow,
      AddMonoidAlgebra.one_def]
    norm_num
    rfl
  let n := 6*t+1
  let A := AddMonoidAlgebra R (ZMod 3)
  have hsingle (j : ℕ) : (-x)^j * (n.choose j : A) =
      AddMonoidAlgebra.single (j:ZMod 3) ((-1:R)^j * (n.choose j:R)) := by
    rw [show -x=AddMonoidAlgebra.single (1:ZMod 3) (-1:R) from by simp [x],
      AddMonoidAlgebra.single_pow, AddMonoidAlgebra.natCast_def, AddMonoidAlgebra.single_mul_single]
    simp
  have lhs : (1-x)^n = ∑ j ∈ range (n+1), AddMonoidAlgebra.single (j:ZMod 3)
      ((-1:R)^j*(n.choose j:R)) := by
    rw [show 1-x=(-x)+1 by ring, add_pow]
    simp [hsingle]
  have rhs : ((-27:A)^t * (1-x)).coeff 0 = (-27:R)^t := by
    rw [show (-27:A)=AddMonoidAlgebra.single (0:ZMod 3) (-27:R) from by
      simpa only [Int.cast_neg,Int.cast_ofNat] using
        (AddMonoidAlgebra.intCast_def (R:=R) (M:=ZMod 3) (-27:ℤ)),
      AddMonoidAlgebra.single_pow]
    rw [smul_zero, mul_sub, mul_one]
    dsimp only [A,x]
    rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
    simp
  have e := congrArg (fun z : A => z.coeff 0) (lhs.symm.trans (power_six x hx t))
  change (∑ j ∈ range (n+1), AddMonoidAlgebra.single (j:ZMod 3) ((-1:R)^j*(n.choose j:R))).coeff 0 = ((-27:A)^t*(1-x)).coeff 0 at e
  rw [rhs,AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply] at e
  simpa +contextual [n,Nat.add_assoc,Finsupp.single_apply,ZMod.natCast_eq_zero_iff] using e

/-- Keeping just the exponents divisible by three in the signed binomial expansion
gives a harmonic sum in the prime-square ring. -/
theorem harmonic (p : ℕ) (prime : p.Prime) (res : p%3=1) :
    (-3 : ZMod (p^2))^((p-1)/2) =
      1 - (p : ZMod (p^2))*∑ j ∈ (Ico 1 p).filter (3 ∣ ·), (j:ZMod (p^2))⁻¹ := by
  let t := p/6
  have odd := prime.eq_two_or_odd
  have hp : 6*t+1=p := by dsimp [t]; omega
  have formula := grouped (R:=ZMod (p^2)) t
  rw [show 6*t+2=p+1 by omega, hp, sum_range_succ, if_neg (show ¬3∣p by omega), add_zero] at formula
  have zeroinsert : range p = insert 0 (Ico 1 p) := by
    ext j
    simp only [mem_range, mem_insert, mem_Ico]
    have := prime.pos
    omega
  rw [zeroinsert,sum_insert (by simp), if_pos (dvd_zero 3), pow_zero,Nat.choose_zero_right,
    Nat.cast_one, one_mul, ← sum_filter] at formula
  have terms : ∑ j ∈ (Ico 1 p).filter (3 ∣ ·), (-1:ZMod (p^2))^j*(p.choose j : ZMod (p^2)) =
      -(p:ZMod (p^2))*∑ j ∈ (Ico 1 p).filter (3 ∣ ·), (j:ZMod (p^2))⁻¹ := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    have h := mem_Ico.mp (mem_filter.mp hj).1
    exact signed_choose p prime j h.1 h.2
  rw [terms, neg_mul, ← sub_eq_add_neg] at formula
  rw [formula, show (p-1)/2=3*t by omega, pow_mul]
  norm_num

end BalaHarmonic

namespace BalaMultiplier
open Finset

def weight (j : ℕ) := if j%3=1 then 0 else if j%3=0 then 1 else 2
def raised (p j : ℕ) := j + weight j * p
private def low (p i : ℕ) := if 3*i+1 < p then 3*i+1 else
  if 3*i+1 < 2*p then 3*i+1-p else 3*i+1-2*p

private theorem raised_info (p j : ℕ) (res : p%3=1) (hj : j ∈ Ico 1 p) :
    raised p j % 3 = 1 ∧ 0 < raised p j ∧ raised p j < 3*p ∧ raised p j ≠ p ∧
    low p ((raised p j-1)/3) = j := by
  rw [mem_Ico] at hj
  unfold raised weight low
  split_ifs
  all_goals try simp only [zero_mul,one_mul,add_zero] at *
  all_goals omega

private theorem low_info (p i : ℕ) (res : p%3=1) (hi : i ∈ (range p).erase ((p-1)/3)) :
    low p i ∈ Ico 1 p ∧ raised p (low p i) = 3*i+1 := by
  simp only [mem_erase,mem_range] at hi
  have center : p = 3*((p-1)/3)+1 := by omega
  have base : (3*i+1)%3=1 := by omega
  have nz : 3*i+1 ≠ p := by omega
  unfold raised weight low
  simp only [mem_Ico]
  split_ifs
  all_goals try simp only [zero_mul,one_mul,add_zero] at *
  all_goals try omega
  exact ⟨⟨Nat.succ_le_succ (Nat.zero_le _), by assumption⟩, trivial⟩

theorem reorder {M : Type*} [CommMonoid M] (f : ℕ → M) {p : ℕ} (res : p%3=1) :
    (∏ i∈(range p).erase ((p-1)/3), f (3*i+1)) =
      ∏ j∈Ico 1 p, f (raised p j) := by
  apply prod_bij' (fun i _ => low p i) (fun j _ => (raised p j-1)/3)
  · exact fun i hi => (low_info p i res hi).1
  · intro j hj
    obtain ⟨hmod,hpos,hlt,hne,_⟩ := raised_info p j res hj
    simp only [mem_erase,mem_range]
    omega
  · intro i hi
    rw [(low_info p i res hi).2]
    omega
  · intro j hj
    exact (raised_info p j res hj).2.2.2.2
  · intro i hi
    rw [(low_info p i res hi).2]

theorem sqzero (p : ℕ) : (p : ZMod (p^2))*(p : ZMod (p^2))=0 := by
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, ← pow_two]

/-- First-order expansion of a product in a ring with a square-zero element. -/
theorem product_linear {R ι : Type*} [CommRing R] [DecidableEq ι]
    (e : R) (sq : e*e=0) (s : Finset ι) (u : ι → R) :
    (∏ i∈s, (1+e*u i)) = 1+e*∑ i∈s, u i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, ih]
    linear_combination (u a * ∑ i∈s, u i)*sq

theorem unit_at (p : ℕ) (prime : p.Prime) (j : ℕ) (hj : j ∈ Ico 1 p) :
    IsUnit (j : ZMod (p^2)) := by
  rw [ZMod.isUnit_iff_coprime]
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  apply prime.coprime_iff_not_dvd.mpr
  have hr := mem_Ico.mp hj
  exact Nat.not_dvd_of_pos_of_lt hr.1 hr.2

theorem expand_units (p : ℕ) (prime : p.Prime) :
    (∏ j∈Ico 1 p, (raised p j : ZMod (p^2))) =
      (∏ j∈Ico 1 p, (j : ZMod (p^2)))*
        (1+(p : ZMod (p^2))*∑ j∈Ico 1 p, (weight j : ZMod (p^2))*(j : ZMod (p^2))⁻¹) := by
  rw [← product_linear _ (sqzero p), ← prod_mul_distrib]
  apply prod_congr rfl
  intro j hj
  have ej := ZMod.mul_inv_of_unit (j : ZMod (p^2)) (unit_at p prime j hj)
  simp only [raised, Nat.cast_add, Nat.cast_mul]
  linear_combination -((weight j : ZMod (p^2))*p)*ej

end BalaMultiplier

namespace BalaMultiplier
open Finset

private theorem mate_mem {p j : ℕ} (hj : j ∈ Ico 1 p) : p-j ∈ Ico 1 p := by
  simp only [mem_Ico] at *
  omega

/-- Opposite residues have opposite inverses after multiplication by p in the square modulus. -/
theorem opposite {p j : ℕ} (hp : p.Prime) (hj : j ∈ Ico 1 p) :
    (p : ZMod (p^2))*((j : ZMod (p^2))⁻¹+((p-j : ℕ) : ZMod (p^2))⁻¹) = 0 := by
  let a : ZMod (p^2) := j
  let b : ZMod (p^2) := (p-j : ℕ)
  have ab : a+b = p := by
    have h : j+(p-j)=p := by have := mem_Ico.mp hj; omega
    dsimp only [a,b]
    rw [← Nat.cast_add,h]
  have au : a*a⁻¹=1 := ZMod.mul_inv_of_unit a (unit_at p hp _ hj)
  have bu : b*b⁻¹=1 := ZMod.mul_inv_of_unit b (unit_at p hp _ (mate_mem hj))
  change (p : ZMod (p^2))*(a⁻¹+b⁻¹) = 0
  calc
    _ = (p : ZMod (p^2))*((a+b)*(a⁻¹*b⁻¹)) := by
      linear_combination -(p : ZMod (p^2))*b⁻¹*au -(p : ZMod (p^2))*a⁻¹*bu
    _ = _ := by rw [ab, ← mul_assoc, sqzero p, zero_mul]

/-- Weighted reciprocal sum of the lifted representatives reduces to the class divisible by three. -/
theorem weighted_sum {p : ℕ} (hp : p.Prime) (res : p%3=1) :
    (p : ZMod (p^2))*(∑ j∈Ico 1 p, (weight j : ZMod (p^2))*(j : ZMod (p^2))⁻¹) =
    (p : ZMod (p^2))*∑ j∈(Ico 1 p).filter (fun j => 3 ∣ j), (j : ZMod (p^2))⁻¹ := by
  let v (j : ℕ) : ZMod (p^2) := if j%3=2 then (p : ZMod (p^2))*(j : ZMod (p^2))⁻¹ else 0
  have pair (j : ℕ) (hj : j∈Ico 1 p) : v j+v (p-j)=0 := by
    have lt := mem_Ico.mp hj
    by_cases c : j%3=2
    · have c' : (p-j)%3=2 := by omega
      simpa only [v,if_pos c,if_pos c',← mul_add] using opposite hp hj
    · have c' : (p-j)%3≠2 := by omega
      simp [v,c,c']
  have swap : (∑ j∈Ico 1 p,v (p-j)) = ∑ j∈Ico 1 p,v j := by
    apply sum_bij' (fun j _ => p-j) (fun j _ => p-j)
    · exact fun j hj => mate_mem hj
    · exact fun j hj => mate_mem hj
    · intro j hj; have := mem_Ico.mp hj; omega
    · intro j hj; have := mem_Ico.mp hj; omega
    · intro _ _; rfl
  have twice : (∑ j∈Ico 1 p,v j)+(∑ j∈Ico 1 p,v j) = 0 := by
    calc
      _ = (∑ j∈Ico 1 p,v j)+(∑ j∈Ico 1 p,v (p-j)) := congrArg _ swap.symm
      _ = _ := by rw [← sum_add_distrib]; exact sum_eq_zero pair
  rw [mul_sum, sum_filter, mul_sum]
  calc
    _ = (∑ j∈Ico 1 p, ((p : ZMod (p^2))*(if 3 ∣ j then (j : ZMod (p^2))⁻¹ else 0) + (v j + v j))) := by
      apply sum_congr rfl
      intro j _
      by_cases c : j%3=0
      · have d := Nat.dvd_of_mod_eq_zero c
        simp [weight,v,c,d]
      · have d : ¬ 3 ∣ j := fun h => c (Nat.mod_eq_zero_of_dvd h)
        by_cases t : j%3=1
        · simp [weight,v,t,d]
        · have u : j%3=2 := by omega
          simp [weight,v,u,d]
          ring
    _ = _ := by rw [sum_add_distrib,sum_add_distrib,twice,add_zero]

end BalaMultiplier

namespace BalaMultiplier
open Finset

private theorem basic_identity {p a : ℕ} (hp : p.Prime) (res : p%3=1)
    (repr : a*p.factorial = 3^(p-1)*∏ i∈range p, (3*i+1)) :
    a*(∏ j∈Ico 1 p,j) = 3^(p-1)*∏ j∈Ico 1 p, raised p j := by
  have pos := hp.pos
  have pred : (p-1)+1=p := by omega
  have fd : p.factorial = p*∏ j∈Ico 1 p,j := by
    conv_lhs => rw [← pred, Nat.factorial_succ, pred]
    rw [← Finset.prod_Ico_id_eq_factorial, pred]
  have c : (p-1)/3 ∈ range p := by simp only [mem_range]; omega
  have ce : 3*((p-1)/3)+1=p := by omega
  rw [fd, ← mul_prod_erase (range p) (fun i => 3*i+1) c] at repr
  simp only [ce] at repr
  have reorder' := reorder id res
  simp only [id_eq] at reorder'
  rw [reorder'] at repr
  exact Nat.eq_of_mul_eq_mul_left pos (by simpa only [mul_left_comm p, mul_comm p, mul_assoc] using repr)

theorem ratio {p a : ℕ} (hp : p.Prime) (res : p%3=1)
    (repr : a*p.factorial = 3^(p-1)*∏ i∈range p, (3*i+1)) :
    (a : ZMod (p^2)) = 3^(p-1)*
       (1+(p : ZMod (p^2))*∑ j∈(Ico 1 p).filter (fun j => 3 ∣ j), (j : ZMod (p^2))⁻¹) := by
  have nat := basic_identity hp res repr
  have casted := congrArg (fun z : ℕ => (z : ZMod (p^2))) nat
  push_cast at casted
  rw [expand_units p hp, weighted_sum hp res] at casted
  have u : IsUnit (∏ j∈Ico 1 p, (j : ZMod (p^2))) := by
    have gen (s : Finset ℕ) (hs : ∀ j∈s, IsUnit (j : ZMod (p^2))) :
        IsUnit (∏ j∈s, (j : ZMod (p^2))) := by
      induction s using Finset.induction_on with
      | empty => simp
      | insert x s hx ih =>
        rw [prod_insert hx]
        exact (hs x (by simp)).mul (ih (fun j hj => hs j (mem_insert_of_mem hj)))
    exact gen _ (unit_at p hp)
  apply u.mul_left_cancel
  linear_combination casted

/-- Convert a harmonic formula for the signed half-power into the explicit multiplier. -/
theorem closed_multiplier {p a : ℕ} (hp : p.Prime) (res : p%3=1)
    (repr : a*p.factorial = 3^(p-1)*∏ i∈range p, (3*i+1))
    (harmonic : (-3 : ZMod (p^2))^((p-1)/2) =
        1-(p : ZMod (p^2))*∑ j∈(Ico 1 p).filter (fun j => 3 ∣ j), (j : ZMod (p^2))⁻¹) :
    (a : ZMod (p^2)) = (-3)^((p-1)/2) := by
  have odd := hp.mod_two_eq_one_iff_ne_two.mpr (show p ≠ 2 from by omega)
  have power : (3 : ZMod (p^2))^(p-1) = ((-3 : ZMod (p^2))^((p-1)/2))^2 := by
    calc
      _ = ((3 : ZMod (p^2))^2)^((p-1)/2) := by rw [← pow_mul]; congr 1; omega
      _ = ((-3 : ZMod (p^2))^2)^((p-1)/2) := by norm_num
      _ = _ := by rw [← pow_mul, Nat.mul_comm, pow_mul]
  rw [ratio hp res repr, power, harmonic]
  generalize (∑ j∈(Ico 1 p).filter (fun j => 3 ∣ j), (j : ZMod (p^2))⁻¹) = S
  linear_combination ((p : ZMod (p^2))*S^3-S^2)*sqzero p

end BalaMultiplier

namespace TripleFactorial
open OMA.S_oeis_a034171

/-- The one-block multiplier has a closed form that involves only the prime. -/
theorem explicit_multiplier {p : ℕ} (hp : p.Prime) (res : p ≡ 1 [MOD 3]) :
    (a p : ZMod (p^2)) = (-3)^((p-1)/2) :=
  BalaMultiplier.closed_multiplier hp res (representation p hp.pos) (BalaHarmonic.harmonic p hp res)

/-- A prime-square congruence valid at every positive index with no exceptional cases. -/
theorem explicit_lift {p n : ℕ} (hp : p.Prime) (res : p ≡ 1 [MOD 3]) (pos : 0 < n) :
    (a (p*n) : ZMod (p^2)) = ((-3 : ZMod (p^2))^((p-1)/2))^n*(a n : ZMod (p^2)) := by
  have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (all_prime_lift hp res pos)
  rw [Nat.cast_mul,Nat.cast_pow,explicit_multiplier hp res] at h
  exact h

end TripleFactorial

namespace BalaWieferich

/-- A square root of one congruent to one at an odd prime is one modulo its square. -/
theorem root_one {p : ℕ} (prime : p.Prime) (odd : p ≠ 2) (x : ZMod (p^2))
    (red : ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p) x = 1) :
    x=1 ↔ x^2=1 := by
  let _ : NeZero p := ⟨prime.ne_zero⟩
  let ρ := ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)
  have hx := ZMod.natCast_zmod_val x
  have hx' : (x.val : ZMod p)=1 :=
    calc
      _ = ρ (x.val : ZMod (p^2)) := (map_natCast ρ x.val).symm
      _ = 1 := by rw [hx]; exact red
  have two : ¬ p ∣ 2 := by
    intro d
    exact odd (((Nat.dvd_prime (by decide : Nat.Prime 2)).mp d).resolve_left prime.ne_one)
  have unit : IsUnit (x+1) := by
    have hu : IsUnit ((x.val+1:ℕ):ZMod (p^2)) := by
      rw [ZMod.isUnit_iff_coprime]
      apply Nat.Coprime.pow_right
      apply Nat.Coprime.symm
      apply prime.coprime_iff_not_dvd.mpr
      intro d
      have hd := (ZMod.natCast_eq_zero_iff (x.val+1) p).mpr d
      rw [Nat.cast_add,Nat.cast_one,hx'] at hd
      exact two ((ZMod.natCast_eq_zero_iff 2 p).mp (by norm_cast at hd ⊢))
    simpa only [Nat.cast_add,Nat.cast_one,hx] using hu
  refine ⟨fun h => by simp [h],fun h => ?_⟩
  have pair : (x-1)*(x+1)=0 := by linear_combination h
  have inv := ZMod.mul_inv_of_unit (x+1) unit
  linear_combination (x+1)⁻¹*pair - (x-1)*inv

/-- For a prime congruent to one modulo three, the signed half-power is one
modulo its square exactly when the prime is Wieferich to base three. -/
theorem base_test {p : ℕ} (prime : p.Prime) (res : p%3=1) :
    (-3 : ZMod (p^2))^((p-1)/2) = 1 ↔ (3 : ℕ)^(p-1) ≡ 1 [MOD p^2] := by
  let T : ZMod (p^2) := (-3)^((p-1)/2)
  let ρ := ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)
  have red : ρ T=1 := by
    have h := congrArg ρ (BalaHarmonic.harmonic p prime res)
    simpa only [map_sub,map_one,map_mul,map_natCast,ZMod.natCast_self,zero_mul,sub_zero,T] using h
  have odd := prime.eq_two_or_odd
  have hpow : T^2 = (3:ZMod (p^2))^(p-1) := by
    have even : (p-1)/2 * 2 = p-1 := by omega
    calc
      _ = ((-3 : ZMod (p^2))^2)^((p-1)/2) := by dsimp [T]; rw [←pow_mul,←pow_mul,Nat.mul_comm]
      _ = ((3:ZMod (p^2))^2)^((p-1)/2) := by norm_num
      _ = (3:ZMod (p^2))^(p-1) := by rw [←pow_mul, Nat.mul_comm, even]
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat]
  exact (root_one prime (by omega) T red).trans (by rw [hpow])

end BalaWieferich

namespace BalaWieferich
open OMA.S_oeis_a034171 in
/-- Replacing the prime-index multiplier by its half-power formula isolates a
condition on p and the two base-p digit conditions on n. -/
theorem failure_iff_wieferich_digits {p n : ℕ} (prime : p.Prime) (res : p ≡ 1 [MOD 3])
    (pos : 0 < n) (multiplier : (a p : ZMod (p^2)) = (-3 : ZMod (p^2))^((p-1)/2)) :
    (¬ a (p*n) ≡ a n [MOD p^2]) ↔
      (¬ (3 : ℕ)^(p-1) ≡ 1 [MOD p^2]) ∧ (¬ p ∣ n) ∧ ∀ d ∈ p.digits n, d ≤ (p-1)/3 := by
  have prime_class : a p ≡ 1 [MOD p^2] ↔ (3:ℕ)^(p-1) ≡ 1 [MOD p^2] := by
    rw [← ZMod.natCast_eq_natCast_iff (a p) 1, Nat.cast_one, multiplier]
    exact base_test prime res
  rw [TripleFactorial.failure_iff_digits prime res pos, prime_class]

open OMA.S_oeis_a034171 in
theorem exact_failure {p n : ℕ} (prime : p.Prime) (res : p ≡ 1 [MOD 3]) (pos : 0 < n) :
    (¬ a (p*n) ≡ a n [MOD p^2]) ↔
      (¬ (3 : ℕ)^(p-1) ≡ 1 [MOD p^2]) ∧ (¬ p ∣ n) ∧ ∀ d ∈ p.digits n, d ≤ (p-1)/3 :=
  failure_iff_wieferich_digits prime res pos
    (BalaMultiplier.closed_multiplier prime res (TripleFactorial.representation _ prime.pos)
      (BalaHarmonic.harmonic p prime res))

end BalaWieferich

namespace TripleFactorial
open OMA.S_oeis_a034171

private theorem exceptional_power : (-3 : ZMod (1006003^2))^503001 = 1 := by
  have h1 : (-3 : ZMod (1006003^2))^1 = 1012042036006 := by decide +kernel
  have h3 : (-3 : ZMod (1006003^2))^3 = 1012042035982 := by
    rw [show 3 = (1+1)+1 by decide, pow_add, pow_one, pow_add,h1]
    decide +kernel
  have h7 : (-3 : ZMod (1006003^2))^7 = 1012042033822 := by
    rw [show 7 = (3+3)+1 by decide, pow_add, pow_one, pow_add,h3]
    decide +kernel
  have h15 : (-3 : ZMod (1006003^2))^15 = 1012027687102 := by
    rw [show 15 = (7+7)+1 by decide, pow_add, pow_one, pow_add,h7]
    decide +kernel
  have h30 : (-3 : ZMod (1006003^2))^30 = 446598784822 := by
    rw [show 30 = 15+15 by decide, pow_add,h15]
    decide +kernel
  have h61 : (-3 : ZMod (1006003^2))^61 = 159642800801 := by
    rw [show 61 = (30+30)+1 by decide, pow_add, pow_one, pow_add,h30]
    decide +kernel
  have h122 : (-3 : ZMod (1006003^2))^122 = 104485392181 := by
    rw [show 122 = 61+61 by decide, pow_add,h61]
    decide +kernel
  have h245 : (-3 : ZMod (1006003^2))^245 = 116577582316 := by
    rw [show 245 = (122+122)+1 by decide, pow_add, pow_one, pow_add,h122]
    decide +kernel
  have h491 : (-3 : ZMod (1006003^2))^491 = 225032459773 := by
    rw [show 491 = (245+245)+1 by decide, pow_add, pow_one, pow_add,h245]
    decide +kernel
  have h982 : (-3 : ZMod (1006003^2))^982 = 699666208663 := by
    rw [show 982 = 491+491 by decide, pow_add,h491]
    decide +kernel
  have h1964 : (-3 : ZMod (1006003^2))^1964 = 739005455314 := by
    rw [show 1964 = 982+982 by decide, pow_add,h982]
    decide +kernel
  have h3929 : (-3 : ZMod (1006003^2))^3929 = 585726740563 := by
    rw [show 3929 = (1964+1964)+1 by decide, pow_add, pow_one, pow_add,h1964]
    decide +kernel
  have h7859 : (-3 : ZMod (1006003^2))^7859 = 817721403535 := by
    rw [show 7859 = (3929+3929)+1 by decide, pow_add, pow_one, pow_add,h3929]
    decide +kernel
  have h15718 : (-3 : ZMod (1006003^2))^15718 = 8456740733 := by
    rw [show 15718 = 7859+7859 by decide, pow_add,h7859]
    decide +kernel
  have h31437 : (-3 : ZMod (1006003^2))^31437 = 276162628831 := by
    rw [show 31437 = (15718+15718)+1 by decide, pow_add, pow_one, pow_add,h15718]
    decide +kernel
  have h62875 : (-3 : ZMod (1006003^2))^62875 = 36288490033 := by
    rw [show 62875 = (31437+31437)+1 by decide, pow_add, pow_one, pow_add,h31437]
    decide +kernel
  have h125750 : (-3 : ZMod (1006003^2))^125750 = 206178610824 := by
    rw [show 125750 = 62875+62875 by decide, pow_add,h62875]
    decide +kernel
  have h251500 : (-3 : ZMod (1006003^2))^251500 = 575340845266 := by
    rw [show 251500 = 125750+125750 by decide, pow_add,h125750]
    decide +kernel
  have h503001 : (-3 : ZMod (1006003^2))^503001 = 1 := by
    rw [show 503001 = (251500+251500)+1 by decide, pow_add, pow_one, pow_add,h251500]
    decide +kernel
  exact h503001

/-- A concrete eligible base-three Wieferich prime satisfies the uncorrected law for every index. -/
theorem at_1006003 (n : ℕ) (pos : 0<n) : a (1006003*n) ≡ a n [MOD 1006003^2] := by
  have hp : Nat.Prime 1006003 := by norm_num
  have h := explicit_lift hp (by decide) (n:=n) pos
  change _ = ((-3 : ZMod (1006003^2))^503001)^n*_ at h
  rw [exceptional_power,one_pow,one_mul] at h
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h

end TripleFactorial

namespace TripleFactorial
open OMA.S_oeis_a034171

/-- A prime is exceptional for the congruence at all indices exactly when it is base-three Wieferich. -/
theorem universal_iff_wieferich {p : ℕ} (hp : p.Prime) (res : p ≡ 1 [MOD 3]) :
    (∀ n, 0 < n → ¬ excluded p n → a (p*n) ≡ a n [MOD p^2]) ↔
      (3 : ℕ)^(p-1) ≡ 1 [MOD p^2] := by
  have multiplier : a p ≡ 1 [MOD p^2] ↔ (3 : ℕ)^(p-1) ≡ 1 [MOD p^2] := by
    rw [← ZMod.natCast_eq_natCast_iff (a p) 1, Nat.cast_one, explicit_multiplier hp res]
    exact BalaWieferich.base_test hp res
  constructor
  · intro all
    by_contra neg
    obtain ⟨pos,hx,fail⟩ := power_plus_one_failure hp res (fun h => neg (multiplier.mp h)) 0
    exact fail (all _ pos hx)
  · intro hw n hn _
    by_contra fail
    exact ((BalaWieferich.exact_failure hp res hn).mp fail).1 hw

/-- If the prime fails the base-three Wieferich test, the first genuine failure is p²+1. -/
theorem first_failure_at_square_plus_one {p : ℕ} (hp : p.Prime) (res : p ≡ 1 [MOD 3])
    (nonw : ¬ (3 : ℕ)^(p-1) ≡ 1 [MOD p^2]) :
    IsLeast {n : ℕ | 0 < n ∧ ¬ excluded p n ∧ ¬ a (p*n) ≡ a n [MOD p^2]} (p^2+1) := by
  apply least_unexcluded_failure hp res
  intro h
  apply nonw
  apply (BalaWieferich.base_test hp res).mp
  rw [← explicit_multiplier hp res]
  simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff (a p) 1 _).mpr h

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
#print axioms TripleFactorial.bounded_digit_count
#print axioms TripleFactorial.bounded_unit_count
#print axioms TripleFactorial.failure_count
#print axioms TripleFactorial.failure_count_zero
#print axioms TripleFactorial.excluded_iff_lt_sq_of_failure
#print axioms TripleFactorial.unexcluded_failure_count
#print axioms TripleFactorial.unexcluded_failure_count_small
#print axioms TripleFactorial.power_plus_one_failure
#print axioms TripleFactorial.least_unexcluded_failure
#print axioms BalaHarmonic.harmonic
#print axioms BalaMultiplier.weighted_sum
#print axioms BalaMultiplier.ratio
#print axioms BalaMultiplier.closed_multiplier
#print axioms TripleFactorial.explicit_multiplier
#print axioms TripleFactorial.explicit_lift
#print axioms BalaWieferich.root_one
#print axioms BalaWieferich.base_test
#print axioms BalaWieferich.exact_failure
#print axioms BalaWieferich.failure_iff_wieferich_digits
#print axioms TripleFactorial.at_1006003
#print axioms TripleFactorial.universal_iff_wieferich
#print axioms TripleFactorial.first_failure_at_square_plus_one
