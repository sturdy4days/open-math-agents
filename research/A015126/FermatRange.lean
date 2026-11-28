import OMAStatements.S_oeis_a015126
import Mathlib.NumberTheory.Fermat
import Mathlib.Combinatorics.Colex
import Mathlib.Tactic.Linarith

/-!
# Odd preimages of powers of two under Euler's totient

The classical Fermat-prime factorization gives a strict upper bound for each odd
preimage and identifies its prime factors by the binary digits of the exponent.
We use Mathlib's Fermat-number criterion and binary support for finite sums.
The official OEIS statement supplies the definition of the minimum preimage.
-/

namespace OMA.S_oeis_a015126

/-- Remove the full power of any specified prime divisor of an odd integer. -/
theorem peel_at_prime {x p : ℕ} (hx : 1 < x) (oddx : Odd x) (hp : p.Prime) (hpx : p ∣ x) :
    ∃ k y : ℕ, 2 < p ∧ x = p^(k+1)*y ∧ ¬p ∣ y ∧
      Nat.totient x = ((p-1)*p^k)*Nat.totient y ∧ p-1 ∣ Nat.totient x ∧
      0 < y ∧ y < x ∧ Odd y := by
  have hx0 : x ≠ 0 := by omega
  have pbig : 2 < p := by
    have low := hp.two_le
    have ne : p ≠ 2 := fun h => oddx.not_two_dvd_nat (h ▸ hpx)
    omega
  have hexp := hp.factorization_pos_of_dvd hx0 hpx
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hexp.ne'
  let y := ordCompl[p] x
  have hprod : p^(k+1)*y = x := by
    change p^k.succ*y = x
    rw [← hk]
    exact Nat.ordProj_mul_ordCompl_eq_self x p
  have hcop : (p^(k+1)).Coprime y := (Nat.coprime_ordCompl hp hx0).pow_left _
  have ht : x.totient = ((p-1)*p^k)*y.totient := by
    calc
      x.totient = (p^(k+1)*y).totient := congrArg Nat.totient hprod.symm
      _ = ((p-1)*p^k)*y.totient := by rw [Nat.totient_mul hcop,Nat.totient_prime_pow_succ hp,mul_comm (p^k)]
  have hy : 0 < y := Nat.ordCompl_pos p hx0
  have high : 1 < p^(k+1) := one_lt_pow₀ hp.one_lt (by omega)
  refine ⟨k,y,pbig,hprod.symm,Nat.not_dvd_ordCompl hp hx0,ht,?_,hy,?_,?_⟩
  · exact ⟨p^k * y.totient,by rw [ht,mul_assoc]⟩
  · calc
      y = 1*y := (one_mul _).symm
      _ < p^(k+1)*y := Nat.mul_lt_mul_of_pos_right high hy
      _ = x := hprod
  · exact (Nat.odd_mul.mp (hprod ▸ oddx)).2

theorem peel_prime_power (x : ℕ) (hx : 1 < x) (oddx : Odd x) :
    ∃ p k y : ℕ, p.Prime ∧ p ∣ x ∧ 2 < p ∧ x = p^(k+1)*y ∧ ¬p ∣ y ∧
      Nat.totient x = ((p-1)*p^k)*Nat.totient y ∧ p-1 ∣ Nat.totient x ∧
      0 < y ∧ y < x ∧ Odd y := by
  obtain ⟨p,hp,hpx⟩ := Nat.exists_prime_and_dvd (by omega : x ≠ 1)
  obtain ⟨k,y,rest⟩ := peel_at_prime hx oddx hp hpx
  exact ⟨p,k,y,hp,hpx,rest⟩

end OMA.S_oeis_a015126

open Finset

namespace OMA.S_oeis_a015126

/-- An odd integer whose totient divides a power of two is a product of distinct
Fermat primes. The second product records their exact contributions to its totient. -/
theorem fermat_support_of_totient_dvd {x m : ℕ} (hx : Odd x) (hφ : x.totient ∣ 2 ^ m) :
    ∃ S : Finset ℕ, S ⊆ range (m + 1) ∧ (∀ i ∈ S, (Nat.fermatNumber i).Prime) ∧
      x = ∏ i ∈ S, Nat.fermatNumber i ∧ x.totient = ∏ i ∈ S, 2 ^ (2 ^ i) := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    by_cases hsmall : x ≤ 1
    · have : x = 1 := by rcases hx with ⟨v, hv⟩; omega
      subst x
      exact ⟨∅, by simp, by simp, by simp, by simp⟩
    obtain ⟨p, k, y, hp, _, hp2, hxy, hpy, htot, hpred, _, hylt, hyodd⟩ :=
      peel_prime_power x (by omega) hx
    have hk : k = 0 := by
      cases k with
      | zero => rfl
      | succ k =>
        have hpx : p ∣ x.totient := by
          rw [htot]
          exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_pow_self p (by omega : k+1 ≠ 0)) _) _
        have : p ∣ 2 := hp.dvd_of_dvd_pow (hpx.trans hφ)
        have := Nat.le_of_dvd (by decide : 0 < 2) this
        omega
    subst k
    simp only [zero_add, pow_one, pow_zero, mul_one] at hxy htot
    have htwo : p - 1 ∣ 2 ^ m := hpred.trans hφ
    obtain ⟨u, hum, hu⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp htwo
    have hpval : p = 2 ^ u + 1 := by omega
    have hu0 : u ≠ 0 := by intro h; simp [h] at hpval; omega
    obtain ⟨i, hi⟩ := Nat.pow_of_pow_add_prime (by decide : 1 < 2) hu0 (hpval ▸ hp)
    have hF : p = Nat.fermatNumber i := by simpa only [Nat.fermatNumber, hi] using hpval
    have hyφ : y.totient ∣ 2 ^ m :=
      (show y.totient ∣ x.totient by rw [htot]; exact dvd_mul_left _ _).trans hφ
    obtain ⟨S, hS, hPrime, hprod, hden⟩ := ih y hylt hyodd hyφ
    have hiS : i ∉ S := fun hm => hpy (hprod ▸ hF ▸ Finset.dvd_prod_of_mem Nat.fermatNumber hm)
    refine ⟨insert i S, Finset.insert_subset ?_ hS, ?_, ?_, ?_⟩
    · exact Finset.mem_range_succ_iff.mpr ((i.lt_two_pow_self.le.trans hi.ge).trans hum)
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hF ▸ hp
      · exact hPrime j hj
    · rw [Finset.prod_insert hiS, ← hprod, ← hF, hxy]
    · rw [Finset.prod_insert hiS, ← hden, htot, hu, hi]

/-- Integer form of the strict bound on every finite subproduct
of the Fermat ratios. The second inequality bounds the denominator at the next index. -/
theorem fermat_subproducts (m : ℕ) (S : Finset ℕ) (hS : S ⊆ range m) :
    (∏ i ∈ S, Nat.fermatNumber i) < 2 * ∏ i ∈ S, (2 : ℕ) ^ (2 ^ i) ∧
    2 * (∏ i ∈ S, (2 : ℕ) ^ (2 ^ i)) ≤ 2 ^ (2 ^ m) := by
  induction m generalizing S with
  | zero =>
    have : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => by simpa using hS hi)
    subst S
    norm_num
  | succ m ih =>
    let T := S.erase m
    have hT : T ⊆ range m := by
      intro i hi
      have hi' := Finset.mem_erase.mp hi
      have hi'' := Finset.mem_range_succ_iff.mp (hS hi'.2)
      exact Finset.mem_range.mpr (by omega)
    obtain ⟨hsmall, hbound⟩ := ih T hT
    let D := ∏ i ∈ T, (2 : ℕ) ^ (2 ^ i)
    let X := ∏ i ∈ T, Nat.fermatNumber i
    let R := (2 : ℕ) ^ (2 ^ m)
    change X < 2*D at hsmall
    change 2*D ≤ R at hbound
    have hpos : 0 < R := pow_pos (by decide) _
    have hnext : 2 ^ (2 ^ (m+1)) = R * R := by
      rw [pow_succ, pow_mul, sq]
    rw [hnext]
    by_cases hm : m ∈ S
    · have hins : insert m T = S := Finset.insert_erase hm
      rw [← hins, Finset.prod_insert (Finset.notMem_erase _ _),
        Finset.prod_insert (Finset.notMem_erase _ _)]
      change (R+1)*X < 2*(R*D) ∧ 2*(R*D) ≤ R*R
      constructor
      · have h := Nat.mul_le_mul_left R (Nat.succ_le_iff.mpr hsmall)
        nlinarith
      · nlinarith [Nat.mul_le_mul_left R hbound]
    · have hEq : T = S := Finset.erase_eq_of_notMem hm
      rw [← hEq]
      exact ⟨hsmall, hbound.trans (by nlinarith [Nat.mul_le_mul_left R hpos])⟩

theorem lt_twice_totient_of_odd_power_two {x m : ℕ} (hx : Odd x) (hφ : x.totient ∣ 2 ^ m) :
    x < 2 * x.totient := by
  obtain ⟨S, hS, _, hprod, hden⟩ := fermat_support_of_totient_dvd hx hφ
  rw [hden, hprod]
  exact (fermat_subproducts (m+1) S hS).1

end OMA.S_oeis_a015126

namespace TotientMinimum

/-- An even number contains at most half as many reduced residues as residues. -/
theorem two_totient_le_of_even (m : ℕ) (hm : Even m) : 2 * m.totient ≤ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    obtain ⟨k, rfl⟩ := hm.two_dvd
    by_cases hk : k = 0
    · simp [hk]
    rcases Nat.even_or_odd k with he | ho
    · have half := ih k (by omega) he
      rw [Nat.totient_two_mul_of_even he]
      omega
    · rw [Nat.totient_two_mul_of_odd ho]
      exact Nat.mul_le_mul_left 2 (Nat.totient_le k)

/-- A witness below twice its totient forces the least preimage to be odd. -/
theorem odd_aSeq_of_lt_two_totient (x : ℕ) (hx : x < 2 * x.totient) :
    Odd (OMA.S_oeis_a015126.aSeq x) := by
  let ex : ∃ m : ℕ, m.totient = x.totient := ⟨x, rfl⟩
  have hmin : OMA.S_oeis_a015126.aSeq x ≤ x := Nat.find_min' ex rfl
  have hval : (OMA.S_oeis_a015126.aSeq x).totient = x.totient := Nat.find_spec ex
  by_contra h
  have he := two_totient_le_of_even _ (Nat.not_odd_iff_even.mp h)
  omega

end TotientMinimum

open Finset

namespace OMA.S_oeis_a015126

/-- The 1-bits of the exponent specify every prime factor of an odd preimage. -/
theorem odd_inverse_eq_fermat_product {x m : ℕ} (hx : Odd x) (hφ : x.totient = 2 ^ m) :
    x = ∏ i ∈ m.bitIndices.toFinset, Nat.fermatNumber i := by
  obtain ⟨S, _, _, hprod, hden⟩ := fermat_support_of_totient_dvd hx hφ.dvd
  have heq : (2 : ℕ)^m = 2 ^ (∑ i ∈ S, 2 ^ i) :=
    hφ.symm.trans (by simpa only [Finset.prod_pow_eq_pow_sum] using hden)
  have hm := Nat.pow_right_injective (by decide : 2 ≤ 2) heq
  simpa only [hm, Finset.toFinset_bitIndices_sum_two_pow] using hprod

theorem odd_aSeq_of_totient_dvd_two_pow {x m : ℕ} (hx : Odd x) (hφ : x.totient ∣ 2^m) :
    Odd (aSeq x) :=
  TotientMinimum.odd_aSeq_of_lt_two_totient _ (lt_twice_totient_of_odd_power_two hx hφ)

/-- The unique odd preimage lies below every even preimage. -/
theorem aSeq_eq_self_of_odd_totient_dvd_two_pow {x m : ℕ} (hx : Odd x)
    (hφ : x.totient ∣ 2^m) : aSeq x = x := by
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hφ
  have hval : (aSeq x).totient = x.totient :=
    Nat.find_spec (⟨x, rfl⟩ : ∃ j : ℕ, j.totient = x.totient)
  exact (odd_inverse_eq_fermat_product (odd_aSeq_of_totient_dvd_two_pow hx hφ) (hval.trans hk)).trans
    (odd_inverse_eq_fermat_product hx hk).symm

end OMA.S_oeis_a015126

#print axioms OMA.S_oeis_a015126.peel_prime_power
#print axioms OMA.S_oeis_a015126.fermat_support_of_totient_dvd
#print axioms OMA.S_oeis_a015126.fermat_subproducts
#print axioms OMA.S_oeis_a015126.lt_twice_totient_of_odd_power_two
#print axioms OMA.S_oeis_a015126.odd_inverse_eq_fermat_product
#print axioms OMA.S_oeis_a015126.odd_aSeq_of_totient_dvd_two_pow
#print axioms OMA.S_oeis_a015126.aSeq_eq_self_of_odd_totient_dvd_two_pow
#print axioms TotientMinimum.two_totient_le_of_even
#print axioms TotientMinimum.odd_aSeq_of_lt_two_totient
