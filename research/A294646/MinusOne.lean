import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
The Sydney University Mathematical Society Problems Competition 2004 solutions,
Problem 2, give the general odd-modulus theorem for every positive base.
https://www.maths.usyd.edu.au/u/SUMSCOMP/sols2004.pdf
The corollary is the second exclusion in OEIS A294646.
https://oeis.org/A294646
-/

namespace A294646

private theorem prod_congruent_one (q : ℕ) (l : List ℕ)
    (h : ∀ p ∈ l, p ≡ 1 [MOD q]) : l.prod ≡ 1 [MOD q] := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simpa using (h p (by simp)).mul (ih fun r hr => h r (by simp [hr]))

/-- No odd modulus greater than one divides one more than a base to the
power one less than the modulus. -/
theorem not_dvd_pow_pred_add_one (b m : ℕ) (hm : 1 < m) (ho : Odd m) :
    ¬ m ∣ b^(m-1)+1 := by
  intro h
  obtain ⟨k,u,hu,hmu⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : m-1 ≠ 0)
  have primeStep (p : ℕ) (hp : p.Prime) (hpm : p ∣ m) : p ≡ 1 [MOD 2^(k+1)] := by
    have : Fact p.Prime := ⟨hp⟩
    have hp2 := hp.two_le
    have hpne : p ≠ 2 := fun he => ho.not_two_dvd_nat (he ▸ hpm)
    obtain ⟨j,v,hv,hpv⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : p-1 ≠ 0)
    have zero := (ZMod.natCast_eq_zero_iff _ p).mpr (hpm.trans h)
    push_cast at zero
    have neg : (b : ZMod p)^(m-1) = -1 := by linear_combination zero
    have hb : (b : ZMod p) ≠ 0 := by
      intro e
      rw [e,zero_pow (by omega : m-1 ≠ 0)] at zero
      simp at zero
    have hj : k < j := by
      by_contra! hjk
      obtain ⟨s,hs⟩ := pow_dvd_pow 2 hjk
      have hexp : (m-1)*v = (p-1)*(s*u) := by rw [hmu,hpv,hs]; ring
      have clash : (-1 : ZMod p) = 1 := calc
        _ = ((b : ZMod p)^(m-1))^v := by rw [neg,hv.neg_one_pow]
        _ = ((b : ZMod p)^(p-1))^(s*u) := by rw [← pow_mul,← pow_mul,hexp]
        _ = 1 := by rw [ZMod.pow_card_sub_one_eq_one hb,one_pow]
      have z : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination -clash
      have lp := Nat.le_of_dvd (by decide : 0 < 2) ((ZMod.natCast_eq_zero_iff _ _).mp z)
      omega
    apply Nat.ModEq.symm
    apply (Nat.modEq_iff_dvd' (show 1≤p by omega)).mpr
    rw [hpv]
    exact dvd_mul_of_dvd_left (pow_dvd_pow _ hj) _
  have hh := prod_congruent_one (2^(k+1)) m.primeFactorsList
    fun p hp => primeStep p (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)
  rw [Nat.prod_primeFactorsList (by omega)] at hh
  have hh' := (Nat.modEq_iff_dvd' (show 1≤m by omega)).mp hh.symm
  rw [hmu,pow_succ] at hh'
  exact hu.not_two_dvd_nat (Nat.dvd_of_mul_dvd_mul_left (pow_pos (by decide) _) hh')

/-- The inverse of 4ⁿ modulo 2n+1 cannot equal 2n. -/
theorem never_twice_index (n : ℕ) (hn : 0 < n) :
    ¬ (2*n*4^n ≡ 1 [MOD 2*n+1]) := by
  intro h
  have z := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  push_cast at z
  have eqm : ((2*n : ℕ) : ZMod (2*n+1)) = -1 := by
    have hz := (ZMod.natCast_eq_zero_iff (2*n+1) (2*n+1)).mpr dvd_rfl
    push_cast at hz ⊢
    linear_combination hz
  push_cast at eqm
  rw [eqm] at z
  apply not_dvd_pow_pred_add_one 2 (2*n+1) (by omega) ⟨n,rfl⟩
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [show 2*n+1-1 = 2*n by omega,pow_mul]
  push_cast
  linear_combination -z

end A294646
