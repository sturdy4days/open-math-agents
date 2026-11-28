import ModuloNine
import PriorLift

/-!
# Multinacci periods modulo every higher power of three

This module applies Matt Gaiser’s proven conditional lifting theorem to the
nonexceptional modulus-nine period from ModuloNine. For n≥2 and r≥1 it proves
T(n,3^r)=3^(r−1) T(n,3), and gives both closed-form families of widths.
-/
namespace A210456AllPowers

open OMA.S_oeis_a351889

/-- Matt Gaiser's solution of Wu's conditional lifting conjecture at the prime three. -/
theorem ternary_period_lift {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r)
    (hlift : a351889 n 3 ≠ a351889 n 9) :
    a351889 n (3 ^ r) = 3 ^ (r - 1) * a351889 n 3 := by
  exact OMA.solution.2 n 3 r hn (by decide) hr hlift

/-- The values of a positive period at 3 and 9 suffice to evaluate every higher power. -/
theorem ternary_period_of_base {n r t : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r) (ht : 0 < t)
    (h3 : a351889 n 3 = t) (h9 : a351889 n 9 = 3 * t) :
    a351889 n (3 ^ r) = 3 ^ (r - 1) * t := by
  have hlift : a351889 n 3 ≠ a351889 n 9 := by omega
  rw [ternary_period_lift hn hr hlift, h3]

end A210456AllPowers

namespace Multinacci351889

open OMA.S_oeis_a351889

/-- At widths q−1 and q for q=3^k, the characteristic-three periods lift exactly
by one factor of three per additional power of the modulus. -/
theorem exact_periods (k r : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    a351889 (3^k-1) (3^r) = 3^(r-1)*(3^(2*k)-1) ∧
    a351889 (3^k) (3^r) = 3^(r-1)*((3^k)^2+3^k+1) := by
  obtain ⟨q3,q9,c3,c9⟩ := prime_cases k hk
  have big : 3 ≤ (3:ℕ)^k := by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 3) hk
  have large : 1 < (3:ℕ)^(2*k) := one_lt_pow₀ (by decide) (by omega)
  exact ⟨A210456AllPowers.ternary_period_of_base (by omega) hr (by omega) q3 q9,
    A210456AllPowers.ternary_period_of_base (by omega) hr (Nat.zero_lt_succ _) c3 c9⟩

/-- Chai Wah Wu's conjecture 3 on OEIS A351889 at the prime p=3. -/
theorem wu_third_ternary (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    a351889 (3^m) (3^k) = (3^(3*m)-1)*3^(k-1)/(3^m-1) := by
  let q := (3:ℕ)^m
  have qp : 1 < q := one_lt_pow₀ (by decide) (by omega)
  have factor : q^3-1 = (q-1)*(q^2+q+1) := by
    obtain ⟨u,hu⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    rw [hu,Nat.succ_sub_one]
    rw [show (u+1)^3 = u*((u+1)^2+(u+1)+1)+1 by ring,Nat.add_sub_cancel]
  rw [(exact_periods m k hm hk).2, Nat.mul_comm 3 m, pow_mul]
  change 3^(k-1)*(q^2+q+1) = (q^3-1)*3^(k-1)/(q-1)
  rw [factor, show ((q-1)*(q^2+q+1))*3^(k-1) = (3^(k-1)*(q^2+q+1))*(q-1) by ring,
    Nat.mul_div_cancel _ (by omega : 0 < q-1)]

end Multinacci351889

namespace Multinacci351889

open OMA.S_oeis_a351889

/-- Every modulus-three period at width at least two triples at each higher power. -/
theorem ternary_all_widths (n r : ℕ) (hn : 2 ≤ n) (hr : 1 ≤ r) :
    a351889 n (3^r) = 3^(r-1)*a351889 n 3 :=
  A210456AllPowers.ternary_period_of_base (by omega) hr
    (period_realized_finite (by omega) (by decide)).1 rfl (nine_direct n hn)

end Multinacci351889
