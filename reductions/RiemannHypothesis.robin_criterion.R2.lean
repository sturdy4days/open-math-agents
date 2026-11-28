import FormalConjectures.Paper.RiemannHypothesisEquivalents
import Mathlib

/-! # Robin's criterion on superabundant integers

An integer is superabundant when its divisor sum divided by itself exceeds
that of every smaller positive integer. A first record past 5040, together
with verification up to that record, allows every larger integer to be
compared with a superabundant integer from the same initial segment. -/

/- The marginal gain in abundancy from increasing a prime exponent
decreases as either the prime or the new exponent increases. -/
namespace RobinRecord
open Finset

theorem ratio_as_reciprocal_sum {x : ℝ} (hx : 1 < x) {j : ℕ} (hj : 0 < j) :
    (1 - x⁻¹ ^ (j + 1)) / (1 - x⁻¹ ^ j) =
      1 + 1 / (x * ∑ i ∈ range j, x ^ i) := by
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x ≠ 1 := ne_of_gt hx
  have hp : 1 < x ^ j := one_lt_pow₀ hx (Nat.ne_of_gt hj)
  have hd : x ^ j - 1 ≠ 0 := by linarith
  rw [geom_sum_eq hx1 j, inv_pow, inv_pow, pow_succ]
  field_simp [hx0, hx1, hd]
  ring

theorem gain_mono {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q)
    {j k : ℕ} (hj : 0 < j) (hjk : j ≤ k) :
    (1 - q⁻¹ ^ (k + 1)) / (1 - q⁻¹ ^ k) ≤
      (1 - p⁻¹ ^ (j + 1)) / (1 - p⁻¹ ^ j) := by
  rw [ratio_as_reciprocal_sum (hp.trans_le hpq) (hj.trans_le hjk),
    ratio_as_reciprocal_sum hp hj]
  apply add_le_add_right
  have hpos : 0 < ∑ i ∈ range j, p ^ i := by
    apply sum_pos
    · intro i hi
      positivity
    · exact ⟨0, mem_range.mpr hj⟩
  apply one_div_le_one_div_of_le (mul_pos (by linarith : 0 < p) hpos)
  apply mul_le_mul hpq _ hpos.le (by linarith)
  calc
    (∑ i ∈ range j, p ^ i) ≤ ∑ i ∈ range j, q ^ i := by
      apply sum_le_sum
      intro i hi
      exact pow_le_pow_left₀ (by linarith) hpq i
    _ ≤ ∑ i ∈ range k, q ^ i := by
      apply sum_le_sum_of_subset_of_nonneg (range_mono hjk)
      intro i hi h
      exact pow_nonneg (by linarith : 0 ≤ q) i

end RobinRecord

/- The following identity is the prime-layer calculation of Robin1984, CAProfile,
written directly for Mathlib's divisor sum (kimihiro64, Apache-2.0). -/
namespace RobinProfile
open Finset
open ArithmeticFunction (sigma)
theorem prime_gain {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    (sigma 1 (n*p) : ℝ) / (p * (sigma 1 n : ℝ)) =
      (1 - (p:ℝ)⁻¹ ^ (n.factorization p + 2)) / (1 - (p:ℝ)⁻¹ ^ (n.factorization p + 1)) := by
  let a := n.factorization p
  let d := n / p^a
  have hdpos : 0 < d := Nat.ordCompl_pos p hn
  have hc : Nat.Coprime p d := Nat.coprime_ordCompl hp hn
  have heq : p^a * d = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have heq' : p^(a+1)*d=n*p := by rw [pow_succ, ← heq]; ring
  have sd : sigma 1 n = sigma 1 (p^a) * sigma 1 d := by
    conv_lhs => rw [← heq]
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hc.pow_left _)
  have sp : sigma 1 (n*p) = sigma 1 (p^(a+1)) * sigma 1 d := by
    rw [← heq']
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hc.pow_left _)
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have ds : (sigma 1 d:ℝ) ≠ 0 := by exact_mod_cast (ArithmeticFunction.sigma_pos 1 d hdpos.ne').ne'
  have closed (e : ℕ) : (sigma 1 (p^e):ℝ) = ((p:ℝ)^(e+1)-1)/(p-1) := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
    push_cast
    exact geom_sum_eq hp1.ne' _
  have ht : (p:ℝ)^(a+1)-1 ≠ 0 := ne_of_gt (sub_pos.mpr (one_lt_pow₀ hp1 (by omega)))
  change _ = (1-(p:ℝ)⁻¹^(a+2))/(1-(p:ℝ)⁻¹^(a+1))
  rw [sp,sd,Nat.cast_mul,Nat.cast_mul,closed,closed,inv_pow,inv_pow]
  have hp_sub : (p:ℝ)-1 ≠ 0 := by linarith
  field_simp [hp0.ne',hp_sub,ds,ht]
  ring
end RobinProfile

namespace RobinProfile
open ArithmeticFunction (sigma)
theorem record_shape_of_gain
    (gain : ∀ {p q : ℝ}, 1 < p → p ≤ q → ∀ {j k : ℕ}, 0 < j → j ≤ k →
      (1 - q⁻¹^(k+1))/(1 - q⁻¹^k) ≤ (1 - p⁻¹^(j+1))/(1 - p⁻¹^j))
    (n : ℕ) (hn : 0 < n) (rec : ∀ m : ℕ, 0 < m → m < n → sigma 1 m*n < sigma 1 n*m) :
    ∀ p q : ℕ, p.Prime → q.Prime → p < q → n.factorization q ≤ n.factorization p := by
  intro p q hp hq hpq
  by_contra! h
  obtain ⟨v,hv⟩ := Nat.dvd_of_factorization_pos (show n.factorization q ≠ 0 by omega)
  have nv : n=v*q := by simpa [Nat.mul_comm] using hv
  have vp : 0 < v := Nat.pos_of_mul_pos_right (nv ▸ hn)
  have hfp : n.factorization p=v.factorization p := by
    rw [nv,Nat.factorization_mul vp.ne' hq.ne_zero,Finsupp.add_apply,hq.factorization]
    simp [Ne.symm hpq.ne]
  have hfq : n.factorization q=v.factorization q+1 := by
    rw [nv,Nat.factorization_mul vp.ne' hq.ne_zero,Finsupp.add_apply,hq.factorization_self]
  rw [hfp,hfq] at h
  have comp := gain (by exact_mod_cast hp.one_lt : (1:ℝ) < p)
    (by exact_mod_cast hpq.le : (p:ℝ) ≤ q) (show 0 < v.factorization p+1 by omega)
    (show v.factorization p+1 ≤ v.factorization q+1 by omega)
  rw [← prime_gain hq vp.ne', ← prime_gain hp vp.ne'] at comp
  have small : v*p < n := by rw [nv]; exact Nat.mul_lt_mul_of_pos_left hpq vp
  have win := rec (v*p) (Nat.mul_pos vp hp.pos) small
  rw [nv] at win
  have strict : sigma 1 (v*p)*q < sigma 1 (v*q)*p := by
    apply Nat.lt_of_mul_lt_mul_right (a:=v)
    simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using win
  have sp : (0:ℝ) < sigma 1 v := by exact_mod_cast ArithmeticFunction.sigma_pos 1 v vp.ne'
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq.pos
  have hc := (div_le_div_iff₀ (mul_pos hq0 sp) (mul_pos hp0 sp)).mp comp
  rw [← mul_assoc,← mul_assoc] at hc
  have near := le_of_mul_le_mul_right hc sp
  exact (not_lt_of_ge near) (by exact_mod_cast strict)
end RobinProfile

open ArithmeticFunction (sigma)
theorem RobinProfile.record_shape (n : ℕ) (hn : 0 < n)
    (rec : ∀ m : ℕ, 0 < m → m < n → sigma 1 m*n < sigma 1 n*m) :
    ∀ p q : ℕ, p.Prime → q.Prime → p < q → n.factorization q ≤ n.factorization p :=
  record_shape_of_gain (@RobinRecord.gain_mono) n hn rec

namespace OMA.R_RiemannHypothesis_robin_criterion_R2
open Finset Real
open scoped ArithmeticFunction.sigma

/-- There is a strict abundancy record past 5040 and every integer between
5040 and this record satisfies Robin's inequality. The next record is 10080. -/
def H1 : Prop := ∃ s : ℕ, 5040 < s ∧
    (∀ m : ℕ, 0 < m → m < s → σ 1 m * s < σ 1 s * m) ∧
    ∀ n : ℕ, 5040 < n → n < s → σ 1 n < exp eulerMascheroniConstant * n * log (log n)

/-- Robin's criterion restricted to strict abundancy records with decreasing
prime exponents. The exponent condition includes primes absent from n. -/
def H2 : Prop := RiemannHypothesis ↔
    ∀ n : ℕ, 5040 < n →
      (∀ m : ℕ, 0 < m → m < n → σ 1 m * n < σ 1 n * m) →
      (∀ p q : ℕ, p.Prime → q.Prime → p < q → n.factorization q ≤ n.factorization p) →
      σ 1 n < exp eulerMascheroniConstant * n * log (log n)

/-- The least maximizer on a positive initial segment is a strict record. -/
theorem prefix_record (f : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ r : ℕ, 0 < r ∧ r ≤ n ∧
      (∀ m : ℕ, 0 < m → m < r → f m < f r) ∧
      ∀ m : ℕ, 0 < m → m ≤ n → f m ≤ f r := by
  classical
  let I := Icc 1 n
  obtain ⟨u,hu,highest⟩ := exists_max_image I f ⟨n,mem_Icc.mpr ⟨hn,le_rfl⟩⟩
  let W := I.filter (fun k => f k = f u)
  obtain ⟨r,hr,first⟩ := exists_min_image W id ⟨u,mem_filter.mpr ⟨hu,rfl⟩⟩
  obtain ⟨hin,eq⟩ := mem_filter.mp hr
  obtain ⟨rpos,rle⟩ := mem_Icc.mp hin
  refine ⟨r,rpos,rle,?_,?_⟩
  · intro m mpos ml
    have hm : m ∈ I := mem_Icc.mpr ⟨mpos,ml.le.trans rle⟩
    apply lt_of_le_of_ne ((highest m hm).trans_eq eq.symm)
    intro bad
    exact (Nat.not_le_of_gt ml) (first m (mem_filter.mpr ⟨hm,bad.trans eq⟩))
  · intro m mpos ml
    exact (highest m (mem_Icc.mpr ⟨mpos,ml⟩)).trans_eq eq.symm

theorem main : H1 → H2 → type_of% @RiemannHypothesis.robin_criterion := by
  rintro ⟨s,hs,early,initial⟩ sparse
  constructor
  · intro rh n hn
    by_cases hns : n < s
    · exact initial n hn hns
    let f (k : ℕ) : ℝ := (σ 1 k : ℝ) / k
    obtain ⟨r,rpos,rle,record,maximum⟩ := prefix_record f (by omega : 0 < n)
    have rP : (0:ℝ) < r := by exact_mod_cast rpos
    have sP : (0:ℝ) < s := by exact_mod_cast (by omega : 0<s)
    have nP : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
    have rbig : 5040 < r := by
      by_contra! small
      have hist := early r rpos (by omega)
      have worse : f r < f s := (div_lt_div_iff₀ rP sP).mpr (by exact_mod_cast hist)
      exact (not_lt_of_ge (maximum s (by omega) (by omega))) worse
    have rrec (m : ℕ) (hm : 0 < m) (hlt : m < r) : σ 1 m * r < σ 1 r * m := by
      have mP : (0:ℝ) < m := by exact_mod_cast hm
      exact_mod_cast (div_lt_div_iff₀ mP rP).mp (record m hm hlt)
    have hRobin := sparse.mp rh r rbig rrec (RobinProfile.record_shape r rpos rrec)
    have normalized : f r < exp eulerMascheroniConstant * log (log r) := by
      apply (div_lt_iff₀ rP).mpr
      simpa only [mul_right_comm _ (log (log r))] using hRobin
    have logmono : log (log r) ≤ log (log n) :=
      log_le_log (log_pos (by exact_mod_cast (by omega : 1 < r)))
        (log_le_log rP (by exact_mod_cast rle))
    have final : f n < exp eulerMascheroniConstant * log (log n) :=
      ((maximum n (by omega) le_rfl).trans_lt normalized).trans_le
        (mul_le_mul_of_nonneg_left logmono (exp_pos _).le)
    simpa only [mul_right_comm _ (log (log n))] using (div_lt_iff₀ nP).mp final
  · intro universal
    exact sparse.mpr (fun n hn _ _ => universal n hn)

end OMA.R_RiemannHypothesis_robin_criterion_R2
