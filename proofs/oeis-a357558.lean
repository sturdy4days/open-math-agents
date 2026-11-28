import OMAStatements.S_oeis_a357558

/-!
# The supercongruence for OEIS A357558

We prove Peter Bala's conjecture by expanding the signed binomial summand modulo the fourth
power of the prime. The linear and quadratic reciprocal sums cancel the surviving terms.
The remaining factor follows from the elementary identity for a binomial coefficient times
its lower index.
-/

open scoped BigOperators

namespace A357558Product

variable {R : Type*} [CommRing R]

theorem mul_prod_quadratic {ι : Type*} (s : Finset ι) (M p : R)
    (x y : ι → R) (h : M * p ^ 2 = 0) :
    M * (∏ i ∈ s, (1 + p * x i + p ^ 2 * y i)) =
      M * (1 + p * ∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      calc
        _ = (1 + p * x a + p ^ 2 * y a) *
              (M * ∏ i ∈ s, (1 + p * x i + p ^ 2 * y i)) := by ring
        _ = (1 + p * x a + p ^ 2 * y a) * (M * (1 + p * ∑ i ∈ s, x i)) := by
              rw [ih]
        _ = M * (1 + p * (x a + ∑ i ∈ s, x i)) +
              (y a + (x a + p * y a) * (∑ i ∈ s, x i)) * (M * p ^ 2) := by ring
        _ = _ := by rw [h, mul_zero, add_zero]

theorem mul_prod_sub_mul_add_sq {ι : Type*} (s : Finset ι) (M p : R)
    (x : ι → R) (h : M * p ^ 2 = 0) :
    M * (∏ i ∈ s, (1 - p * x i) * (1 + p * x i) ^ 2) =
      M * (1 + p * ∑ i ∈ s, x i) := by
  calc
    _ = M * (∏ i ∈ s, (1 + p * x i + p ^ 2 * (-(x i ^ 2 * (1 + p * x i))))) := by
      congr 1
      exact Finset.prod_congr rfl fun i _ => by ring
    _ = _ := mul_prod_quadratic s M p x (fun i => -(x i ^ 2 * (1 + p * x i))) h

theorem signed_summand {ι : Type*} (s : Finset ι) (p v : R)
    (x : ι → R) (h : p ^ 4 = 0) :
    p ^ 2 * v * (1 - p * v) * (∏ i ∈ s, (1 - p * x i) * (1 + p * x i) ^ 2) =
      p ^ 2 * v + p ^ 3 * (v * (∑ i ∈ s, x i) - v ^ 2) := by
  have hmul : (p ^ 2 * v) * p ^ 2 = 0 := by
    calc
      _ = v * p ^ 4 := by ring
      _ = 0 := by rw [h, mul_zero]
  calc
    _ = (1 - p * v) * (p ^ 2 * v * (∏ i ∈ s, (1 - p * x i) * (1 + p * x i) ^ 2)) := by ring
    _ = (1 - p * v) * (p ^ 2 * v * (1 + p * ∑ i ∈ s, x i)) := by
      rw [mul_prod_sub_mul_add_sq s (p ^ 2 * v) p x hmul]
    _ = p ^ 2 * v + p ^ 3 * (v * (∑ i ∈ s, x i) - v ^ 2) -
          p ^ 4 * (v ^ 2 * (∑ i ∈ s, x i)) := by ring
    _ = _ := by rw [h, zero_mul, sub_zero]

example (p k : ℕ) :
    let P : ZMod (p ^ 4) := p
    let v : ZMod (p ^ 4) := (k : ZMod (p ^ 4))⁻¹
    let x : ℕ → ZMod (p ^ 4) := fun i => ((i + 1 : ℕ) : ZMod (p ^ 4))⁻¹
    P ^ 2 * v * (1 - P * v) * (∏ i ∈ Finset.range (k - 1), (1 - P * x i) * (1 + P * x i) ^ 2) =
      P ^ 2 * v + P ^ 3 * (v * (∑ i ∈ Finset.range (k - 1), x i) - v ^ 2) := by
  dsimp only
  apply signed_summand
  rw [← Nat.cast_pow]
  exact ZMod.natCast_self (p ^ 4)

end A357558Product


namespace A357558Summand

private theorem inv_small {p t : ℕ} (hp : p.Prime) (ht0 : 0 < t) (htp : t < p) :
    (t : ZMod (p ^ 4)) * (t : ZMod (p ^ 4))⁻¹ = 1 :=
  ZMod.mul_inv_of_unit _ ((ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide)).2
    (Nat.not_dvd_of_pos_of_lt ht0 htp))

private theorem factorial_mul_inv_prod {p k : ℕ} (hp : p.Prime) (hk : k < p) :
    (k.factorial : ZMod (p ^ 4)) *
      (∏ j ∈ Finset.range k, (((j + 1 : ℕ) : ZMod (p ^ 4)))⁻¹) = 1 := by
  rw [Nat.factorial_eq_prod_range_add_one, Nat.cast_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro j hj
  have hjk := Finset.mem_range.mp hj
  exact inv_small hp (by omega) (by omega)

private theorem choose_desc_prod {p k : ℕ} (hp : p.Prime) (hk : k < p) :
    ((p - 1).choose k : ZMod (p ^ 4)) = (-1 : ZMod (p ^ 4)) ^ k *
      ∏ j ∈ Finset.range k, (1 - (p : ZMod (p ^ 4)) * (((j + 1 : ℕ) : ZMod (p ^ 4)))⁻¹) := by
  let invprod := ∏ j ∈ Finset.range k, (((j + 1 : ℕ) : ZMod (p ^ 4)))⁻¹
  calc
    _ = ((k.factorial : ZMod (p ^ 4)) * ((p - 1).choose k : ZMod (p ^ 4))) * invprod := by
      rw [mul_right_comm, factorial_mul_inv_prod hp hk, one_mul]
    _ = ∏ j ∈ Finset.range k,
        ((p - 1 - j : ℕ) : ZMod (p ^ 4)) * (((j + 1 : ℕ) : ZMod (p ^ 4)))⁻¹ := by
      rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose,
        Nat.descFactorial_eq_prod_range, Nat.cast_prod]
      exact (Finset.prod_mul_distrib).symm
    _ = ∏ j ∈ Finset.range k,
        -(1 - (p : ZMod (p ^ 4)) * (((j + 1 : ℕ) : ZMod (p ^ 4)))⁻¹) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hjk := Finset.mem_range.mp hj
      have hcast : ((p - 1 - j : ℕ) : ZMod (p ^ 4)) +
          ((j + 1 : ℕ) : ZMod (p ^ 4)) = p := by
        rw [← Nat.cast_add, show p - 1 - j + (j + 1) = p by omega]
      rw [eq_sub_of_add_eq hcast, sub_mul, inv_small (t := j+1) hp (by omega) (by omega)]
      ring
    _ = _ := by rw [Finset.prod_neg, Finset.card_range]

private theorem choose_asc_prod {p k : ℕ} (hp : p.Prime) (hk : k < p) :
    ((p - 1 + k).choose k : ZMod (p ^ 4)) =
      (∏ j ∈ Finset.range k, ((p : ZMod (p ^ 4)) + (j : ZMod (p ^ 4)))) *
      (∏ j ∈ Finset.range k, (((j + 1 : ℕ) : ZMod (p ^ 4)))⁻¹) := by
  let invprod := ∏ j ∈ Finset.range k, (((j + 1 : ℕ) : ZMod (p ^ 4)))⁻¹
  calc
    _ = ((k.factorial : ZMod (p ^ 4)) * ((p - 1 + k).choose k : ZMod (p ^ 4))) * invprod := by
      rw [mul_right_comm, factorial_mul_inv_prod hp hk, one_mul]
    _ = _ := by
      have h : p - 1 + k = p + k - 1 := by have := hp.pos; omega
      rw [← Nat.cast_mul, h, ← Nat.ascFactorial_eq_factorial_mul_choose',
        Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
      simp [invprod]

private theorem choose_asc_factored {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    ((p - 1 + k).choose k : ZMod (p ^ 4)) =
      (p : ZMod (p ^ 4)) * (k : ZMod (p ^ 4))⁻¹ *
        ∏ j ∈ Finset.range (k - 1), (1 + (p : ZMod (p ^ 4)) * (((j + 1 : ℕ) : ZMod (p ^ 4)))⁻¹) := by
  have hk1 : k - 1 + 1 = k := by omega
  let A := ∏ j ∈ Finset.range (k - 1), ((p : ZMod (p ^ 4)) + ((j + 1 : ℕ) : ZMod (p ^ 4)))
  let B := ∏ j ∈ Finset.range (k - 1), (((j + 1 : ℕ) : ZMod (p ^ 4)))⁻¹
  have hA : (∏ j ∈ Finset.range k, ((p : ZMod (p ^ 4)) + (j : ZMod (p ^ 4)))) = A * p := by
    simpa only [hk1, Nat.cast_zero, add_zero] using
      (Finset.prod_range_succ' (fun j : ℕ => (p : ZMod (p ^ 4)) + (j : ZMod (p ^ 4))) (k - 1))
  have hB : (∏ j ∈ Finset.range k, (((j + 1 : ℕ) : ZMod (p ^ 4)))⁻¹) = B * (k : ZMod (p ^ 4))⁻¹ := by
    simpa only [hk1] using
      (Finset.prod_range_succ (fun j : ℕ => (((j + 1 : ℕ) : ZMod (p ^ 4)))⁻¹) (k - 1))
  rw [choose_asc_prod hp hkp, hA, hB]
  calc
    _ = (p : ZMod (p ^ 4)) * (k : ZMod (p ^ 4))⁻¹ * (A * B) := by ring
    _ = _ := by
      dsimp only [A, B]
      rw [← Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      have hjk := Finset.mem_range.mp hj
      rw [add_mul, inv_small (t := j+1) hp (by omega) (by omega), add_comm]

/-- Factor the signed summand into unit reciprocals and binomial factors modulo `p^4`. -/
theorem summand_exact {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk0 : 0 < k) (hkp : k < p) :
    (-1 : ZMod (p ^ 4)) ^ (p - 1 + k) * (k : ZMod (p ^ 4)) *
      ((p - 1).choose k : ZMod (p ^ 4)) * ((p - 1 + k).choose k : ZMod (p ^ 4)) ^ 2 =
    (p : ZMod (p ^ 4)) ^ 2 * (k : ZMod (p ^ 4))⁻¹ *
      (1 - (p : ZMod (p ^ 4)) * (k : ZMod (p ^ 4))⁻¹) *
      ∏ j ∈ Finset.range (k - 1),
        (1 - (p : ZMod (p ^ 4)) * (((j + 1 : ℕ) : ZMod (p ^ 4)))⁻¹) *
        (1 + (p : ZMod (p ^ 4)) * (((j + 1 : ℕ) : ZMod (p ^ 4)))⁻¹)^2 := by
  let P : ZMod (p ^ 4) := p
  let u : ZMod (p ^ 4) := (k : ZMod (p ^ 4))⁻¹
  let f : ℕ → ZMod (p ^ 4) := fun j => 1 - P * (((j + 1 : ℕ) : ZMod (p ^ 4)))⁻¹
  let g : ℕ → ZMod (p ^ 4) := fun j => 1 + P * (((j + 1 : ℕ) : ZMod (p ^ 4)))⁻¹
  have hk1 : k - 1 + 1 = k := by omega
  have hfade : Even (p - 1) := hp.even_sub_one (by omega)
  have hsign : (-1 : ZMod (p ^ 4)) ^ (p - 1 + k) * (-1 : ZMod (p ^ 4)) ^ k = 1 := by
    rw [pow_add, hfade.neg_one_pow, one_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hprod : (∏ j ∈ Finset.range k, f j) = (∏ j ∈ Finset.range (k - 1), f j) * (1 - P * u) := by
    simpa only [hk1, f, u] using (Finset.prod_range_succ f (k - 1))
  have hpair : (∏ j ∈ Finset.range (k - 1), f j) * (∏ j ∈ Finset.range (k - 1), g j)^2 =
      ∏ j ∈ Finset.range (k - 1), f j * (g j)^2 := by
    rw [pow_two, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    ring
  change _ = P^2 * u * (1 - P*u) * ∏ j ∈ Finset.range (k - 1), f j * (g j)^2
  rw [choose_desc_prod hp hkp, choose_asc_factored hp hk0 hkp]
  change (-1 : ZMod (p ^ 4)) ^ (p - 1 + k) * (k : ZMod (p ^ 4)) *
      ((-1 : ZMod (p ^ 4)) ^ k * ∏ j ∈ Finset.range k, f j) *
      (P * u * ∏ j ∈ Finset.range (k - 1), g j)^2 = _
  rw [hprod]
  calc
    _ = ((-1 : ZMod (p ^ 4)) ^ (p - 1 + k) * (-1 : ZMod (p ^ 4)) ^ k) *
          ((k : ZMod (p ^ 4)) * u) * (P^2 * u * (1 - P * u)) *
          ((∏ j ∈ Finset.range (k - 1), f j) * (∏ j ∈ Finset.range (k - 1), g j)^2) := by ring
    _ = _ := by rw [hsign, show (k : ZMod (p ^ 4)) * u = 1 from inv_small hp hk0 hkp,
      hpair, one_mul, one_mul]

end A357558Summand

namespace A357558Combine

theorem coprime_pred_pow (p : ℕ) (h : 1 ≤ p) :
    IsCoprime ((p - 1 : ℕ) : ℤ) ((p ^ 4 : ℕ) : ℤ) := by
  push_cast
  apply IsCoprime.pow_right
  refine ⟨-1, 1, ?_⟩
  rw [Nat.cast_sub h]
  push_cast
  ring

end A357558Combine

namespace A357558Combine

private theorem shift_sum {R : Type*} [AddCommMonoid R] (k : ℕ) (f : ℕ → R) :
    (∑ i ∈ Finset.range (k - 1), f (i + 1)) = ∑ j ∈ Finset.Ioo 0 k, f j := by
  refine Finset.sum_bij' (fun i _ => i + 1) (fun j _ => j - 1) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    have h := Finset.mem_range.mp hi
    exact Finset.mem_Ioo.mpr ⟨by omega, by omega⟩
  · intro j hj
    have h := Finset.mem_Ioo.mp hj
    exact Finset.mem_range.mpr (by omega)
  · intro i _
    omega
  · intro j hj
    have h := Finset.mem_Ioo.mp hj
    omega
  · intro i _
    rfl

/-- The summand through degree three in the prime, computed modulo its fourth power. -/
theorem summand_expanded {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk0 : 0 < k) (hkp : k < p) :
    (-1 : ZMod (p ^ 4)) ^ (p - 1 + k) * (k : ZMod (p ^ 4)) *
        ((p - 1).choose k : ZMod (p ^ 4)) * ((p - 1 + k).choose k : ZMod (p ^ 4)) ^ 2 =
      (p : ZMod (p ^ 4)) ^ 2 * (k : ZMod (p ^ 4))⁻¹ +
        (p : ZMod (p ^ 4)) ^ 3 *
          ((k : ZMod (p ^ 4))⁻¹ * (∑ j ∈ Finset.Ioo 0 k, (j : ZMod (p ^ 4))⁻¹) -
           ((k : ZMod (p ^ 4))⁻¹) ^ 2) := by
  have nilp : (p : ZMod (p ^ 4)) ^ 4 = 0 := by
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self (p ^ 4)
  rw [A357558Summand.summand_exact hp hp5 hk0 hkp, A357558Product.signed_summand _ _ _ _ nilp]
  rw [shift_sum k (fun i => (i : ZMod (p ^ 4))⁻¹)]

end A357558Combine

namespace A357558Harmonic

open Finset

theorem natCast_isUnit_of_mem_Ioo {p k r : ℕ} (hp : p.Prime) (hr : 0 < r)
    (hk : k ∈ Ioo 0 p) : IsUnit (k : ZMod (p ^ r)) := by
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp hr]
  exact Nat.not_dvd_of_pos_of_lt (mem_Ioo.mp hk).1 (mem_Ioo.mp hk).2

theorem castHom_inv_of_isUnit {m n : ℕ} (hmn : m ∣ n) (x : ZMod n) (hx : IsUnit x) :
    (ZMod.castHom hmn (ZMod m)) x⁻¹ = ((ZMod.castHom hmn (ZMod m)) x)⁻¹ := by
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  rw [← map_mul, ZMod.mul_inv_of_unit x hx, map_one]

theorem mul_pow_eq_zero_of_castHom_eq_zero {p r s : ℕ} (hp : 0 < p) (hrs : s ≤ r)
    (x : ZMod (p ^ r))
    (hx : ZMod.castHom (pow_dvd_pow p hrs) (ZMod (p ^ s)) x = 0) :
    (p : ZMod (p ^ r)) ^ (r - s) * x = 0 := by
  let : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne'⟩
  have hval : (x.val : ZMod (p ^ s)) = 0 := by
    rw [← map_natCast (ZMod.castHom (pow_dvd_pow p hrs) (ZMod (p ^ s))) x.val,
      ZMod.natCast_zmod_val]
    exact hx
  obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff x.val (p ^ s)).mp hval
  rw [← ZMod.natCast_zmod_val x, ht, Nat.cast_mul, Nat.cast_pow, ← mul_assoc,
    ← pow_add, Nat.sub_add_cancel hrs, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

theorem sum_inv_sq_Ioo_zmod {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ k ∈ Ioo 0 p, ((k : ZMod p)⁻¹) ^ 2) = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hbij :
      (∑ k ∈ Ioo 0 p, ((k : ZMod p)⁻¹) ^ 2) =
        ∑ x ∈ (univ.erase (0 : ZMod p)), x⁻¹ ^ 2 := by
    refine Finset.sum_bij' (fun k _ => (k : ZMod p)) (fun x _ => x.val) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact mt (ZMod.natCast_eq_zero_iff k p).mp
        (Nat.not_dvd_of_pos_of_lt (mem_Ioo.mp hk).1 (mem_Ioo.mp hk).2)
    · intro x hx
      exact mem_Ioo.mpr ⟨ZMod.val_pos.mpr (Finset.mem_erase.mp hx).1, ZMod.val_lt x⟩
    · intro k hk
      exact ZMod.val_cast_of_lt (mem_Ioo.mp hk).2
    · intro x _
      exact ZMod.natCast_zmod_val x
    · intros
      rfl
  have hzero : ((0 : ZMod p)⁻¹) ^ 2 = 0 := by simp
  have herase : (∑ x ∈ univ.erase (0 : ZMod p), x⁻¹ ^ 2) = ∑ x : ZMod p, x⁻¹ ^ 2 := by
    have h := Finset.sum_erase_add univ (fun x : ZMod p => x⁻¹ ^ 2)
      (Finset.mem_univ (0 : ZMod p))
    simpa only [hzero, add_zero] using h
  have hinv :
      (∑ x : ZMod p, x⁻¹ ^ 2) = ∑ x : ZMod p, x ^ 2 := by
    let e : ZMod p ≃ ZMod p := ⟨(·⁻¹), (·⁻¹), inv_inv, inv_inv⟩
    change (∑ x : ZMod p, (e x) ^ 2) = _
    exact e.sum_comp (fun x : ZMod p => x ^ 2)
  rw [hbij, herase, hinv]
  refine FiniteField.sum_pow_lt_card_sub_one (ZMod p) 2 ?_
  rw [ZMod.card]
  omega

theorem natCast_mul_eq_zero_of_castHom_eq_zero {m n d : ℕ} (hn : n ≠ 0)
    (hmn : m ∣ n) (hprod : d * m = n) (x : ZMod n)
    (hx : ZMod.castHom hmn (ZMod m) x = 0) : (d : ZMod n) * x = 0 := by
  let : NeZero n := ⟨hn⟩
  have hval : (x.val : ZMod m) = 0 := by
    rw [← map_natCast (ZMod.castHom hmn (ZMod m)) x.val, ZMod.natCast_zmod_val]
    exact hx
  obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff x.val m).mp hval
  rw [← ZMod.natCast_zmod_val x, ht, Nat.cast_mul, ← mul_assoc,
    ← Nat.cast_mul, hprod, ZMod.natCast_self, zero_mul]

private theorem sum_reflect_Ioo {R : Type*} [AddCommMonoid R] (p : ℕ) (g : ℕ → R) :
    (∑ k ∈ Ioo 0 p, g k) = ∑ k ∈ Ioo 0 p, g (p - k) := by
  have hmem (k : ℕ) (hk : k ∈ Ioo 0 p) : p - k ∈ Ioo 0 p := by
    rw [mem_Ioo] at hk ⊢
    omega
  have hreflect (k : ℕ) (hk : k ∈ Ioo 0 p) : p - (p - k) = k := by
    have := (mem_Ioo.mp hk).2
    omega
  refine Finset.sum_bij' (fun k _ => p - k) (fun k _ => p - k) hmem hmem hreflect hreflect ?_
  intro k hk
  rw [hreflect k hk]

theorem sum_inv_Ioo_zmod_sq {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ k ∈ Ioo 0 p, (k : ZMod (p ^ 2))⁻¹) = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  let R := ZMod (p ^ 2)
  have hdiv : p ∣ p ^ 2 := dvd_pow_self p (by decide)
  let f : R →+* ZMod p := ZMod.castHom hdiv (ZMod p)
  let H : R := ∑ k ∈ Ioo 0 p, (k : R)⁻¹
  let T : R := ∑ k ∈ Ioo 0 p, (k : R)⁻¹ * ((p - k : ℕ) : R)⁻¹
  have hmem (k : ℕ) (hk : k ∈ Ioo 0 p) : p - k ∈ Ioo 0 p := by
    rw [mem_Ioo] at hk ⊢
    omega
  have hT : f T = 0 := by
    dsimp only [T]
    rw [map_sum]
    calc
      _ = -(∑ k ∈ Ioo 0 p, ((k : ZMod p)⁻¹) ^ 2) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        have hleft := natCast_isUnit_of_mem_Ioo hp (by decide : 0 < (2 : ℕ)) hk
        have hright := natCast_isUnit_of_mem_Ioo hp (by decide : 0 < (2 : ℕ)) (hmem k hk)
        have hcastK : f (k : R) = (k : ZMod p) := map_natCast f k
        have hcastR : f ((p - k : ℕ) : R) = -(k : ZMod p) := by
          rw [map_natCast, Nat.cast_sub (mem_Ioo.mp hk).2.le, ZMod.natCast_self, zero_sub]
        rw [map_mul, castHom_inv_of_isUnit hdiv _ hleft,
          castHom_inv_of_isUnit hdiv _ hright]
        change (f (k : R))⁻¹ * (f ((p - k : ℕ) : R))⁻¹ = _
        rw [hcastK, hcastR, inv_neg, mul_neg, pow_two]
      _ = 0 := by rw [sum_inv_sq_Ioo_zmod hp hp5, neg_zero]
  have hkillT : (p : R) * T = 0 :=
    natCast_mul_eq_zero_of_castHom_eq_zero (pow_ne_zero _ hp.ne_zero) hdiv (pow_two p).symm T hT
  have hdouble : H + H = (p : R) * T := by
    calc
      H + H = H + (∑ k ∈ Ioo 0 p, ((p - k : ℕ) : R)⁻¹) :=
        congrArg (H + ·) (sum_reflect_Ioo p (fun k => (k : R)⁻¹))
      _ = ∑ k ∈ Ioo 0 p, ((k : R)⁻¹ + ((p - k : ℕ) : R)⁻¹) := (Finset.sum_add_distrib).symm
      _ = (p : R) * T := by
        dsimp only [T]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := (mem_Ioo.mp hk).2
        have hc : (k : R) + ((p - k : ℕ) : R) = (p : R) := by
          rw [← Nat.cast_add, Nat.add_sub_of_le hk'.le]
        have ha := ZMod.mul_inv_of_unit (k : R)
          (natCast_isUnit_of_mem_Ioo hp (by decide : 0 < (2 : ℕ)) hk)
        have hb := ZMod.mul_inv_of_unit ((p - k : ℕ) : R)
          (natCast_isUnit_of_mem_Ioo hp (by decide : 0 < (2 : ℕ)) (hmem k hk))
        rw [← hc]
        linear_combination -(((p - k : ℕ) : R)⁻¹) * ha - ((k : R)⁻¹) * hb
  apply (ZMod.add_self_eq_zero_iff_eq_zero (hp.odd_of_ne_two (by omega)).pow).mp
  exact hdouble.trans hkillT

theorem castHom_natCast_inv_of_mem_Ioo {p k r m : ℕ} (hp : p.Prime) (hr : 0 < r)
    (hmn : m ∣ p ^ r) (hk : k ∈ Ioo 0 p) :
    ZMod.castHom hmn (ZMod m) ((k : ZMod (p ^ r))⁻¹) = (k : ZMod m)⁻¹ := by
  rw [castHom_inv_of_isUnit hmn _ (natCast_isUnit_of_mem_Ioo hp hr hk), map_natCast]

theorem pow_sq_mul_sum_inv_Ioo_zmod_four {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ZMod (p ^ 4)) ^ 2 * (∑ k ∈ Ioo 0 p, (k : ZMod (p ^ 4))⁻¹) = 0 := by
  refine mul_pow_eq_zero_of_castHom_eq_zero (r := 4) (s := 2) hp.pos (by decide) _ ?_
  rw [map_sum]
  calc
    _ = ∑ k ∈ Ioo 0 p, (k : ZMod (p ^ 2))⁻¹ :=
      Finset.sum_congr rfl (fun _ hk =>
        castHom_natCast_inv_of_mem_Ioo hp (by decide) _ hk)
    _ = 0 := sum_inv_Ioo_zmod_sq hp hp5

theorem pow_cube_mul_sum_inv_sq_Ioo_zmod_four {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ZMod (p ^ 4)) ^ 3 * (∑ k ∈ Ioo 0 p, ((k : ZMod (p ^ 4))⁻¹) ^ 2) = 0 := by
  rw [← Nat.cast_pow]
  refine natCast_mul_eq_zero_of_castHom_eq_zero (m := p) (d := p ^ 3)
    (pow_ne_zero _ hp.ne_zero) (dvd_pow_self p (by decide : (4 : ℕ) ≠ 0)) (pow_succ p 3).symm _ ?_
  rw [map_sum]
  calc
    _ = ∑ k ∈ Ioo 0 p, ((k : ZMod p)⁻¹) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [map_pow, castHom_natCast_inv_of_mem_Ioo hp (by decide) _ hk]
    _ = 0 := sum_inv_sq_Ioo_zmod hp hp5

end A357558Harmonic


namespace A357558Complete

open Finset
open OMA.S_oeis_a357558 (a)

theorem nat_dvd_a (n : ℕ) : (n : ℤ) ∣ a n := by
  cases n with
  | zero => simp [a]
  | succ n =>
    unfold a
    apply Finset.dvd_sum
    intro k _
    cases k with
    | zero => simp
    | succ k =>
      have h :
          (↑(k + 1) : ℤ) * ↑((n + 1).choose (k + 1)) =
            ↑(n + 1) * ↑(n.choose k) := by
        exact_mod_cast (by simpa [mul_comm] using (Nat.add_one_mul_choose_eq n k).symm :
          (k + 1) * (n + 1).choose (k + 1) = (n + 1) * n.choose k)
      refine ⟨(-1 : ℤ) ^ (n + 1 + (k + 1)) * ↑(n.choose k) *
          (↑((n + 1 + (k + 1)).choose (k + 1)) : ℤ) ^ 2, ?_⟩
      rw [mul_assoc ((-1 : ℤ) ^ _) (↑(k + 1) : ℤ), h]
      ring

private theorem twice_prefix {R : Type*} [CommRing R] (f : ℕ → R) (n : ℕ) :
    2 * (∑ k ∈ Ioo 0 n, f k * ∑ j ∈ Ioo 0 k, f j) =
      (∑ k ∈ Ioo 0 n, f k) ^ 2 - ∑ k ∈ Ioo 0 n, (f k) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      have hempty : Ioo 0 1 = (∅ : Finset ℕ) := by ext k; simp only [mem_Ioo, notMem_empty, iff_false]; omega
      simp [hempty]
    have hins : Ioo 0 (n + 1) = insert n (Ioo 0 n) := by
      ext k
      simp only [mem_Ioo, mem_insert]
      omega
    have hnot : n ∉ Ioo 0 n := by simp
    rw [hins]
    simp only [sum_insert hnot]
    linear_combination ih

private theorem sum_doubled {R : Type*} [CommRing R] (f : ℕ → R) (p : ℕ) (P : R)
    (hlinear : P ^ 2 * (∑ k ∈ Ioo 0 p, f k) = 0)
    (hquadratic : P ^ 3 * (∑ k ∈ Ioo 0 p, (f k) ^ 2) = 0) :
    2 * (∑ k ∈ Ioo 0 p,
      (P ^ 2 * f k + P ^ 3 * (f k * (∑ j ∈ Ioo 0 k, f j) - (f k) ^ 2))) = 0 := by
  have hH2 : P ^ 3 * (∑ k ∈ Ioo 0 p, f k) ^ 2 = 0 := by
    calc
      _ = (P ^ 2 * (∑ k ∈ Ioo 0 p, f k)) * (P * (∑ k ∈ Ioo 0 p, f k)) := by ring
      _ = 0 := by rw [hlinear, zero_mul]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
  linear_combination P ^ 3 * twice_prefix f p + 2 * hlinear + hH2 - 3 * hquadratic

theorem cast_a_zero_of_expansion (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (summand : ∀ k ∈ Ioo 0 p,
      ((-1 : ℤ) ^ (p - 1 + k) * (k : ℤ) * ((p - 1).choose k : ℤ) *
        (((p - 1 + k).choose k : ℕ) : ℤ) ^ 2 : ZMod (p ^ 4)) =
          (p : ZMod (p ^ 4)) ^ 2 * (k : ZMod (p ^ 4))⁻¹ +
          (p : ZMod (p ^ 4)) ^ 3 * ((k : ZMod (p ^ 4))⁻¹ *
            (∑ j ∈ Ioo 0 k, (j : ZMod (p ^ 4))⁻¹) - ((k : ZMod (p ^ 4))⁻¹) ^ 2))
    (hlinear : (p : ZMod (p ^ 4)) ^ 2 * (∑ k ∈ Ioo 0 p, (k : ZMod (p ^ 4))⁻¹) = 0)
    (hquadratic : (p : ZMod (p ^ 4)) ^ 3 *
      (∑ k ∈ Ioo 0 p, ((k : ZMod (p ^ 4))⁻¹) ^ 2) = 0) :
    (a (p - 1) : ZMod (p ^ 4)) = 0 := by
  have h2 : IsUnit (2 : ZMod (p ^ 4)) := by
    change IsUnit ((2 : ℕ) : ZMod (p ^ 4))
    apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide)).2
    intro h
    have := Nat.le_of_dvd (by decide : 0 < 2) h
    omega
  apply h2.mul_right_inj.mp
  rw [mul_zero]
  have hrange : range p = insert 0 (Ioo 0 p) := by
    ext k
    simp only [mem_range, mem_insert, mem_Ioo]
    omega
  unfold a
  rw [Int.cast_sum, show p - 1 + 1 = p by omega, hrange, sum_insert (by simp)]
  simp only [Nat.cast_zero, mul_zero, zero_mul, Int.cast_zero, zero_add, Int.cast_mul, Int.cast_pow]
  rw [sum_congr rfl summand]
  exact sum_doubled (fun k => (k : ZMod (p ^ 4))⁻¹) p (p : ZMod (p ^ 4))
    hlinear hquadratic

end A357558Complete


open OMA.S_oeis_a357558 (a)

theorem OMA.solution : type_of% @OMA.S_oeis_a357558.main := by
  intro p hp hp5
  have ha := A357558Complete.cast_a_zero_of_expansion p hp hp5
    (fun k hk => by
      obtain ⟨hk0, hkp⟩ := Finset.mem_Ioo.mp hk
      simpa using A357558Combine.summand_expanded hp hp5 hk0 hkp)
    (A357558Harmonic.pow_sq_mul_sum_inv_Ioo_zmod_four hp hp5)
    (A357558Harmonic.pow_cube_mul_sum_inv_sq_Ioo_zmod_four hp hp5)
  have hdvdPow := (ZMod.intCast_zmod_eq_zero_iff_dvd (a (p - 1)) (p ^ 4)).mp ha
  have hdvdPred := A357558Complete.nat_dvd_a (p - 1)
  have hcop := A357558Combine.coprime_pred_pow p (by omega)
  simpa only [Nat.cast_mul] using hcop.mul_dvd hdvdPred hdvdPow
