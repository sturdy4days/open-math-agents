import OMAStatements.S_mo_345716

/-!
# Hyperplanes containing quadratic level sets over prime fields

Wenbo Sun posed the zero-set question on MathOverflow, question 345716.
Fedor Petrov's comment 865175 supplies the coordinate sign-change argument.
Statement PR #21333 by @etaubman records the exceptional anisotropic binary
quadratic form in odd characteristic. Here we classify the possible levels,
including characteristic two, for every prime and every dimension at least two.
-/

open MvPolynomial OMA.S_mo_345716

namespace AnisotropicPlane

theorem zero_iff {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) (x y : ZMod p) :
    x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have squares : x ^ 2 = -(y ^ 2) := eq_neg_of_add_eq_zero_left h
    exact ⟨by_contra fun hx => ZMod.mod_four_ne_three_of_sq_eq_neg_sq hx squares hp,
      by_contra fun hy => ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hy squares hp⟩
  · rintro ⟨rfl, rfl⟩
    simp

end AnisotropicPlane

namespace PlaneClassification

/-- A permutation-invariant sphere containing a nonzero point has full affine span
in characteristic different from two. Reflecting one coordinate detects its coefficient. -/
theorem reflection {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {d : ℕ}
    (x a : Fin d → K) (b : K) {j : Fin d} (hj : x j ≠ 0)
    (vanish : ∀ z : Fin d → K, (∑ k, z k ^ 2) = ∑ k, x k ^ 2 →
      (∑ k, a k * z k) + b = 0) :
    (∀ i, a i = 0) ∧ b = 0 := by
  classical
  have coeff (i : Fin d) : a i = 0 := by
    let e := Equiv.swap i j
    let z := x ∘ e
    have hs : (∑ k, z k ^ 2) = ∑ k, x k ^ 2 := Equiv.sum_comp e (fun k => x k ^ 2)
    have hz : z i ≠ 0 := by simpa [z, e] using hj
    let w := Function.update z i (-z i)
    have same (k : Fin d) : w k ^ 2 = z k ^ 2 := by
      by_cases hk : k = i
      · subst k
        simp [w]
      · simp [w, Function.update_of_ne hk]
    have hw := vanish w ((Finset.sum_congr rfl (fun k _ => same k)).trans hs)
    have hv := vanish z hs
    have rest : (∑ k ∈ Finset.univ.erase i, a k * w k) =
        ∑ k ∈ Finset.univ.erase i, a k * z k := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [w, Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), rest] at hw
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hv
    have reflected : w i = -z i := Function.update_self .. 
    rw [reflected] at hw
    have h : 2 * a i * z i = 0 := by linear_combination hv - hw
    exact (mul_eq_zero.mp (mul_eq_zero.mp h |>.resolve_right hz)).resolve_left h2
  exact ⟨coeff, by simpa [coeff] using (vanish x rfl)⟩

end PlaneClassification

namespace PlaneClassification

/-- All levels in dimension at least three contain a nonzero point. In dimension
two the zero level also does when minus one is a square. -/
theorem nonzero_point {p d : ℕ} [Fact p.Prime] (hd : 2 ≤ d) (c : ZMod p)
    (h : c ≠ 0 ∨ 3 ≤ d ∨ p % 4 ≠ 3) :
    ∃ x : Fin d → ZMod p, (∑ i, x i ^ 2) = c ∧ ∃ i, x i ≠ 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  cases k with
  | zero =>
    change ∃ x : Fin 2 → ZMod p, (∑ i, x i ^ 2) = c ∧ ∃ i, x i ≠ 0
    by_cases hc : c = 0
    · have hp : p % 4 ≠ 3 := by
        rcases h with nonzero | large | split
        · exact (nonzero hc).elim
        · omega
        · exact split
      obtain ⟨a, ha⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 hp
      refine ⟨![1, a], ?_, 0, by simp⟩
      simp [Fin.sum_univ_two, hc, pow_two, ← ha]
    · obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p c
      refine ⟨![a, b], by simpa [Fin.sum_univ_two] using hab, ?_⟩
      by_cases ha : a = 0
      · refine ⟨1, ?_⟩
        simpa using (show b ≠ 0 from fun hb => hc (by simpa [ha, hb] using hab.symm))
      · exact ⟨0, by simpa using ha⟩
  | succ k =>
    rw [Nat.add_comm]
    obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (c - 1)
    let x : Fin (k + 3) → ZMod p :=
      Fin.cons 1 (Fin.cons a (Fin.cons b (fun _ : Fin k => 0)))
    refine ⟨x, ?_, 0, by simp [x]⟩
    calc
      (∑ i, x i ^ 2) = 1 + (a ^ 2 + b ^ 2) := by simp [x, Fin.sum_univ_succ]
      _ = c := by rw [hab]; ring

end PlaneClassification

namespace PlaneClassification

/-- For all primes and every level c, classify the quadrics contained in a
proper affine hyperplane over the base field. -/
theorem fixed_level {p d : ℕ} [hp : Fact p.Prime] (hd : 2 ≤ d) (c : ZMod p) :
    (∃ (a : Fin d → ZMod p) (b : ZMod p), (∃ i, a i ≠ 0) ∧
      ∀ x : Fin d → ZMod p, eval x (quadratic p d c) = 0 →
        eval x (linear p d a b) = 0) ↔
    p = 2 ∨ (d = 2 ∧ c = 0 ∧ p % 4 = 3) := by
  classical
  have i : Fin d := ⟨0, by omega⟩
  constructor
  · rintro ⟨a, b, ⟨k, hk⟩, hf⟩
    by_cases two : p = 2
    · exact Or.inl two
    right
    by_contra! bad
    have ht : (2 : ZMod p) ≠ 0 := by
      intro zero
      have dvd := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast zero)
      have lower := hp.out.two_le
      have upper := Nat.le_of_dvd (by decide : 0 < 2) dvd
      omega
    have alternatives : c ≠ 0 ∨ 3 ≤ d ∨ p % 4 ≠ 3 := by
      by_cases hc : c = 0
      · by_cases hd' : d = 2
        · exact Or.inr (Or.inr (bad hd' hc))
        · exact Or.inr (Or.inl (by omega))
      · exact Or.inl hc
    obtain ⟨x, hsum, j, hj⟩ := nonzero_point hd c alternatives
    apply hk
    apply (reflection ht x a b hj ?_).1
    intro z hz
    have hq : eval z (quadratic p d c) = 0 := by simp [quadratic, hz, hsum]
    simpa [linear] using hf z hq
  · rintro (rfl | ⟨rfl, rfl, hmod⟩)
    · refine ⟨fun _ => 1, -c, ⟨i, one_ne_zero⟩, ?_⟩
      intro x hx
      have sq (z : ZMod 2) : z ^ 2 = z := by simp
      have sum_eq : (∑ j, x j) = c := sub_eq_zero.mp (by simpa [quadratic, sq] using hx)
      simp only [linear, map_add, map_sum, map_mul, eval_C, eval_X, one_mul, sum_eq, add_neg_cancel]
    · refine ⟨![1, 0], 0, ⟨0, by simp⟩, ?_⟩
      intro x hx
      have hxy : x 0 ^ 2 + x 1 ^ 2 = 0 := by
        simpa [quadratic, Fin.sum_univ_two] using hx
      simpa [linear, Fin.sum_univ_two] using ((AnisotropicPlane.zero_iff hmod _ _).mp hxy).1

theorem possible_iff {p d : ℕ} [Fact p.Prime] (hd : 2 ≤ d) :
    possible p d ↔ p = 2 ∨ (d = 2 ∧ p % 4 = 3) := by
  constructor
  · rintro ⟨c, a, b, _, coeff, vanish⟩
    rcases (fixed_level hd c).mp ⟨a, b, coeff, vanish⟩ with h | ⟨hd', _, hmod⟩
    · exact Or.inl h
    · exact Or.inr ⟨hd', hmod⟩
  · intro h
    have i : Fin d := ⟨0, by omega⟩
    obtain ⟨a, b, ha, hb⟩ := (fixed_level hd (0 : ZMod p)).mpr
      (h.imp_right fun ⟨hd', hmod⟩ => ⟨hd', rfl, hmod⟩)
    refine ⟨0, a, b, ?_, ha, hb⟩
    intro zero
    let x : Fin d → ZMod p := fun j => if j = i then 1 else 0
    have hx := congrArg (eval x) zero
    simp [quadratic, x, Finset.sum_ite_eq'] at hx

end PlaneClassification
