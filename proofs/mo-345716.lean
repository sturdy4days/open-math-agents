import OMAStatements.S_mo_345716

/-!
A proof of the two-dimensional construction specified by @etaubman in
statement PR #21333 for Wenbo Sun's MathOverflow question 345716.
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

theorem possible_two {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) : possible p 2 := by
  let a : Fin 2 → ZMod p := ![1, 0]
  refine ⟨0, a, 0, ?_, ⟨0, by simp [a]⟩, ?_⟩
  · intro h
    have e := congrArg (eval a) h
    simp [quadratic, Fin.sum_univ_two, a] at e
  · intro x h
    have xy : x 0 ^ 2 + x 1 ^ 2 = 0 := by
      simpa [quadratic, Fin.sum_univ_two] using h
    simpa [linear, Fin.sum_univ_two, a] using ((zero_iff hp _ _).mp xy).1

end AnisotropicPlane

theorem OMA.solution : type_of% @OMA.S_mo_345716.main := by
  intro N
  obtain ⟨p, hN, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq N
    (q := 4) (a := 3) (by decide) (by decide)
  let : Fact p.Prime := ⟨hp⟩
  exact ⟨p, 2, hp, hN, le_rfl, rfl, AnisotropicPlane.possible_two hmod⟩
