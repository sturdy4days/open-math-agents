import OMAStatements.S_mo_138446
import Mathlib.Tactic

/-!
# Square residues of rational Mordell coordinates

The prime-by-prime argument follows somayeh didari’s MathOverflow answer 145955.
Noam D. Elkies specified that the points are rational in comment 357272. This
proof clears both denominators, treats zero residues separately, and obtains
the square root for every squarefree modulus without the congruence modulo 24.
-/

namespace MordellResidue

/-- Reduce a rational Mordell point when its x-coordinate is integral locally
at every prime dividing k. Translation by k leaves the reduced denominator
unchanged, so the denominator of y is a unit as well. -/
theorem reduce_point (k : ℤ) (x y : ℚ) (curve : y^2 = x^3 + (k:ℚ))
    (hx : x.den.Coprime k.natAbs) :
    ∃ b : ZMod k.natAbs, b^2 = ((x.num : ZMod k.natAbs)*(x.den : ZMod k.natAbs)⁻¹)^3 := by
  have den : y.den^2 = x.den^3 := by simpa using congrArg Rat.den curve
  have hy : y.den.Coprime k.natAbs := by
    apply (Nat.coprime_pow_left_iff (by decide : 0<2) _ _).1
    rw [den]
    exact hx.pow_left 3
  have denomQ : (y.den:ℚ)^2 = (x.den:ℚ)^3 := by exact_mod_cast den
  have numQ : (y.num:ℚ)^2 = (x.num:ℚ)^3 + (k:ℚ)*(x.den:ℚ)^3 := by
    calc
      _ = y^2 * (x.den:ℚ)^3 := by rw [← denomQ, ← mul_pow, Rat.mul_den_eq_num]
      _ = _ := by rw [curve, add_mul, ← mul_pow, Rat.mul_den_eq_num]
  have nums : y.num^2 = x.num^3 + k*(x.den:ℤ)^3 := by exact_mod_cast numQ
  let R := ZMod k.natAbs
  have nz : (k : R) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr Int.natAbs_dvd_self
  have yn : (y.num:R)^2 = (x.num:R)^3 := by
    have h := congrArg (fun z : ℤ => (z:R)) nums
    change ((y.num^2 : ℤ) : R) = ((x.num^3 + k*(x.den:ℤ)^3 : ℤ) : R) at h
    rw [Int.cast_pow,Int.cast_add,Int.cast_pow,Int.cast_mul,nz,zero_mul,add_zero] at h
    exact h
  have dn : (y.den:R)^2 = (x.den:R)^3 := by exact_mod_cast congrArg (fun z : ℕ => (z:R)) den
  have invX : (x.den:R)*(x.den:R)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime ..).mpr hx)
  have invY : (y.den:R)*(y.den:R)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime ..).mpr hy)
  have invpow : ((y.den:R)⁻¹)^2 = ((x.den:R)⁻¹)^3 := by
    calc
      _ = ((x.den:R)^3 * ((x.den:R)⁻¹)^3) * ((y.den:R)⁻¹)^2 := by rw [← mul_pow,invX,one_pow,one_mul]
      _ = ((x.den:R)⁻¹)^3 * ((y.den:R)*(y.den:R)⁻¹)^2 := by rw [← dn]; ring
      _ = _ := by rw [invY,one_pow,mul_one]
  exact ⟨(y.num:R)*(y.den:R)⁻¹, by rw [mul_pow,mul_pow,yn,invpow]⟩

end MordellResidue

namespace MordellResidue

lemma field_square_of_square_cube {F : Type*} [Field F] (a b : F) (h : b^2 = a^3) :
    IsSquare a := by
  by_cases ha : a = 0
  · exact ⟨0, by simp [ha]⟩
  · refine ⟨b/a, ?_⟩
    field_simp
    linear_combination -h

/-- In a squarefree residue ring, every element whose cube is a square is a square. -/
theorem square_of_square_cube (n : ℕ) : Squarefree n → ∀ a b : ZMod n,
    b^2 = a^3 → IsSquare a := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p e hp he =>
    intro hs
    obtain ⟨_,rfl⟩ := (Nat.squarefree_pow_iff hp.ne_one he.ne').mp hs
    rw [pow_one]
    have : Fact p.Prime := ⟨hp⟩
    exact field_square_of_square_cube
  | zero => simp
  | one =>
    intro _ a _ _
    exact ⟨0,Subsingleton.elim _ _⟩
  | coprime r s _ _ coprime hr hs =>
    intro sq a b eq
    let e := ZMod.chineseRemainder coprime
    have pair : (e b)^2 = (e a)^3 := by simpa using congrArg e eq
    obtain ⟨l,hl⟩ := hr ((Nat.squarefree_mul coprime).mp sq).1 (e a).1 (e b).1
      (congrArg Prod.fst pair)
    obtain ⟨u,hu⟩ := hs ((Nat.squarefree_mul coprime).mp sq).2 (e a).2 (e b).2
      (congrArg Prod.snd pair)
    refine ⟨e.symm (l,u), e.injective ?_⟩
    rw [map_mul, e.apply_symm_apply]
    exact Prod.ext hl hu

end MordellResidue

theorem MordellResidue.square_x (k : ℤ) (x y : ℚ) (sq : Squarefree k.natAbs)
    (curve : y^2 = x^3 + (k : ℚ)) (den : x.den.Coprime k.natAbs) :
    IsSquare ((x.num : ZMod k.natAbs) * (x.den : ZMod k.natAbs)⁻¹) := by
  obtain ⟨b,eq⟩ := MordellResidue.reduce_point k x y curve den
  exact MordellResidue.square_of_square_cube _ sq _ b eq

theorem OMA.solution : type_of% @OMA.S_mo_138446.main := by
  intro k x y sq _ curve den
  exact MordellResidue.square_x k x y sq curve den
