import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Which residue rings turn square cubes into squares?

For positive n, every pair of residues satisfying b² = a³ has a square
first coordinate exactly when n is squarefree. The converse uses a cube-zero
counterexample modulo a repeated prime power and the Chinese remainder
theorem. At n = 0 the residue ring is the integers.

The sufficient direction reuses the primewise argument from the formal proof
of MathOverflow 138446, following somayeh didari's answer 145955. The
necessity statement here quantifies over all residue pairs on b² = a³.
-/

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

namespace MordellResidue

/-- A p-power of odd valuation strictly below k is a nonsquare modulo p^k. -/
theorem nonsquare_odd_power {p k : ℕ} (hp : p.Prime) (t : ℕ) (below : 2*t+1 < k) :
    ¬ IsSquare ((p : ZMod (p^k))^(2*t+1)) := by
  let : NeZero (p^k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rintro ⟨y,hy⟩
  let v := 2*t+1
  have congruence : p^v ≡ y.val^2 [MOD p^k] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa [v,pow_two, ZMod.natCast_zmod_val] using hy
  have same (j : ℕ) (le : j≤k) : p^j ∣ p^v ↔ p^j ∣ y.val^2 := by
    have h := congruence.of_dvd (pow_dvd_pow p le)
    exact ⟨fun hv => Nat.modEq_zero_iff_dvd.mp (h.symm.trans hv.modEq_zero_nat),
      fun hy' => Nat.modEq_zero_iff_dvd.mp (h.trans hy'.modEq_zero_nat)⟩
  have low : p^v ∣ y.val^2 := (same v (by omega)).mp dvd_rfl
  have high : ¬ p^(v+1) ∣ y.val^2 := by
    intro div
    have bound := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp ((same (v+1) (by omega)).mpr div)
    omega
  have pos : y.val^2 ≠ 0 := by
    rintro eq
    apply high
    rw [eq]
    exact dvd_zero _
  rw [hp.pow_dvd_iff_le_factorization pos] at low high
  simp only [Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul] at low high
  dsimp [v] at low high
  omega

/-- The largest odd exponent below k yields a cube-zero, nonsquare residue.
For k even this exponent is k−1, and for k odd it is k−2. -/
theorem prime_power_counterexample (p k : ℕ) (hp : p.Prime) (hk : 2≤k) :
    ∃ a : ZMod (p^k), a^3=0 ∧ ¬IsSquare a := by
  let t := (k-2)/2
  let v := 2*t+1
  have lower : v<k := by dsimp [v,t]; omega
  have triple : k≤v*3 := by dsimp [v,t]; omega
  refine ⟨(p : ZMod (p^k))^v,?_,nonsquare_odd_power hp t lower⟩
  rw [←pow_mul,←Nat.cast_pow]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr (pow_dvd_pow p triple)
end MordellResidue

namespace MordellResidue

/-- A cube-zero nonsquare in either CRT factor gives one in the residue ring.
This statement also works when one of the factors is the trivial ring. -/
theorem crt_nonsquare_cube_zero {r s : ℕ} (coprime : r.Coprime s)
    (h : (∃ a : ZMod r, a ^ 3 = 0 ∧ ¬ IsSquare a) ∨
         (∃ a : ZMod s, a ^ 3 = 0 ∧ ¬ IsSquare a)) :
    ∃ a : ZMod (r * s), a ^ 3 = 0 ∧ ¬ IsSquare a := by
  let e := ZMod.chineseRemainder coprime
  rcases h with ⟨a, ha, no⟩ | ⟨b, hb, no⟩
  · refine ⟨e.symm (a, 0), e.injective ?_, ?_⟩
    · rw [map_pow, e.apply_symm_apply, map_zero]
      exact Prod.ext ha (by simp)
    · rintro ⟨x, hx⟩
      apply no
      refine ⟨(e x).1, ?_⟩
      simpa using congrArg (fun z => (e z).1) hx
  · refine ⟨e.symm (0, b), e.injective ?_, ?_⟩
    · rw [map_pow, e.apply_symm_apply, map_zero]
      exact Prod.ext (by simp) hb
    · rintro ⟨x, hx⟩
      apply no
      refine ⟨(e x).2, ?_⟩
      simpa using congrArg (fun z => (e z).2) hx

/-- Prime-power obstructions propagate to every positive nonsquarefree modulus. -/
theorem nonsquare_cube_zero_of_prime_powers
    (bad : ∀ p k : ℕ, p.Prime → 2 ≤ k → ∃ a : ZMod (p ^ k), a ^ 3 = 0 ∧ ¬ IsSquare a)
    (n : ℕ) : 0 < n → ¬ Squarefree n → ∃ a : ZMod n, a ^ 3 = 0 ∧ ¬ IsSquare a := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp
  | prime_pow p k hp hk =>
    intro _ ns
    apply bad p k hp
    by_contra! h
    obtain rfl : k = 1 := by omega
    exact ns (by simpa using hp.squarefree)
  | coprime r s rp sp h hr hs =>
    intro _ ns
    apply crt_nonsquare_cube_zero h
    by_cases sr : Squarefree r
    · exact Or.inr (hs (by omega) fun ss => ns ((Nat.squarefree_mul h).mpr ⟨sr,ss⟩))
    · exact Or.inl (hr (by omega) sr)

end MordellResidue

namespace MordellResidue

/-- At modulus zero the residue ring is the integers. Coprimality of
the exponents three and two forces the nonnegative cubic base to be a square. -/
private theorem integer_square (a b : ℤ) (eq : b ^ 2 = a ^ 3) : IsSquare a := by
  have ha : 0 ≤ (a : ℤ) := by
    by_contra! h
    have neg : (a : ℤ) ^ 3 < 0 := (by decide : Odd 3).pow_neg h
    exact ((sq_nonneg (b : ℤ)).not_gt (eq.trans_lt neg))
  have posEq : a.natAbs ^ 3 = b.natAbs ^ 2 := by simpa only [Int.natAbs_pow] using congrArg Int.natAbs eq.symm
  obtain ⟨c,hc,_⟩ := Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow
    (by decide : Nat.Coprime 3 2) posEq
  refine ⟨(c : ℤ), ?_⟩
  calc (a : ℤ) = ((a : ℤ).natAbs : ℤ) := (Int.natAbs_of_nonneg ha).symm
       _ = (c : ℤ) * c := by exact_mod_cast hc.trans (pow_two c)

theorem zero_modulus_square (a b : ZMod 0) (eq : b ^ 2 = a ^ 3) : IsSquare a :=
  integer_square a b eq

end MordellResidue

namespace MordellResidue

/-- A positive nonsquarefree modulus already fails the square-cube property on
the singular point with y-coordinate zero. -/
theorem nonsquare_cube_zero (n : ℕ) (hn : 0<n) (h : ¬Squarefree n) :
    ∃ a : ZMod n, a^3=0 ∧ ¬IsSquare a :=
  nonsquare_cube_zero_of_prime_powers prime_power_counterexample n hn h

theorem cube_zero_squares_iff_squarefree (n : ℕ) (hn : 0<n) :
    (∀ a : ZMod n, a^3=0 → IsSquare a) ↔ Squarefree n := by
  constructor
  · intro all
    by_contra bad
    obtain ⟨a,zero,no⟩ := nonsquare_cube_zero n hn bad
    exact no (all a zero)
  · intro sq a zero
    exact square_of_square_cube n sq a 0 (by simp [zero])

/-- The square-cube implication on all residue pairs characterizes the
positive squarefree moduli. -/
theorem square_cube_iff_squarefree (n : ℕ) (hn : 0<n) :
    (∀ a b : ZMod n, b^2=a^3 → IsSquare a) ↔ Squarefree n := by
  refine ⟨fun all => (cube_zero_squares_iff_squarefree n hn).mp (fun a zero => ?_),square_of_square_cube n⟩
  exact all a 0 (by simp [zero])
/-- At modulus zero the ring is ℤ, where the square-cube implication also holds. -/
theorem square_cube_moduli (n : ℕ) :
    (∀ a b : ZMod n, b^2=a^3 → IsSquare a) ↔ n=0 ∨ Squarefree n := by
  cases n with
  | zero => exact ⟨fun _ => Or.inl rfl,fun _ => zero_modulus_square⟩
  | succ k => simpa using square_cube_iff_squarefree (k+1) (Nat.succ_pos _)
end MordellResidue

#print axioms MordellResidue.nonsquare_odd_power
#print axioms MordellResidue.prime_power_counterexample
#print axioms MordellResidue.nonsquare_cube_zero
#print axioms MordellResidue.cube_zero_squares_iff_squarefree
#print axioms MordellResidue.square_cube_iff_squarefree
#print axioms MordellResidue.zero_modulus_square
#print axioms MordellResidue.square_cube_moduli
