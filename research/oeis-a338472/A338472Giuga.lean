import Mathlib

/-!
# OEIS A338472 and Giuga's conjecture

Pairing the residues `i` and `n - i` identifies the two power sums for odd `n`.
The even case uses the reflection argument from ZenimXD's Agoh–Giuga equivalence proof.
The two formulations express the same open question.

* [OEIS A338472](https://oeis.org/A338472)
* [A338472 Lean statement under review](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/fe8dbffee6ae366b32cfb62f2fad8c4a539fa1ed/statements/oeis-a338472.lean)
* [Pinned Giuga statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/Wikipedia/AgohGiuga.lean#L55-L71)
* [ZenimXD's Agoh–Giuga equivalence proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/421)
-/

namespace A338472Giuga

open Finset

/-- The divisibility test from OEIS A338472, restricted to even summands. -/
def HalfTest (n : ℕ) : Prop :=
  n ∣ 1 + ∑ j ∈ Icc 1 ((n - 1) / 2), 2 * (2 * j) ^ (n - 1)

/-- The full power-sum test in Giuga's formulation. -/
def FullTest (n : ℕ) : Prop :=
  n ∣ 1 + ∑ i ∈ Ioo 0 n, i ^ (n - 1)

/-- For odd moduli each pair contributes twice its even member's power. -/
private theorem odd_half (n : ℕ) (hodd : Odd n) :
    (∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1)) ≡
    (∑ j ∈ Finset.Icc 1 ((n - 1) / 2), 2 * (2 * j) ^ (n - 1)) [MOD n] := by
  obtain ⟨m, rfl⟩ := hodd
  let half := Finset.Icc 1 m
  let evenPart := half.image (fun j => 2 * j)
  let oddPart := half.image (fun j => 2 * m + 1 - 2 * j)
  have unionParts : Finset.Ioo 0 (2 * m + 1) = evenPart ∪ oddPart := by
    ext i
    simp only [evenPart, oddPart, half, Finset.mem_Ioo, Finset.mem_union, Finset.mem_image,
      Finset.mem_Icc]
    constructor
    · intro ⟨hi₀, hi₁⟩
      by_cases heven : i % 2 = 0
      · exact Or.inl ⟨i / 2, ⟨by omega, by omega⟩, by omega⟩
      · exact Or.inr ⟨(2 * m + 1 - i) / 2, ⟨by omega, by omega⟩, by omega⟩
    · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> omega
  have disjointParts : Disjoint evenPart oddPart := by
    rw [Finset.disjoint_left]
    intro i hiEven hiOdd
    simp only [evenPart, oddPart, half, Finset.mem_image, Finset.mem_Icc] at hiEven hiOdd
    obtain ⟨j, hj, hji⟩ := hiEven
    obtain ⟨k, hk, hki⟩ := hiOdd
    omega
  have injectEven : Set.InjOn (fun j : ℕ => 2 * j) half := by
    intro a _ b _ h
    change 2 * a = 2 * b at h
    omega
  have injectOdd : Set.InjOn (fun j : ℕ => 2 * m + 1 - 2 * j) half := by
    intro a ha b hb h
    simp only [Finset.mem_coe, half, Finset.mem_Icc] at ha hb
    change 2 * m + 1 - 2 * a = 2 * m + 1 - 2 * b at h
    omega
  have evenExponent : Even (2 * m + 1 - 1) := ⟨m, by omega⟩
  have reflectPow (j : ℕ) (hj : j ∈ half) :
      ((2 * m + 1 - 2 * j : ℕ) : ZMod (2 * m + 1)) ^ (2 * m + 1 - 1) =
        ((2 * j : ℕ) : ZMod (2 * m + 1)) ^ (2 * m + 1 - 1) := by
    have hle : 2 * j ≤ 2 * m + 1 := by
      simp only [half, Finset.mem_Icc] at hj
      omega
    rw [Nat.cast_sub hle, ZMod.natCast_self, zero_sub, evenExponent.neg_pow]
  have normalizeHalf : (2 * m + 1 - 1) / 2 = m := by omega
  rw [← ZMod.natCast_eq_natCast_iff, normalizeHalf]
  push_cast
  rw [unionParts, Finset.sum_union disjointParts, Finset.sum_image injectEven,
    Finset.sum_image injectOdd]
  have reflectSum :
      (∑ j ∈ half, (↑(2 * m + 1 - 2 * j) : ZMod (2 * m + 1)) ^ (2 * m + 1 - 1)) =
        ∑ j ∈ half, (↑(2 * j) : ZMod (2 * m + 1)) ^ (2 * m + 1 - 1) :=
    Finset.sum_congr rfl reflectPow
  rw [show 2 * m + 1 - 1 = 2 * m by omega] at reflectSum
  rw [reflectSum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by push_cast; ring)

/-- An even modulus greater than two cannot satisfy the full divisibility test. -/
private theorem even_composite (n : ℕ) (he : Even n) (hc : 2 < n) :
    ¬ n ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) := by
  have hodd : Odd (n - 1) := by
    obtain ⟨k, hk⟩ := he
    exact ⟨k - 1, by omega⟩
  let s : ZMod n := ∑ i ∈ Ioo 0 n, (i : ZMod n) ^ (n - 1)
  have hmem (i : ℕ) (hi : i ∈ Ioo 0 n) : n - i ∈ Ioo 0 n := by
    rw [mem_Ioo] at hi ⊢
    omega
  have hreflect (i : ℕ) (hi : i ∈ Ioo 0 n) : n - (n - i) = i := by
    have hi' := (mem_Ioo.mp hi).2
    omega
  have hperm : s = ∑ i ∈ Ioo 0 n, ((n - i : ℕ) : ZMod n) ^ (n - 1) := by
    change (∑ i ∈ Ioo 0 n, (i : ZMod n) ^ (n - 1)) = _
    refine sum_bij' (fun i _ => n - i) (fun i _ => n - i) hmem hmem
      hreflect hreflect ?_
    intro i hi
    rw [hreflect i hi]
  have hs : s = -s := by
    calc
      s = ∑ i ∈ Ioo 0 n, ((n - i : ℕ) : ZMod n) ^ (n - 1) := hperm
      _ = ∑ i ∈ Ioo 0 n, -((i : ZMod n) ^ (n - 1)) := by
        refine sum_congr rfl fun i hi => ?_
        rw [Nat.cast_sub (mem_Ioo.mp hi).2.le, ZMod.natCast_self, zero_sub, hodd.neg_pow]
      _ = -s := Finset.sum_neg_distrib _
  intro hd
  have hz : (1 : ZMod n) + s = 0 := by
    change (1 : ZMod n) + ∑ i ∈ Ioo 0 n, (i : ZMod n) ^ (n - 1) = 0
    exact_mod_cast (ZMod.natCast_eq_zero_iff (1 + ∑ i ∈ Ioo 0 n, i ^ (n - 1)) n).mpr hd
  have ht : (2 : ZMod n) = 0 := by
    linear_combination 2 * hz - hs
  have hn2 : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp (by simpa using ht)
  exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < (2 : ℕ)) hc hn2

private theorem even_half_exclusion (n : ℕ) (hn : Even n) : ¬ HalfTest n := by
  intro hd
  have hsum : 2 ∣ ∑ j ∈ Icc 1 ((n - 1) / 2), 2 * (2 * j) ^ (n - 1) :=
    dvd_sum (fun _ _ => dvd_mul_right _ _)
  have hnum := (even_iff_two_dvd.mp hn).trans hd
  omega

/-- At each input the two conjectures make equivalent assertions, including at `n = 2`. -/
theorem pointwise (n : ℕ) (hn : 2 ≤ n) :
    (HalfTest n ↔ n.Prime ∧ n ≠ 2) ↔ (n.Prime ↔ FullTest n) := by
  rcases Nat.even_or_odd n with he | ho
  · by_cases htwo : n = 2
    · subst n
      unfold HalfTest FullTest
      decide
    · have hprime : ¬ n.Prime := by
        intro hp
        rcases hp.eq_two_or_odd with h | h
        · exact htwo h
        · obtain ⟨k, hk⟩ := he
          omega
      have hf : ¬ FullTest n := even_composite n he (by omega)
      simp [even_half_exclusion n he, hprime, hf]
  · have htwo : n ≠ 2 := by obtain ⟨k, hk⟩ := ho; omega
    have eqDvd : FullTest n ↔ HalfTest n :=
      ((odd_half n ho).add_left 1).dvd_iff (dvd_refl n)
    rw [and_iff_left htwo, eqDvd]
    exact iff_comm

/-- The OEIS conjecture is equivalent to the full Giuga primality conjecture. -/
theorem equivalent :
    (∀ n : ℕ, 2 ≤ n →
      (n ∣ 1 + ∑ j ∈ Finset.Icc 1 ((n - 1) / 2), 2 * (2 * j) ^ (n - 1) ↔
        n.Prime ∧ n ≠ 2)) ↔
    (∀ n : ℕ, 2 ≤ n →
      (n.Prime ↔ n ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1))) := by
  constructor
  · intro h n hn
    exact (pointwise n hn).mp (h n hn)
  · intro h n hn
    exact (pointwise n hn).mpr (h n hn)

end A338472Giuga
