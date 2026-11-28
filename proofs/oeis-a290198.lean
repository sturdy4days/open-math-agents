import OMAStatements.S_oeis_a290198
import Mathlib.Tactic

/-!
# Stabilization of Rule 721

We prove David A. Corneth's formula for Robert Price's sequence
by tracking the entire plane. The first four OFF sets after the seed are the cross,
the four diagonal neighbors, the boundary of the central square, and the origin.
The last of these configurations is fixed.
-/

namespace Corneth721
open OMA.S_oeis_a290198 Finset

/-- The proposed sequence of full-plane configurations. -/
private def plane : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | 1, x, y => !decide ((x = 0 ∧ -1 ≤ y ∧ y ≤ 1) ∨ (y = 0 ∧ -1 ≤ x ∧ x ≤ 1))
  | 2, x, y => !decide ((x = -1 ∨ x = 1) ∧ (y = -1 ∨ y = 1))
  | 3, x, y => !decide (-1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 ∧ (x ≠ 0 ∨ y ≠ 0))
  | _ + 4, x, y => !decide (x = 0 ∧ y = 0)

private def update (v l r d u : Bool) : Bool :=
  Nat.testBit 721 (v.toNat + 2*(l.toNat + r.toNat + d.toNat + u.toNat))

private theorem outside (n : ℕ) (x y : ℤ)
    (far : x < -1 ∨ 1 < x ∨ y < -1 ∨ 1 < y) : plane n x y = decide (n ≠ 0) := by
  rcases n with _ | _ | _ | _ | n <;> simp [plane] <;> omega

private theorem check_square : ∀ t i j : Fin 5,
    let x : ℤ := (i.val : ℤ) - 2
    let y : ℤ := (j.val : ℤ) - 2
    plane (t.val+1) x y = update (plane t.val x y)
      (plane t.val (x-1) y) (plane t.val (x+1) y)
      (plane t.val x (y-1)) (plane t.val x (y+1)) := by decide +kernel

private theorem local_update (n : ℕ) (x y : ℤ) :
    plane (n+1) x y = update (plane n x y)
      (plane n (x-1) y) (plane n (x+1) y) (plane n x (y-1)) (plane n x (y+1)) := by
  by_cases box : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · let i : Fin 5 := ⟨(x+2).toNat, by omega⟩
    let j : Fin 5 := ⟨(y+2).toNat, by omega⟩
    have hi : (i.val : ℤ)-2 = x := by dsimp [i]; omega
    have hj : (j.val : ℤ)-2 = y := by dsimp [j]; omega
    have h (t : Fin 5) := check_square t i j
    dsimp only at h
    rw [hi,hj] at h
    rcases n with _ | _ | _ | _ | n
    · exact h 0
    · exact h 1
    · exact h 2
    · exact h 3
    · exact h 4
  · rw [outside (n+1) x y (by omega), outside n x y (by omega),
      outside n (x-1) y (by omega), outside n (x+1) y (by omega),
      outside n x (y-1) (by omega), outside n x (y+1) (by omega)]
    rw [decide_eq_true (show n+1 ≠ 0 by omega)]
    cases decide (n ≠ 0) <;> decide

private theorem config (n : ℕ) (x y : ℤ) : state n x y = plane n x y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    rw [state, local_update]
    simp only [ih, update]

/-- From time four onwards the origin is the only OFF cell in the entire plane. -/
theorem stabilized (n : ℕ) (hn : 4 ≤ n) (x y : ℤ) :
    state n x y = !decide (x=0 ∧ y=0) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m+4 := ⟨n-4, by omega⟩
  exact config (m+4) x y

theorem digits (n : ℕ) (hn : 4 ≤ n) : (a n : ℤ) = 2^(n+1) - 2 := by
  have binary (m : ℕ) :
      (∑ k ∈ range (m+1), if k=0 then 0 else 2^k) + 2 = 2^(m+1) := by
    induction m with
    | zero => decide
    | succ m ih =>
      rw [sum_range_succ]
      simp only [Nat.succ_ne_zero, if_false]
      rw [pow_succ (2 : ℕ) (m+1)]
      omega
  have h : a n + 2 = 2^(n+1) := by
    simpa [a, stabilized n hn] using binary n
  have hz : (a n : ℤ) + 2 = 2^(n+1) := by exact_mod_cast h
  omega

end Corneth721

theorem OMA.solution : type_of% @OMA.S_oeis_a290198.main := by
  refine ⟨?_, Corneth721.digits⟩
  intro n hn
  interval_cases n <;> decide +kernel
