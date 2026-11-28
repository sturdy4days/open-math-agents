import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-!
A computable countable obstruction for the lower-cardinal variant of Erdős 623.
A finite free subset has exactly as many elements as its minimum permits.
The example realizes every member of every infinite set using the remaining members.
-/

namespace OMA.Erdos623Lower

/-- Output the cardinality whenever possible, with a fresh value as a fallback. -/
def cardMap (A : Finset ℕ) : ℕ :=
  if A.card ∈ A then A.sup id + 1 else A.card

theorem avoids (A : Finset ℕ) : cardMap A ∉ A := by
  unfold cardMap
  split_ifs with h
  · intro hy
    have hle : A.sup id + 1 ≤ A.sup id := Finset.le_sup (f := id) hy
    omega
  · exact h

/-- Every natural number is hit, using a finite subset of any given infinite set
that omits the desired output. -/
theorem hits_every_member {Y : Set ℕ} (hi : Y.Infinite) (n : ℕ) :
    ∃ A : Finset ℕ, (A : Set ℕ) ⊆ Y ∧ n ∉ A ∧ A.card = n ∧ cardMap A = n := by
  obtain ⟨A, hA, hc⟩ := (hi.sdiff (Set.finite_singleton n)).exists_subset_card_eq n
  have hnA : n ∉ A := fun h => (hA h).2 (by rfl)
  exact ⟨A, fun _ h => (hA h).1, hnA, hc, by simp [cardMap, hc, hnA]⟩

/-- The countable version of the registered existential assertion fails. -/
theorem no_infinite_free : ¬ ∃ Y : Set ℕ, Y.Infinite ∧
    ∀ A : Finset ℕ, ↑A ⊆ Y → cardMap A ∉ Y := by
  rintro ⟨Y, hi, hfree⟩
  obtain ⟨x, hx⟩ := hi.nonempty
  obtain ⟨A, hAY, _, _, hit⟩ := hits_every_member hi x
  exact hfree A hAY (hit ▸ hx)

/-- The free finite sets are precisely the sets whose members are all at least
as large as the cardinality of the set. This includes the empty set. -/
theorem finite_free_iff (Y : Finset ℕ) :
    (∀ A : Finset ℕ, A ⊆ Y → cardMap A ∉ Y) ↔ ∀ x ∈ Y, Y.card ≤ x := by
  constructor
  · intro hfree n hn
    by_contra! hlt
    obtain ⟨A, hA, hc⟩ := (Y.erase n).exists_subset_card_eq (n := n) (by
      rw [Finset.card_erase_of_mem hn]; omega)
    have hnA : n ∉ A := fun h => (Finset.mem_erase.mp (hA h)).1 rfl
    have hnot := hfree A (hA.trans (Finset.erase_subset _ _))
    exact hnot (by simpa [cardMap, hc, hnA] using hn)
  · intro hmin A hA hh
    by_cases hb : A.card ∈ A
    · have heq := Finset.eq_of_subset_of_card_le hA (hmin _ (hA hb))
      subst Y
      exact avoids A hh
    · have hmem : A.card ∈ Y := by simpa [cardMap, hb] using hh
      have heq := Finset.eq_of_subset_of_card_le hA (hmin _ hmem)
      exact hb (heq ▸ hmem)

/-- For each size, the free finite sets include the consecutive block starting
at that size. Thus arbitrarily large finite witnesses coexist with failure on
every infinite set. -/
theorem free_sets_all_sizes (n : ℕ) :
    ∃ Y : Finset ℕ, Y.card = n ∧ ∀ A : Finset ℕ, A ⊆ Y → cardMap A ∉ Y := by
  let e : ℕ ↪ ℕ := ⟨fun i => n + i, fun _ _ h => Nat.add_left_cancel h⟩
  refine ⟨(Finset.range n).map e, by simp, (finite_free_iff _).mpr ?_⟩
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
  rw [Finset.card_map, Finset.card_range]
  change n ≤ n + i
  omega

end OMA.Erdos623Lower
