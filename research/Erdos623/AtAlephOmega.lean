import CountableBound

/-! At the exact cardinal in Erdős 623, some maps have no uncountable free set.
The maps constructed here attain the countable bound. -/

open Set Cardinal
open scoped Cardinal Ordinal
namespace Erdos623Lower
universe u

/-- On every set of cardinality aleph-omega, some input-avoiding map has an
infinite independent set and every independent set for it is countable. -/
theorem exact_countable_bound (X : Type u) (hx : #X = ℵ_ ω) :
    ∃ f : Finset X → X, (∀ A, f A ∉ A) ∧
      (∀ Y : Set X, (∀ B : Finset X, (B : Set X) ⊆ Y → f B ∉ Y) → Y.Countable) ∧
      ∃ Z : Set X, Z.Infinite ∧ ∀ B : Finset X, (B : Set X) ⊆ Z → f B ∉ Z := by
  classical
  let D (i : ℕ) := (ℵ_ (i : Ordinal.{u})).out
  have inst (i : ℕ) : Infinite (D i) := Cardinal.aleph0_le_mk_iff.mp (by
    simp [D])
  let : ∀ i, Infinite (D i) := inst
  have small (i : ℕ) : #(D i) < ℵ_ ω := by
    simp [D]
  obtain ⟨g,fresh,hits,Z,hzi,hz⟩ := countable_levels D (fun i => bad_map_below_aleph_omega (D i) (small i))
  obtain ⟨e⟩ : Nonempty ((Σ i, D i) ≃ X) := Cardinal.eq.mp (card_aleph_levels.trans hx.symm)
  let f (A : Finset X) := e (g (A.map e.symm.toEmbedding))
  have back (A : Finset (Σ i, D i)) : (A.map e.toEmbedding).map e.symm.toEmbedding = A := by
    ext x
    simp [Finset.mem_map_equiv]
  refine ⟨f, ?_, ?_, e '' Z,hzi.image e.injective.injOn, ?_⟩
  · intro A mem
    apply fresh (A.map e.symm.toEmbedding)
    exact Finset.mem_map_equiv.mpr mem
  · intro Y h
    have hy := (hits (e ⁻¹' Y) (by
      intro A hA hg
      have hsub : (A.map e.toEmbedding : Set X) ⊆ Y := by
        intro x hx
        obtain ⟨z,hm,rfl⟩ := Finset.mem_map.mp hx
        exact hA hm
      apply h (A.map e.toEmbedding) hsub
      change e (g A) ∈ Y at hg
      simpa only [f,back] using hg)).2
    simpa only [Set.image_preimage_eq _ e.surjective] using hy.image e
  · intro B hB hmem
    apply hz (B.map e.symm.toEmbedding)
    · intro x hx
      obtain ⟨z,hz⟩ := hB (Finset.mem_map_equiv.mp hx)
      exact e.injective hz.2 ▸ hz.1
    · obtain ⟨z,hz',hze⟩ := hmem
      exact e.injective hze ▸ hz'

end Erdos623Lower
#print axioms Erdos623Lower.countable_levels
#print axioms Erdos623Lower.card_aleph_levels
#print axioms Erdos623Lower.exact_countable_bound
