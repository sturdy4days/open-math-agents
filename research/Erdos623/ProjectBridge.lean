import FormalConjectures.ErdosProblems.«623»
import Erdos623.ZFCBridge

/-!
This file specializes Sungchul Lee's countable-language free-subset equivalence
to the exact pinned Formal Conjectures declaration. The proof works at every
universe level. It also proves upward transfer along arbitrary embeddings.
-/

open Set Cardinal
open scoped Cardinal Ordinal

namespace OMA.Erdos623Bridge

universe u

/-- The registered problem permits any infinite witness. A countably infinite
subset of that witness retains independence for every finite input. -/
theorem infiniteWitness_iff (X : Type u) :
    (∀ f : Finset X → X, (∀ A, f A ∉ A) →
      ∃ Y : Set X, Y.Infinite ∧ ∀ B : Finset X, ↑B ⊆ Y → f B ∉ Y) ↔
      Erdos623.E623 X := by
  constructor
  · intro h f hf
    obtain ⟨Y, hi, hfree⟩ := h f hf
    obtain ⟨Z, hZY, hc, hz⟩ := hi.exists_subset_countable_infinite
    exact ⟨Z, ⟨hc, hz⟩, Erdos623.independent_mono hZY hfree⟩
  · intro h f hf
    obtain ⟨Y, ⟨_, hi⟩, hfree⟩ := h f hf
    exact ⟨Y, hi, hfree⟩

/-- Freeness transfers to a larger distinguished set because any embedding of
that set into a structure also embeds the original distinguished set. -/
theorem structural_of_embedding {X Y : Type u} (e : X ↪ Y)
    (h : Erdos623.FrOmega.{u,u,0,0} X) : Erdos623.FrOmega.{u,u,0,0} Y := by
  intro M g L inst hL
  obtain ⟨S, ⟨hc, hi⟩, hf⟩ := h M (e.trans g) L inst hL
  refine ⟨e '' S, ⟨hc.image _, hi.image e.injective.injOn⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have him : g '' (e '' S \ {e x}) = (e.trans g) '' (S \ {x}) := by
    ext z
    constructor
    · rintro ⟨_, ⟨⟨v, hv, rfl⟩, hne⟩, rfl⟩
      exact ⟨v, ⟨hv, fun he => hne (congrArg e he)⟩, rfl⟩
    · rintro ⟨v, ⟨hv, hne⟩, rfl⟩
      exact ⟨e v, ⟨⟨v, hv, rfl⟩, fun he => hne (e.injective he)⟩, rfl⟩
  rw [him]
  exact hf x hx

/-- The arbitrary well-order chosen to apply the donor bridge does not occur
in either endpoint. -/
theorem singleton_iff_structural (X : Type u) [Infinite X] :
    Erdos623.E623 X ↔ Erdos623.FrOmega.{u,u,0,0} X := by
  classical
  let : LinearOrder X := linearOrderOfSTO (@WellOrderingRel X)
  let : IsWellOrder X (· < ·) := WellOrderingRel.isWellOrder
  obtain ⟨h₁, h₂, h₃⟩ := Erdos623.zfcBridge (α := X)
  exact (h₁.trans h₂).trans h₃

/-- The exact project proposition at aleph-omega is equivalent to Koepke's
structural property on one representative of that cardinal. -/
theorem exact_iff_koepke : (type_of% @Erdos623.erdos_623.{u}) ↔
    Erdos623.FrOmega.{u,u,0,0} (ℵ_ ω : Cardinal.{u}).out := by
  have card_rep : #((ℵ_ ω : Cardinal.{u}).out) = ℵ_ ω := Cardinal.mk_out _
  have : Infinite (ℵ_ ω : Cardinal.{u}).out := Cardinal.aleph0_le_mk_iff.mp
    (card_rep.symm ▸ Cardinal.aleph0_le_aleph ω)
  constructor
  · intro h
    exact (singleton_iff_structural _).mp ((infiniteWitness_iff _).mp (h _ card_rep))
  · intro h X hX
    have : Infinite X := Cardinal.aleph0_le_mk_iff.mp (hX.symm ▸ Cardinal.aleph0_le_aleph ω)
    obtain ⟨e⟩ := (Cardinal.le_def _ _).mp (le_of_eq (card_rep.trans hX.symm))
    exact (infiniteWitness_iff _).mpr ((singleton_iff_structural _).mpr (structural_of_embedding e h))

/-- A positive answer would apply at every cardinal at least aleph-omega. -/
theorem free_above (h : type_of% @Erdos623.erdos_623.{u}) (X : Type u)
    (hX : ℵ_ ω ≤ #X) (f : Finset X → X) (hf : ∀ A, f A ∉ A) :
    ∃ Y : Set X, Y.Countable ∧ Y.Infinite ∧ ∀ B : Finset X, ↑B ⊆ Y → f B ∉ Y := by
  have : Infinite X := Cardinal.aleph0_le_mk_iff.mp ((Cardinal.aleph0_le_aleph ω).trans hX)
  obtain ⟨e⟩ : Nonempty ((ℵ_ ω : Cardinal.{u}).out ↪ X) := (Cardinal.le_def _ _).mp (by simpa using hX)
  obtain ⟨Y, ⟨hc, hi⟩, hfree⟩ := (singleton_iff_structural X).mpr
    (structural_of_embedding e (exact_iff_koepke.mp h)) f hf
  exact ⟨Y, hc, hi, hfree⟩

end OMA.Erdos623Bridge
