import ErdosHajnalLower
import Mathlib.SetTheory.Cardinal.Arithmetic

/-! A consequence of the finite-aleph negative construction of Erdős and Hajnal
(1958, Theorem 2). Taking countably many disjoint levels bounds the size of
every independent set at the first limit aleph. -/

open Set Cardinal
open scoped Cardinal Ordinal
namespace Erdos623Lower

universe u

/-- Local obstructions on each of countably many levels give a global map with
finite independent fibers. The same map admits an infinite free transversal. -/
theorem countable_levels (D : ℕ → Type u) [∀ i, Infinite (D i)]
    (bad : ∀ i, ∃ f : Finset (D i) → D i, (∀ A, f A ∉ A) ∧
      ∀ Y : Set (D i), Y.Infinite → ∃ A : Finset (D i), (A : Set (D i)) ⊆ Y ∧ f A ∈ Y) :
    ∃ g : Finset (Σ i, D i) → (Σ i, D i), (∀ B, g B ∉ B) ∧
      (∀ Y : Set (Σ i, D i), (∀ B : Finset _, (B : Set _) ⊆ Y → g B ∉ Y) →
        (∀ i, (Sigma.mk i ⁻¹' Y).Finite) ∧ Y.Countable) ∧
      ∃ Z : Set (Σ i, D i), Z.Infinite ∧ ∀ B : Finset _, (B : Set _) ⊆ Z → g B ∉ Z := by
  classical
  choose f fresh hits using bad
  let inc (i : ℕ) : D i ↪ (Σ i, D i) := Function.Embedding.sigmaMk i
  let P (B : Finset (Σ i, D i)) (z : Σ i, D i) : Prop :=
    ∃ (i : ℕ) (A : Finset (D i)), A.Nonempty ∧ B = A.map (inc i) ∧ z = inc i (f i A)
  have unique {B x y} (hx : P B x) (hy : P B y) : x = y := by
    obtain ⟨i,A,⟨a,ha⟩,rfl,rfl⟩ := hx
    obtain ⟨j,C,_,eqn,rfl⟩ := hy
    have mem : inc i a ∈ C.map (inc j) := eqn ▸ Finset.mem_map_of_mem _ ha
    obtain ⟨b,_,hb⟩ := Finset.mem_map.mp mem
    obtain rfl : j = i := congrArg Sigma.fst hb
    obtain rfl : A = C := Finset.map_injective (inc j) eqn
    rfl
  have escape (B : Finset (Σ i, D i)) : ∃ z ∈ Set.range (inc 0), z ∉ B := by
    obtain ⟨z,hz⟩ := ((Set.infinite_range_of_injective (inc 0).injective).sdiff B.finite_toSet).nonempty
    exact ⟨z,hz.1,hz.2⟩
  let g (B : Finset (Σ i, D i)) := if h : ∃ z, P B z then h.choose else (escape B).choose
  have onLevel (i : ℕ) (A : Finset (D i)) (ha : A.Nonempty) :
      g (A.map (inc i)) = inc i (f i A) := by
    have h : ∃ z, P (A.map (inc i)) z := ⟨_, i,A,ha,rfl,rfl⟩
    exact (dif_pos h).trans (unique h.choose_spec ⟨i,A,ha,rfl,rfl⟩)
  refine ⟨g, ?_, ?_, ?_⟩
  · intro B
    by_cases h : ∃ z, P B z
    · obtain ⟨z,i,A,ha,rfl,rfl⟩ := h
      rw [onLevel i A ha, Finset.mem_map']
      exact fresh i A
    · change (if h : ∃ z, P B z then h.choose else (escape B).choose) ∉ B
      rw [dif_neg h]
      exact (escape B).choose_spec.2
  · intro Y free
    have fibers (i : ℕ) : (inc i ⁻¹' Y).Finite := by
      by_contra inf
      let S := (inc i ⁻¹' Y) \ {f i ∅}
      obtain ⟨A,hA,hfa⟩ := hits i S ((show (inc i ⁻¹' Y).Infinite from inf).sdiff (Set.finite_singleton _))
      have ha : A.Nonempty := by
        by_contra! h
        subst A
        exact hfa.2 (Set.mem_singleton _)
      have hsub : (A.map (inc i) : Set (Σ i, D i)) ⊆ Y := by
        intro z hz
        obtain ⟨a,h,rfl⟩ := Finset.mem_map.mp hz
        exact (hA h).1
      exact free _ hsub (onLevel i A ha ▸ hfa.1)
    refine ⟨fibers, ?_⟩
    apply (Set.countable_iUnion (fun i => (fibers i).countable.image (inc i))).mono
    rintro ⟨i,a⟩ h
    exact Set.mem_iUnion.mpr ⟨i,a,h,rfl⟩
  · let w (i : ℕ) : Σ i, D i := ⟨i+1, Classical.choice (inferInstance : Nonempty (D (i+1)))⟩
    have hi : Function.Injective w := fun i j eqn => Nat.succ.inj (congrArg Sigma.fst eqn)
    refine ⟨Set.range w, Set.infinite_range_of_injective hi, ?_⟩
    intro B hB
    by_cases h : ∃ z, P B z
    · obtain ⟨z,i,A,⟨a,ha⟩,rfl,rfl⟩ := h
      rw [onLevel i A ⟨a,ha⟩]
      rintro ⟨j,eqj⟩
      obtain ⟨k,eqk⟩ := hB (Finset.mem_map_of_mem _ ha)
      have same : j = k := Nat.succ.inj ((congrArg Sigma.fst eqj).trans (congrArg Sigma.fst eqk).symm)
      subst k
      exact fresh i A ((inc i).injective (eqj.symm.trans eqk) ▸ ha)
    · rw [show g B = _ from dif_neg h]
      obtain ⟨x,hx⟩ := (escape B).choose_spec.1
      rintro ⟨i,hi⟩
      exact Nat.succ_ne_zero i (congrArg Sigma.fst (hi.trans hx.symm))

/-- The sigma type of finite-aleph levels has cardinality aleph-omega. -/
theorem card_aleph_levels :
    #(Σ n : ℕ, (ℵ_ (n : Ordinal.{u})).out) = ℵ_ ω := by
  rw [Cardinal.mk_sigma]
  simp only [Cardinal.mk_out]
  apply le_antisymm
  · calc
      _ ≤ Cardinal.sum (fun _ : ℕ => ℵ_ (ω : Ordinal.{u})) :=
        Cardinal.sum_le_sum _ _ (fun n => (Cardinal.aleph_lt_aleph.mpr (Ordinal.natCast_lt_omega0 n)).le)
      _ = _ := by simp
  · rw [← Ordinal.iSup_natCast, Cardinal.isNormal_aleph.map_iSup Ordinal.bddAbove_of_small]
    apply ciSup_le
    intro i
    simpa using Cardinal.lift_le_sum (fun n : ℕ => ℵ_ (n : Ordinal.{u})) i

end Erdos623Lower
