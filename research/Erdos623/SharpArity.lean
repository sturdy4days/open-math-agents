import ErdosHajnalLower
import Mathlib.SetTheory.Cardinal.Arithmetic

/-! Finite free sets for countable-valued maps. This proves the positive
counterpart of the finite-aleph obstruction by adjoining one fresh point
to a free set at the preceding aleph. -/

namespace Erdos623Lower
open Set Cardinal
open scoped Cardinal Ordinal
universe u

private theorem fresh {I X : Type u} [Infinite I]
    (e : I ↪ X) (size : #I < #X) (F : Finset X → Set X) (cnt : ∀ A, (F A).Countable) :
    ∃ x : X, x ∉ Set.range e ∧ ∀ B : Finset I, x ∉ F (B.map e) := by
  let Z : Set X := range e ∪ ⋃ B : Finset I, F (B.map e)
  have small : #(⋃ B : Finset I, F (B.map e)) ≤ #I := by
    calc
      _ ≤ #(Finset I) * ⨆ B : Finset I, #(F (B.map e)) := Cardinal.mk_iUnion_le _
      _ ≤ #(Finset I) * ℵ₀ := by
        gcongr
        exact ciSup_le fun B => Cardinal.le_aleph0_iff_set_countable.mpr (cnt _)
      _ = #I := by rw [Cardinal.mk_finset_of_infinite, Cardinal.mul_aleph0_eq (Cardinal.aleph0_le_mk I)]
  have hZ : #Z ≤ #I := (Cardinal.mk_union_le _ _).trans
    ((add_le_add Cardinal.mk_range_le small).trans_eq (Cardinal.add_eq_self (Cardinal.aleph0_le_mk I)))
  have ex : ∃ x : X, x ∉ Z := by
    by_contra! h
    have he : Z = Set.univ := Set.eq_univ_of_forall h
    rw [he,Cardinal.mk_univ] at hZ
    exact size.not_ge hZ
  obtain ⟨x,hx⟩ := ex
  exact ⟨x,fun h => hx (Or.inl h),fun B h => hx (Or.inr (mem_iUnion_of_mem B h))⟩

private theorem diagonal (n : ℕ) (X : Type u) [DecidableEq X] (size : ℵ_ (n : Ordinal) ≤ #X)
    (F : Finset X → Set X) (cnt : ∀ A, (F A).Countable) :
    ∃ S : Finset X, S.card = n ∧ ∀ y ∈ S, y ∉ F (S.erase y) := by
  classical
  induction n generalizing X with
  | zero => exact ⟨∅, by simp⟩
  | succ n ih =>
    let c := ℵ_ (n : Ordinal.{u})
    let I := c.out
    have hI : #I = c := Cardinal.mk_out _
    have : Infinite I := Cardinal.aleph0_le_mk_iff.mp (hI.symm ▸ Cardinal.aleph0_le_aleph _)
    have less : #I < #X := by
      rw [hI]
      apply lt_of_lt_of_le (b := Order.succ c) (Order.lt_succ c)
      simpa [c,Cardinal.succ_aleph] using size
    obtain ⟨e⟩ := (Cardinal.le_def I X).mp less.le
    obtain ⟨x,hx,hF⟩ := fresh e less F cnt
    let G (B : Finset I) : Set I := e ⁻¹' F (insert x (B.map e))
    obtain ⟨S,hS,free⟩ := ih I hI.ge G (fun B => (cnt _).preimage e.injective)
    have freshS : x ∉ S.map e := fun h => hx (by
      obtain ⟨z,_,rfl⟩ := Finset.mem_map.mp h
      exact Set.mem_range_self z)
    refine ⟨insert x (S.map e), ?_, ?_⟩
    · simp [Finset.card_insert_of_notMem freshS,hS]
    · intro y hy
      obtain rfl | hy := Finset.mem_insert.mp hy
      · simpa [Finset.erase_insert freshS] using hF S
      · obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hy
        have ne : e z ≠ x := fun h => hx ⟨z,h⟩
        have h := free z hz
        change e z ∉ F (insert x ((S.erase z).map e)) at h
        simpa [Finset.erase_insert_of_ne (Ne.symm ne),Finset.map_erase] using h

/-- Some n-set is free for all finite inputs inside it. -/
theorem finite_free (n : ℕ) (X : Type u) (size : ℵ_ (n : Ordinal) ≤ #X)
    (F : Finset X → Set X) (cnt : ∀ A, (F A).Countable) :
    ∃ S : Finset X, S.card = n ∧
      ∀ A : Finset X, A ⊆ S → ∀ y ∈ S, y ∉ A → y ∉ F A := by
  classical
  let G (A : Finset X) : Set X := ⋃ B ∈ (A.powerset : Set (Finset X)), F B
  obtain ⟨S,hS,free⟩ := diagonal n X size G fun A =>
    A.powerset.finite_toSet.countable.biUnion (fun B _ => cnt B)
  refine ⟨S,hS,?_⟩
  intro A sub y hy hn hF
  apply free y hy
  apply Set.mem_iUnion_of_mem A
  have hA : A ∈ (S.erase y).powerset := Finset.mem_powerset.mpr
    (fun x hx => Finset.mem_erase.mpr ⟨fun h => hn (h ▸ hx),sub hx⟩)
  exact Set.mem_iUnion_of_mem hA hF

/-- A bad map catching every (n+1)-set exists exactly below the next aleph. -/
theorem obstruction_iff_cardinal (n : ℕ) (X : Type u) [DecidableEq X] :
    Obstruction X (n+1) ↔ #X < ℵ_ ((n+1 : ℕ) : Ordinal) := by
  constructor
  · rintro ⟨F,cnt,hit⟩
    by_contra! size
    obtain ⟨S,hS,free⟩ := finite_free (n+1) X size F cnt
    obtain ⟨y,hy,bad⟩ := hit S hS
    exact free (S.erase y) (Finset.erase_subset _ _) y hy (Finset.notMem_erase _ _) bad
  · intro size
    have hle : #X ≤ ℵ_ (n : Ordinal) := by
      apply Order.lt_succ_iff.mp
      simpa [Cardinal.succ_aleph] using size
    obtain ⟨e⟩ : Nonempty (X ↪ (ℵ_ (n : Ordinal.{u})).ord.ToType) :=
      (Cardinal.le_def _ _).mp (by simpa using hle)
    exact restrict e (finite_aleph_obstruction n)

/-- The cardinal threshold for guaranteeing a free set of any fixed positive size. -/
theorem finite_free_iff (n : ℕ) (X : Type u) :
    (∀ F : Finset X → Set X, (∀ A, (F A).Countable) →
      ∃ S : Finset X, S.card = n+1 ∧
        ∀ A : Finset X, A ⊆ S → ∀ y ∈ S, y ∉ A → y ∉ F A) ↔
      ℵ_ ((n+1 : ℕ) : Ordinal) ≤ #X := by
  classical
  constructor
  · intro h
    by_contra! size
    obtain ⟨F,cnt,hit⟩ := (obstruction_iff_cardinal n X).mpr size
    obtain ⟨S,hS,free⟩ := h F cnt
    obtain ⟨y,hy,bad⟩ := hit S hS
    exact free (S.erase y) (Finset.erase_subset _ _) y hy (Finset.notMem_erase _ _) bad
  · exact finite_free (n+1) X

end Erdos623Lower

#print axioms Erdos623Lower.finite_free
#print axioms Erdos623Lower.obstruction_iff_cardinal

#print axioms Erdos623Lower.finite_free_iff
