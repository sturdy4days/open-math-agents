import OMAStatements.S_oeis_a388713

/-!
# Distinct representatives for the initial intervals of a partition

Gus Wiseman proposed the interpretation in OEIS A388713. This proof
formalizes Clément Garrot's prefix pigeonhole argument, recorded in A387112
on August 31, 2026. The registered statement is due to @esracummings31-blip.

Sources: https://oeis.org/A388713 and https://oeis.org/A387112.
-/

namespace NestedIntervals
open OMA.S_oeis_a388713

/-- For nested initial intervals, each prefix must fit into its largest interval.
When this holds, its one-based ranks supply distinct representatives. -/
theorem choosable_iff (y : List ℕ) (ordered : y.Pairwise (· ≤ ·)) :
    Choosable y ↔ Superdiagonal y := by
  constructor
  · rintro ⟨z,unique,hz⟩ i
    let index (j : Fin (i.val+1)) : Fin y.length := ⟨j.val,by have := j.isLt; omega⟩
    have below (j : Fin (i.val+1)) : y.get (index j) ≤ y.get i :=
      ordered.rel_get_of_le (by change j.val ≤ i.val; omega)
    let f (j : Fin (i.val+1)) : Fin (y.get i) :=
      ⟨z (index j)-1,by have h := hz (index j); have b := below j; omega⟩
    have inj : Function.Injective f := by
      intro u v eq
      have h := congrArg Fin.val eq
      change z (index u) - 1 = z (index v) - 1 at h
      have eu := (hz (index u)).1
      have ev := (hz (index v)).1
      have eqindex := unique (show z (index u) = z (index v) by omega)
      exact Fin.ext (congrArg (fun t : Fin y.length => t.val) eqindex)
    simpa using Fintype.card_le_of_injective f inj
  · intro h
    refine ⟨fun i => i.val+1, ?_, fun i => ⟨Nat.succ_pos _,h i⟩⟩
    exact fun i j eq => Fin.ext (Nat.succ.inj eq)

/-- Reversing the list only changes the indexing of a system of distinct representatives. -/
theorem choosable_reverse (y : List ℕ) : Choosable y.reverse ↔ Choosable y := by
  have flip (l : List ℕ) (h : Choosable l) : Choosable l.reverse := by
    obtain ⟨z,inj,valid⟩ := h
    let idx (i : Fin l.reverse.length) : Fin l.length := (i.cast l.length_reverse).rev
    refine ⟨fun i => z (idx i),inj.comp (Fin.rev_injective.comp (Fin.cast_injective _)),?_⟩
    intro i
    have eq : l.reverse.get i = l.get (idx i) := by
      simp [List.get_eq_getElem,idx,Fin.rev,Nat.sub_sub,Nat.add_comm]
    rw [eq]
    exact valid (idx i)
  exact ⟨fun h => by simpa using flip y.reverse h,flip y⟩

end NestedIntervals

theorem OMA.solution : type_of% @OMA.S_oeis_a388713.main := by
  intro n k
  unfold OMA.S_oeis_a388713.T
  apply congrArg Nat.card
  congr 1
  funext p
  apply propext
  have sorted : (OMA.S_oeis_a388713.parts n p).reverse.Pairwise (· ≤ ·) :=
    List.pairwise_reverse.mpr (Multiset.pairwise_sort _ _)
  rw [← NestedIntervals.choosable_iff _ sorted,NestedIntervals.choosable_reverse]
