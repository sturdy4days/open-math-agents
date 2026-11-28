import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Countable
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Tactic
import Mathlib.SetTheory.Ordinal.Family

/-! Lower-cardinal obstructions for the free-set principle of Erdős and Hajnal.
The lower-cardinal theorem is P. Erdős and A. Hajnal, *On the structure of
set-mappings* (1958), Theorem 2, pp. 112–115.

An order-k obstruction is a countable-valued map that catches an omitted
element of every k-point set. The successor step labels the initial segment
below the largest vertex by elements of the smaller cardinal. -/

namespace Erdos623Lower
open Set Cardinal
open scoped Cardinal

universe u

def Obstruction (α : Type u) (k : ℕ) [DecidableEq α] : Prop :=
  ∃ F : Finset α → Set α, (∀ A, (F A).Countable) ∧
    ∀ S : Finset α, S.card = k → ∃ y ∈ S, y ∈ F (S.erase y)

theorem countable_base {α : Type u} [DecidableEq α] [Countable α] :
    Obstruction α 1 := by
  refine ⟨fun _ => univ, fun _ => countable_univ, ?_⟩
  intro S h
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  exact ⟨y, hy, trivial⟩

theorem successor {α β : Type u} [LinearOrder α] [DecidableEq β]
    (e : α → α → β) (inj : ∀ z, InjOn (e z) (Iio z))
    (k : ℕ) (hk : Obstruction β k) : Obstruction α (k+1) := by
  classical
  obtain ⟨F, count, hit⟩ := hk
  let cut (z : α) (A : Finset α) := (A.filter (· < z)).image (e z)
  let G (A : Finset α) : Set α :=
    ⋃ z ∈ (A : Set α), {y | y < z ∧ e z y ∈ F (cut z A)}
  refine ⟨G, ?_, ?_⟩
  · intro A
    apply A.finite_toSet.countable.biUnion
    intro z _
    exact Set.MapsTo.countable_of_injOn (f := e z) (fun _ hy => hy.2)
      ((inj z).mono (fun _ hy => hy.1)) (count _)
  · intro S hs
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    let z := S.max' hne
    have hz : z ∈ S := S.max'_mem _
    let R := S.erase z
    have hsmall {x : α} (hx : x ∈ R) : x < z :=
      lt_of_le_of_ne (S.le_max' x (Finset.mem_erase.mp hx).2) (Finset.mem_erase.mp hx).1
    have hrk : (R.image (e z)).card = k := by
      rw [Finset.card_image_of_injOn ((inj z).mono (fun x hx => hsmall hx))]
      dsimp [R]
      rw [Finset.card_erase_of_mem hz]; omega
    obtain ⟨t, ht, hhit⟩ := hit _ hrk
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
    have hyz := hsmall hy
    refine ⟨y, (Finset.mem_erase.mp hy).2, ?_⟩
    apply Set.mem_iUnion_of_mem z
    apply Set.mem_iUnion_of_mem (Finset.mem_erase.mpr ⟨ne_of_gt hyz,hz⟩)
    refine ⟨hyz, ?_⟩
    have heq : cut z (S.erase y) = (R.image (e z)).erase (e z y) := by
      ext b
      constructor
      · intro hb
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
        obtain ⟨hxs,hxz⟩ := Finset.mem_filter.mp hx
        obtain ⟨hxy,hxs⟩ := Finset.mem_erase.mp hxs
        refine Finset.mem_erase.mpr ⟨fun h => hxy (inj z hxz hyz h), ?_⟩
        exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨ne_of_lt hxz,hxs⟩, rfl⟩
      · intro hb
        obtain ⟨hby,hb⟩ := Finset.mem_erase.mp hb
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
        apply Finset.mem_image.mpr
        refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, (Finset.mem_erase.mp hx).2⟩, hsmall hx⟩, rfl⟩
        exact fun h => hby (congrArg (e z) h)
    rwa [heq]

end Erdos623Lower

namespace Erdos623Lower
open Set Cardinal Order
open scoped Cardinal Ordinal
noncomputable section
universe u

/-- A finite obstruction on each finite aleph. -/
theorem finite_aleph_obstruction (n : ℕ) :
    Obstruction (ℵ_ (n : Ordinal.{u})).ord.ToType (n+1) := by
  induction n with
  | zero =>
    have : Countable (ℵ_ ((0 : ℕ) : Ordinal.{u})).ord.ToType :=
      Cardinal.mk_le_aleph0_iff.mp (by simp)
    exact countable_base
  | succ n ih =>
    let c : Cardinal.{u} := ℵ_ (n : Ordinal)
    let d : Cardinal.{u} := ℵ_ ((n+1 : ℕ) : Ordinal)
    have hd : d = Order.succ c := by
      dsimp [d,c]
      rw [Nat.cast_add_one, Cardinal.succ_aleph]
    have : Nonempty c.ord.ToType := Cardinal.nonempty_ord_toType (Cardinal.aleph_pos _).ne'
    have emb (z : d.ord.ToType) : Nonempty (Iio z ↪ c.ord.ToType) := by
      apply (Cardinal.le_def _ _).mp
      rw [Cardinal.mk_ord_toType]
      apply Order.lt_succ_iff.mp
      rw [← hd]
      have h := Cardinal.mk_Iio_lt z (by simp)
      simpa using h
    let maps (z : d.ord.ToType) := (emb z).some
    let e (z x : d.ord.ToType) : c.ord.ToType :=
      if h : x < z then maps z ⟨x,h⟩ else Classical.choice inferInstance
    apply successor e _ (n+1) ih
    intro z x hx y hy he
    change x < z at hx
    change y < z at hy
    simp only [e, dif_pos hx, dif_pos hy] at he
    exact congrArg Subtype.val ((maps z).injective he)

/-- Restrict a finite-set obstruction along an embedding. -/
theorem restrict {α β : Type u} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) {k : ℕ} (h : Obstruction β k) : Obstruction α k := by
  obtain ⟨F, count, hit⟩ := h
  refine ⟨fun A => e ⁻¹' F (A.map e), fun A => (count _).preimage e.injective, ?_⟩
  intro S hS
  obtain ⟨b,hb,hy⟩ := hit (S.map e) (by simpa using hS)
  obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hb
  refine ⟨x,hx,?_⟩
  change e x ∈ F ((S.erase x).map e)
  rwa [Finset.map_erase]

/-- A cardinal strictly below aleph-omega is bounded by some finite aleph. -/
theorem below_aleph_omega {c : Cardinal.{u}} (hc : c < ℵ_ ω) :
    ∃ n : ℕ, c ≤ ℵ_ (n : Ordinal.{u}) := by
  by_contra! hn
  apply hc.not_ge
  rw [← Ordinal.iSup_natCast, Cardinal.isNormal_aleph.map_iSup Ordinal.bddAbove_of_small]
  exact ciSup_le (fun n : ℕ => (hn n).le)

theorem obstruction_below {X : Type u} [DecidableEq X] (hX : #X < ℵ_ ω) :
    ∃ n : ℕ, Obstruction X (n+1) := by
  obtain ⟨n,hn⟩ := below_aleph_omega hX
  obtain ⟨e⟩ : Nonempty (X ↪ (ℵ_ (n : Ordinal.{u})).ord.ToType) :=
    (Cardinal.le_def _ _).mp (by simpa using hn)
  exact ⟨n, restrict e (finite_aleph_obstruction n)⟩

end
end Erdos623Lower

/- A fixed-arity countable obstruction gives a single-valued obstruction by
padding its inputs. Their cardinality records one enumeration index and their
smallest n elements recover the original input. -/

namespace Erdos623Lower
open Set Cardinal
open scoped Cardinal Ordinal
universe u

private def First {X : Type u} [LinearOrder X]
    (n : ℕ) (A : Finset X) (Y : Set X) : Prop :=
  A.card = n ∧ (A : Set X) ⊆ Y ∧ ∀ x ∈ A, ∀ y ∈ Y, y ∉ A → x < y

private theorem first_unique {X : Type u} [LinearOrder X] {n : ℕ}
    {A B : Finset X} {Y : Set X} (ha : First n A Y) (hb : First n B Y) : A = B := by
  by_contra h
  obtain ⟨a,haA,haB⟩ := Finset.not_subset.mp (fun hAB : A ⊆ B =>
    h (Finset.eq_of_subset_of_card_le hAB (hb.1.trans ha.1.symm).le))
  obtain ⟨b,hbB,hbA⟩ := Finset.not_subset.mp (fun hBA : B ⊆ A =>
    h (Finset.eq_of_subset_of_card_le hBA (ha.1.trans hb.1.symm).le).symm)
  exact (ha.2.2 a haA b (hb.2.1 hbB) hbA).not_gt (hb.2.2 b hbB a (ha.2.1 haA) haB)

private theorem first_exists {X : Type u} [LinearOrder X] [WellFoundedLT X]
    (Y : Set X) (hY : Y.Infinite) (n : ℕ) : ∃ A, First n A Y := by
  classical
  induction n with
  | zero => exact ⟨∅, by simp [First]⟩
  | succ n ih =>
    obtain ⟨A,hA⟩ := ih
    have ht : (Y \ (A : Set X)).Nonempty := (hY.sdiff A.finite_toSet).nonempty
    let m := wellFounded_lt.min (Y \ (A : Set X)) ht
    have hm : m ∈ Y \ (A : Set X) := wellFounded_lt.min_mem _ ht
    refine ⟨insert m A, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hm.2, hA.1]
    · intro x hx
      obtain rfl | hx := Finset.mem_insert.mp hx
      · exact hm.1
      · exact hA.2.1 hx
    · intro x hx y hy hyA
      have hy' : y ∈ Y \ (A : Set X) := ⟨hy, fun hy₁ => hyA (Finset.mem_insert_of_mem hy₁)⟩
      obtain rfl | hx := Finset.mem_insert.mp hx
      · exact lt_of_le_of_ne (wellFounded_lt.min_le hy') (fun eq => hyA (eq ▸ Finset.mem_insert_self _ _))
      · exact hA.2.2 x hx y hy hy'.2

/-- Recover a single-valued input-avoiding map from a fixed-arity countable
obstruction. Each infinite set supplies the initial n+1 points and as many
later padding points as the relevant countable code requires. -/
theorem singleton_of_obstruction {X : Type u} [LinearOrder X] [WellFoundedLT X] [Infinite X]
    (n : ℕ) (bad : Obstruction X (n+1)) :
    ∃ f : Finset X → X, (∀ A, f A ∉ A) ∧
      ∀ Y : Set X, Y.Infinite → ∃ A : Finset X, (A : Set X) ⊆ Y ∧ f A ∈ Y := by
  classical
  obtain ⟨F,count,capture⟩ := bad
  choose code inj using fun A => countable_iff_exists_injOn.mp (count A)
  let W (B : Finset X) (y : X) : Prop := y ∉ B ∧
    ∃ A : Finset X, First n A (B : Set X) ∧ y ∈ F A ∧ code A y = B.card - n
  have unique {B : Finset X} {x y : X} (hx : W B x) (hy : W B y) : x = y := by
    obtain ⟨_,A,ha,hx,hcx⟩ := hx
    obtain ⟨_,A',ha',hy,hcy⟩ := hy
    obtain rfl := first_unique ha ha'
    exact inj A hx hy (hcx.trans hcy.symm)
  have outside (B : Finset X) : ∃ x : X, x ∉ B := by
    obtain ⟨x,hx⟩ := (Set.infinite_univ.sdiff B.finite_toSet).nonempty
    exact ⟨x,hx.2⟩
  let f (B : Finset X) := if h : ∃ x, W B x then h.choose else (outside B).choose
  refine ⟨f, ?_, ?_⟩
  · intro A
    dsimp [f]
    split
    · next h => exact h.choose_spec.1
    · exact (outside A).choose_spec
  · intro Y inf
    obtain ⟨S,hS⟩ := first_exists Y inf (n+1)
    obtain ⟨y,hy,hit⟩ := capture S hS.1
    let A := S.erase y
    have hak : A.card = n := by
      dsimp [A]
      rw [Finset.card_erase_of_mem hy,hS.1]
      omega
    obtain ⟨D,hD,kD⟩ := (inf.sdiff S.finite_toSet).exists_subset_card_eq (code A y)
    have dis : Disjoint A D := Finset.disjoint_left.mpr fun x hx hd =>
      (hD hd).2 (Finset.mem_of_mem_erase hx)
    let B := A ∪ D
    have eqn : B.card - n = code A y := by
      simp [B, Finset.card_union_of_disjoint dis, hak,kD]
    have pre : First n A (B : Set X) := by
      refine ⟨hak, fun _ hx => Finset.mem_union_left _ hx, ?_⟩
      intro x hx z hz hn
      obtain hz | hz := Finset.mem_union.mp hz
      · contradiction
      · exact hS.2.2 x (Finset.mem_of_mem_erase hx) z (hD hz).1 (hD hz).2
    have hW : W B y := by
      refine ⟨?_, A,pre,hit,eqn.symm⟩
      intro h
      obtain hh | hh := Finset.mem_union.mp h
      · exact (Finset.notMem_erase y S) hh
      · exact (hD hh).2 hy
    have existsW : ∃ x, W B x := ⟨y,hW⟩
    have heq : f B = y := by
      dsimp [f]
      rw [dif_pos existsW]
      exact unique existsW.choose_spec hW
    refine ⟨B, ?_, heq ▸ hS.2.1 hy⟩
    intro x hx
    obtain hx | hx := Finset.mem_union.mp hx
    · exact hS.2.1 (Finset.mem_of_mem_erase hx)
    · exact (hD hx).1

/-- The negative result for every infinite cardinal below aleph-omega,
in the same single-output language as Erdős Problem 623. -/
theorem bad_map_below_aleph_omega (X : Type u) [Infinite X] (hX : #X < ℵ_ ω) :
    ∃ f : Finset X → X, (∀ A, f A ∉ A) ∧
      ∀ Y : Set X, Y.Infinite → ∃ A : Finset X, (A : Set X) ⊆ Y ∧ f A ∈ Y := by
  classical
  let : LinearOrder X := linearOrderOfSTO (@WellOrderingRel X)
  have : IsWellOrder X (· < ·) := WellOrderingRel.isWellOrder
  obtain ⟨n,bad⟩ := obstruction_below hX
  exact singleton_of_obstruction n bad

end Erdos623Lower
