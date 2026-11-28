import SquareClassification
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.Sum

/-! # Maximum four-cycle packings in balanced complete bipartite graphs

Lean formalization of the balanced case of Lemma 2.2 of E. J. Billington,
H.-L. Fu and C. A. Rodger, "Packing complete multipartite graphs with 4-cycles",
Journal of Combinatorial Designs 9 (2001), 107–127. A classical packing leaves
a set of uncovered edges, represented here by singleton balanced bicliques.
-/

namespace MOBicliquePacking
open OMA.S_mo_341688 Finset

/-- At most ⌊n⌊n/k⌋/k⌋ of the balanced bicliques can have side at least k.
Count tile-row incidences. Each selected tile uses at least k rows, while the
disjoint column sets of the selected tiles in any one row use at least k columns each. -/
theorem incidence_bound {ι : Type} [Fintype ι] {n k : ℕ} (hk : 0 < k) (s : ι → ℕ)
    (D : HasBicliqueDecomposition n s) :
    (univ.filter fun i => k ≤ s i).card ≤ n*(n/k)/k := by
  classical
  obtain ⟨R,C,size,partition⟩ := D
  let T := univ.filter fun i => k ≤ s i
  let rel (i : ι) (a : Fin n) := a ∈ R i
  have perTile (i : ι) (hi : i ∈ T) :
      k ≤ ((univ : Finset (Fin n)).bipartiteAbove rel i).card := by
    have same : (univ : Finset (Fin n)).bipartiteAbove rel i = R i := by
      ext a
      simp [Finset.bipartiteAbove,rel]
    rw [same,(size i).1]
    exact (mem_filter.mp hi).2
  have perRow (a : Fin n) (_ : a ∈ (univ : Finset (Fin n))) :
      (T.bipartiteBelow rel a).card ≤ n/k := by
    let U := T.bipartiteBelow rel a
    have disj : (↑U : Set ι).PairwiseDisjoint C := by
      intro i hi j hj ne
      apply Finset.disjoint_left.mpr
      intro b bi bj
      have ai : a ∈ R i := (mem_filter.mp (show i ∈ T.filter (fun j => a ∈ R j) from hi)).2
      have aj : a ∈ R j := (mem_filter.mp (show j ∈ T.filter (fun u => a ∈ R u) from hj)).2
      obtain ⟨_,_,unique⟩ := partition a b
      exact ne ((unique i ⟨ai,bi⟩).trans (unique j ⟨aj,bj⟩).symm)
    apply (Nat.le_div_iff_mul_le hk).mpr
    calc
      _ = ∑ _i ∈ U, k := by simp [U]
      _ ≤ ∑ i ∈ U, (C i).card := by
        apply sum_le_sum
        intro i hi
        rw [(size i).2]
        have hT : i ∈ T := (mem_filter.mp (show i ∈ T.filter (fun j => a ∈ R j) from hi)).1
        exact (mem_filter.mp hT).2
      _ = (U.biUnion C).card := (card_biUnion disj).symm
      _ ≤ n := by simpa using (U.biUnion C).card_le_univ
  apply (Nat.le_div_iff_mul_le hk).mpr
  simpa [T] using card_mul_le_card_mul rel perTile perRow

end MOBicliquePacking

namespace MOEvenTwos
open OMA.S_mo_341688 Finset

private def twin {t : ℕ} (i : Fin t) : Fin 2 ↪ Fin (t*2) where
  toFun a := finProdFinEquiv (i,a)
  inj' := by
    intro a b h
    exact (Prod.mk.inj (finProdFinEquiv.injective h)).2

private def group {t : ℕ} (i : Fin t) := univ.map (twin i)

private theorem group_iff {t : ℕ} {i : Fin t} {a : Fin (t*2)} :
    a ∈ group i ↔ (finProdFinEquiv.symm a : Fin t × Fin 2).1 = i := by
  constructor
  · intro h
    rcases mem_map.mp h with ⟨b,_,rfl⟩
    exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (i,b))
  · intro h
    obtain ⟨b,hb⟩ := finProdFinEquiv.surjective a
    obtain ⟨j,b⟩ := b
    subst a
    simp only [Equiv.symm_apply_apply] at h
    subst j
    exact mem_map.mpr ⟨b, mem_univ _,rfl⟩

/-- Pair the vertices on each side. Each pair of pairs gives a separate four-cycle. -/
theorem achieve (t : ℕ) :
    HasBicliqueDecomposition (t*2) (fun _ : Fin t × Fin t => 2) := by
  refine ⟨fun i => group i.1, fun i => group i.2, ?_, ?_⟩
  · intro i
    simp [group]
  · intro a b
    let u := (finProdFinEquiv.symm a : Fin t × Fin 2).1
    let v := (finProdFinEquiv.symm b : Fin t × Fin 2).1
    exact ⟨(u,v), ⟨group_iff.mpr rfl, group_iff.mpr rfl⟩,
      fun _ h => Prod.ext (group_iff.mp h.1).symm (group_iff.mp h.2).symm⟩

theorem count (t : ℕ) :
    ((Finset.univ : Finset (Fin t × Fin t)).filter (fun _ => 2 ≤ (2 : ℕ))).card =
      (t*2)*((t*2)/2)/2 := by
  rw [Nat.mul_div_cancel _ (by decide : 0<2), show t*2*t=t*t*2 by ring, Nat.mul_div_cancel _ (by decide : 0<2)]
  simp

end MOEvenTwos

namespace MOTwoPadding

open Finset OMA.S_mo_341688 SquareConverseFamily

abbrev Core (s : ℕ) := Fin (4*s+1)
abbrev Point (s : ℕ) := Core s ⊕ Fin 2
abbrev Wing (s : ℕ) := Fin (2*s) ⊕ Fin 2
abbrev Pieces (s : ℕ) := Tiles s ⊕ (Wing s ⊕ (Wing s ⊕ Unit))

private def pair {s : ℕ} (i : Fin (2*s)) : Finset (Core s) :=
  {⟨2*i.val, by have := i.isLt; omega⟩, ⟨2*i.val+1, by have := i.isLt; omega⟩}

private theorem pair_card {s : ℕ} (i : Fin (2*s)) : (pair i).card = 2 := by
  apply Finset.card_pair
  exact fun h => by have := congrArg Fin.val h; dsimp at this; omega

private def last (s : ℕ) : Core s := ⟨4*s, by omega⟩

private theorem core_cases {s : ℕ} (x : Core s) : x = last s ∨ ∃ i, x ∈ pair i := by
  by_cases h : x.val = 4*s
  · exact Or.inl (Fin.ext h)
  · let i : Fin (2*s) := ⟨x.val/2, by have := x.isLt; omega⟩
    refine Or.inr ⟨i, ?_⟩
    simp only [pair, mem_insert, mem_singleton]
    have : x.val = 2*i.val ∨ x.val = 2*i.val+1 := by dsimp [i]; omega
    exact this.imp Fin.ext Fin.ext

def wingSide {s : ℕ} : Wing s → ℕ := Sum.elim (fun _ => 2) (fun _ => 1)
private def wingCore {s : ℕ} : Wing s → Finset (Core s) :=
  Sum.elim pair (fun _ => {last s})
private def wingNew {s : ℕ} : Wing s → Finset (Fin 2) :=
  Sum.elim (fun _ => univ) (fun x => {x})

private theorem wing_cards {s : ℕ} (i : Wing s) :
    (wingCore i).card = wingSide i ∧ (wingNew i).card = wingSide i := by
  cases i <;> simp [wingCore, wingNew, wingSide, pair_card]

private theorem wing_covers {s : ℕ} (x : Core s) (y : Fin 2) :
    ∃ i : Wing s, x ∈ wingCore i ∧ y ∈ wingNew i := by
  rcases core_cases x with eq | ⟨i,hi⟩
  · exact ⟨.inr y, by simp [wingCore, eq], by simp [wingNew]⟩
  · exact ⟨.inl i, hi, mem_univ _⟩

/-- The old core includes the one-point board when `s = 0`. -/
private theorem core_decomp (s : ℕ) : HasBicliqueDecomposition (4*s+1) (side s) := by
  by_cases h : 0 < s
  · exact biclique s h
  obtain rfl : s=0 := by omega
  let : Subsingleton (Board 0) := ZMod.subsingleton_iff.mpr (by decide)
  refine ⟨fun _ => univ, fun _ => univ, ?_, ?_⟩
  · rintro (⟨_,f⟩ | j)
    · exact Fin.elim0 f
    · simp [side]
  · intro a b
    refine ⟨.inr 0, ⟨mem_univ _,mem_univ _⟩, ?_⟩
    rintro (⟨_,f⟩ | j) _
    · exact Fin.elim0 f
    · exact congrArg Sum.inr (Subsingleton.elim _ _)

def length {s : ℕ} : Pieces s → ℕ :=
  Sum.elim (side s) (Sum.elim wingSide (Sum.elim wingSide (fun _ => 2)))

/-- A rectangular cover with exactly the board's area covers every cell once. -/
private theorem one_cover {ι V : Type} [Fintype ι] [Fintype V] (R C : ι → Finset V)
    (area : (∑ i, (R i).card * (C i).card) = (Fintype.card V)^2)
    (cover : ∀ x y, ∃ i, x ∈ R i ∧ y ∈ C i) : ∀ x y, ∃! i, x ∈ R i ∧ y ∈ C i := by
  classical
  let cell : (Σ i, (R i) × (C i)) → V × V := fun p => (p.2.1.val,p.2.2.val)
  have sur : Function.Surjective cell := by
    rintro ⟨x,y⟩
    obtain ⟨i,hx,hy⟩ := cover x y
    exact ⟨⟨i,⟨x,hx⟩,⟨y,hy⟩⟩,rfl⟩
  have count : Fintype.card (Σ i, (R i) × (C i)) = Fintype.card (V × V) := by
    simpa [sq] using area
  have inj := ((Fintype.bijective_iff_surjective_and_card cell).2 ⟨sur,count⟩).1
  intro x y
  obtain ⟨i,hx,hy⟩ := cover x y
  refine ⟨i,⟨hx,hy⟩,?_⟩
  rintro j ⟨ux,uy⟩
  have eq : (⟨j,⟨x,ux⟩,⟨y,uy⟩⟩ : Σ i, (R i) × (C i)) = ⟨i,⟨x,hx⟩,⟨y,hy⟩⟩ := inj rfl
  exact congrArg Sigma.fst eq

/-- Two wings and a single side-two corner enlarge the cyclic core by two rows
and two columns. The final old row and column use singletons in the wings. -/
theorem decomposition (s : ℕ) : HasBicliqueDecomposition (4*s+3) (@length s) := by
  classical
  obtain ⟨R,C,size,cov⟩ := core_decomp s
  let chart : Point s ≃ Fin (4*s+3) := Fintype.equivFinOfCardEq (by simp [Point, Core])
  let left : Core s ↪ Fin (4*s+3) := Function.Embedding.inl.trans chart.toEmbedding
  let right : Fin 2 ↪ Fin (4*s+3) := Function.Embedding.inr.trans chart.toEmbedding
  let row : Pieces s → Finset (Fin (4*s+3)) := Sum.elim (fun i => (R i).map left)
    (Sum.elim (fun i => (wingCore i).map left)
      (Sum.elim (fun i => (wingNew i).map right) (fun _ => univ.map right)))
  let col : Pieces s → Finset (Fin (4*s+3)) := Sum.elim (fun i => (C i).map left)
    (Sum.elim (fun i => (wingNew i).map right)
      (Sum.elim (fun i => (wingCore i).map left) (fun _ => univ.map right)))
  have dims (i : Pieces s) : (row i).card=length i ∧ (col i).card=length i := by
    rcases i with i | i | i | u
    · simpa [row,col,length] using size i
    · simpa [row,col,length] using wing_cards i
    · simpa [row,col,length] using (wing_cards i).symm
    · simp [row,col,length]
  refine ⟨row,col,dims,one_cover row col ?_ ?_⟩
  · simp_rw [fun i => (dims i).1,fun i => (dims i).2, ←sq]
    simp [Pieces, Tiles, Wing, length, side, wingSide, Fintype.sum_sum_type, Board, ZMod.card]
    ring
  · intro x y
    obtain ⟨a,rfl⟩ := chart.surjective x
    obtain ⟨b,rfl⟩ := chart.surjective y
    rcases a with a|a <;> rcases b with b|b
    · obtain ⟨i,⟨ha,hb⟩,_⟩ := cov a b
      exact ⟨.inl i, mem_map.mpr ⟨a,ha,rfl⟩, mem_map.mpr ⟨b,hb,rfl⟩⟩
    · obtain ⟨i,ha,hb⟩ := wing_covers a b
      exact ⟨.inr (.inl i), mem_map.mpr ⟨a,ha,rfl⟩, mem_map.mpr ⟨b,hb,rfl⟩⟩
    · obtain ⟨i,hb,ha⟩ := wing_covers b a
      exact ⟨.inr (.inr (.inl i)), mem_map.mpr ⟨a,ha,rfl⟩, mem_map.mpr ⟨b,hb,rfl⟩⟩
    · exact ⟨.inr (.inr (.inr ())),mem_map.mpr ⟨a,mem_univ _,rfl⟩,mem_map.mpr ⟨b,mem_univ _,rfl⟩⟩

theorem lengths (s : ℕ) (i : Pieces s) : length i = 1 ∨ length i = 2 := by
  rcases i with (i|i) | (j|j) | (j|j) | u <;> simp [length,side,wingSide]

theorem number_of_twos (s : ℕ) :
    ((univ : Finset (Pieces s)).filter (fun i => length i=2)).card = (2*s+1)^2+s := by
  rw [card_filter]
  simp [Pieces, Wing, Tiles, length, side, wingSide, Fintype.sum_sum_type, Board, ZMod.card]
  ring

/-- A board of order `4s+3` admits a decomposition attaining the row-incidence
upper bound for the number of side-two bicliques, including the 3×3 case. -/
theorem four_mul_add_three (s : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (l : ι → ℕ), (∀ i, l i=1 ∨ l i=2) ∧
      HasBicliqueDecomposition (4*s+3) l ∧
      (univ.filter (fun i => l i=2)).card = (4*s+3)*((4*s+3)/2)/2 := by
  refine ⟨Pieces s, inferInstance, length, lengths s, decomposition s, ?_⟩
  rw [number_of_twos, show (4*s+3)/2 = 2*s+1 by omega]
  have prod : (4*s+3)*(2*s+1) = 2*((2*s+1)^2+s)+1 := by ring
  rw [prod]
  omega

end MOTwoPadding

/-! The four-cycle packing number of a balanced complete bipartite graph.
The formula is classical (Billington, Fu and Rodger, 2001, Lemma 2.2).
Unused edges in any four-cycle packing may be recorded as singleton bicliques. -/
namespace MOBicliquePacking
open OMA.S_mo_341688 Finset SquareConverseFamily

private theorem mod_one (q : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (s : ι → ℕ), (∀ i, s i=1 ∨ s i=2) ∧
      HasBicliqueDecomposition (4*q+1) s ∧
      (univ.filter (fun i => s i=2)).card = (4*q+1)*((4*q+1)/2)/2 := by
  rcases Nat.eq_zero_or_pos q with rfl|hq
  · refine ⟨Fin 1,inferInstance,fun _ => 1,by simp,?_,by decide⟩
    refine ⟨fun _ => {0},fun _ => {0},by decide,?_⟩
    simp only [ExistsUnique]
    decide
  · have sizes (i : Tiles q) : side q i=1 ∨ side q i=2 := by cases i <;> simp [side]
    refine ⟨Tiles q,inferInstance,side q,sizes,biclique q hq,?_⟩
    have eq : (univ.filter (fun i => side q i=2)) = (univ.filter (fun i => 2≤side q i)) := by
      ext i
      simp only [mem_filter,mem_univ,true_and]
      rcases sizes i with h|h <;> omega
    rw [eq,(multiplicities q).1,show (4*q+1)/2=2*q by omega]
    rw [show (4*q+1)*(2*q)=((4*q+1)*q)*2 by ring, Nat.mul_div_cancel _ (by decide : 0<2)]

/-- The largest attainable number of side-two bicliques is exactly
floor(n floor(n/2)/2), and an extremizer uses only sides one and two. -/
theorem four_cycle_maximum (n : ℕ) : IsGreatest
    {m : ℕ | ∃ (ι : Type) (_ : Fintype ι) (s : ι → ℕ), (∀ i, s i=1 ∨ s i=2) ∧
      HasBicliqueDecomposition n s ∧ (univ.filter (fun i => s i=2)).card = m}
    (n*(n/2)/2) := by
  constructor
  · rcases (show n%2=0 ∨ n%4=1 ∨ n%4=3 by omega) with he|h1|h3
    · obtain ⟨t,rfl⟩ : ∃ t, n=t*2 := ⟨n/2, by omega⟩
      exact ⟨Fin t × Fin t,inferInstance,fun _ => 2,by simp,MOEvenTwos.achieve t,
        by simpa using MOEvenTwos.count t⟩
    · obtain ⟨q,rfl⟩ : ∃ q, n=4*q+1 := ⟨n/4,by omega⟩
      exact mod_one q
    · obtain ⟨q,rfl⟩ : ∃ q, n=4*q+3 := ⟨n/4,by omega⟩
      exact MOTwoPadding.four_mul_add_three q
  · rintro m ⟨ι,inst,s,_,D,rfl⟩
    apply le_trans (Finset.card_le_card ?_) (incidence_bound (k:=2) (by decide) s D)
    intro i h
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2.ge⟩

end MOBicliquePacking
