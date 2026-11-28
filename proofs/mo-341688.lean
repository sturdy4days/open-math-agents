import OMAStatements.S_mo_341688
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic

/-! # A counterexample to the squared-square converse

For Aaron Meyerowitz’s question, the square-area partition 25 = 5·4 + 5·1
admits a balanced biclique decomposition. In a geometric packing the five
lower-left corners of the large squares would each need a different
coordinate bin, but the board has only four. The general bound also allows real tile coordinates.
Source: https://mathoverflow.net/questions/341688
Credit: @sturdy4days
-/

/-! Packing axis-parallel squares with disjoint interiors by counting floor coordinates. -/

namespace MOPacking

/-- A real board of side L contains at most floor(L/s)^2 non-overlapping squares of side s. -/
theorem packing_bound {ι : Type*} [Fintype ι] (L s : ℝ) (hs : 0<s) (x y : ι → ℝ)
    (bounds : ∀ i, 0≤x i ∧ x i+s≤L ∧ 0≤y i ∧ y i+s≤L)
    (apart : ∀ i j, i≠j → x i+s≤x j ∨ x j+s≤x i ∨ y i+s≤y j ∨ y j+s≤y i) :
    Fintype.card ι ≤ ⌊L/s⌋₊^2 := by
  have separated (a b : ℝ) (nonneg : 0≤a) (gap : a+s≤b) : ⌊a/s⌋₊ < ⌊b/s⌋₊ := by
    calc
      ⌊a/s⌋₊ < ⌊a/s⌋₊+1 := Nat.lt_succ_self _
      _ = ⌊(a+s)/s⌋₊ := by rw [add_div,div_self hs.ne',Nat.floor_add_one (div_nonneg nonneg hs.le)]
      _ ≤ ⌊b/s⌋₊ := Nat.floor_mono (div_le_div_of_nonneg_right gap hs.le)
  let cell (i : ι) : Fin ⌊L/s⌋₊ × Fin ⌊L/s⌋₊ :=
    (⟨⌊x i/s⌋₊,separated _ _ (bounds i).1 (bounds i).2.1⟩,
     ⟨⌊y i/s⌋₊,separated _ _ (bounds i).2.2.1 (bounds i).2.2.2⟩)
  have injective : Function.Injective cell := by
    intro i j same
    have col : ⌊x i/s⌋₊=⌊x j/s⌋₊ := congrArg (fun a => (a.1 : Fin ⌊L/s⌋₊).val) same
    have row : ⌊y i/s⌋₊=⌊y j/s⌋₊ := congrArg (fun a => (a.2 : Fin ⌊L/s⌋₊).val) same
    by_contra diff
    rcases apart i j diff with h|h|h|h
    · exact (separated _ _ (bounds i).1 h).ne col
    · exact (separated _ _ (bounds j).1 h).ne col.symm
    · exact (separated _ _ (bounds i).2.2.1 h).ne row
    · exact (separated _ _ (bounds j).2.2.1 h).ne row.symm
  simpa only [Fintype.card_prod,Fintype.card_fin,pow_two] using Fintype.card_le_of_injective cell injective

/-- In a mixed tiling the same bound holds for the number of tiles with side at least k. -/
theorem large_tiles {ι : Type} [Fintype ι] {n k : ℕ} {s : ι → ℕ}
    (hk : 0<k) (tiling : OMA.S_mo_341688.HasSquareTiling n s) :
    ((Finset.univ : Finset ι).filter fun i => k≤s i).card ≤ (n/k)^2 := by
  classical
  obtain ⟨x,y,bounds,apart,_⟩ := tiling
  let T := (Finset.univ : Finset ι).filter fun i => k≤s i
  have sz (i : T) : (k:ℝ)≤s i.val := by exact_mod_cast (Finset.mem_filter.mp i.property).2
  have b (i : T) := bounds i.val
  have result := packing_bound (ι:=T) (n:ℝ) (k:ℝ) (by exact_mod_cast hk)
    (fun i => x i.val) (fun i => y i.val) (fun i =>
      ⟨(b i).1,(add_le_add_right (sz i) _).trans (b i).2.1,(b i).2.2.1,
       (add_le_add_right (sz i) _).trans (b i).2.2.2⟩) (by
        intro i j neq
        rcases apart i.val j.val (fun h => neq (Subtype.ext h)) with h|h|h|h
        · exact Or.inl ((add_le_add_right (sz i) _).trans h)
        · exact Or.inr (Or.inl ((add_le_add_right (sz j) _).trans h))
        · exact Or.inr (Or.inr (Or.inl ((add_le_add_right (sz i) _).trans h)))
        · exact Or.inr (Or.inr (Or.inr ((add_le_add_right (sz j) _).trans h))))
  simpa only [Fintype.card_coe,Nat.floor_div_natCast,Nat.floor_natCast,T] using result

end MOPacking

/-! # A side-five counterexample to the squared-square converse

Five copies of K₂,₂ occupy twenty edges of K₅,₅. Five copies of K₁,₁
complete the decomposition. Five squares of side two cannot pack inside a
square of side five, even with arbitrary real coordinates.
-/
namespace SquareConverse
open OMA.S_mo_341688

abbrev Tiles := Fin 5 ⊕ Fin 5
def side : Tiles → ℕ := Sum.elim (fun _ => 2) (fun _ => 1)

def rows : Tiles → Finset (Fin 5) :=
  Sum.elim (fun i => {i, i+1}) (fun i => {i})
def cols : Tiles → Finset (Fin 5) :=
  Sum.elim (fun i => {2*i, 2*i+1}) (fun i => {2*i+2})

theorem five_decomposition : HasBicliqueDecomposition 5 side :=
  ⟨rows,cols,by decide,by
    simp only [ExistsUnique, Sum.exists, Sum.forall]
    decide⟩

theorem five_no_tiling : ¬HasSquareTiling 5 side := by
  intro tile
  have bound := MOPacking.large_tiles (k:=2) (by decide) tile
  have witness : ((Finset.univ : Finset Tiles).filter (fun i => 2 ≤ side i)).card = 5 := by decide
  rw [witness] at bound
  omega

end SquareConverse

theorem OMA.disproof : ¬(type_of% @OMA.S_mo_341688.main) := by
  intro converse
  apply SquareConverse.five_no_tiling
  exact converse 5 SquareConverse.Tiles SquareConverse.side (by decide) (by decide)
      (by decide) SquareConverse.five_decomposition
