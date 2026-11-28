import OMAStatements.S_mo_341688
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Multiset.Fintype
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # When do balanced biclique partitions imply a square tiling?

For positive integer n, the implication in Aaron Meyerowitz's question holds at
n = 1, 2, 3, 4, 6 and fails at n = 5 and every n ≥ 7. Square positions may be
arbitrary real numbers. The final classification uses the public formalization
of https://mathoverflow.net/questions/341688 by @LDJAI.
The cyclic four-cycle packing of K(5,5) minus a matching is the construction of
Billington, Fu, and Rodger, "Packing complete multipartite graphs with 4-cycles",
Journal of Combinatorial Designs 9 (2001), Lemma 2.1, up to vertex relabeling.
-/

/-! # Twelve by twelve squared-square counterexample

Split twelve coordinates into blocks of sizes 2,3,2,3,2. Assign the consecutive
edges of a 5-cycle to those blocks, giving tile vertex i the coordinates of its
incident edges. Use the complementary 5-cycle for column labels. -/
namespace SquaredTwelve
open OMA.S_mo_341688

def big : Fin 5 → ℕ := ![4, 5, 5, 5, 5]

def row : Fin 5 → Finset (Fin 12) :=
  ![{0, 1, 10, 11}, {0, 1, 2, 3, 4}, {2, 3, 4, 5, 6}, {5, 6, 7, 8, 9}, {7, 8, 9, 10, 11}]

def col : Fin 5 → Finset (Fin 12) :=
  ![{0, 1, 10, 11}, {5, 6, 7, 8, 9}, {0, 1, 2, 3, 4}, {7, 8, 9, 10, 11}, {2, 3, 4, 5, 6}]

def unused (p : Fin 12 × Fin 12) : Prop :=
  ¬ ∃ i : Fin 5, p.1 ∈ row i ∧ p.2 ∈ col i

instance : DecidablePred unused := fun p => inferInstanceAs
  (Decidable (¬ ∃ i : Fin 5, p.1 ∈ row i ∧ p.2 ∈ col i))

abbrev Tile := Fin 5 ⊕ {p : Fin 12 × Fin 12 // unused p}

def side : Tile → ℕ := Sum.elim big (fun _ => 1)
def rows : Tile → Finset (Fin 12) := Sum.elim row (fun p => {p.val.1})
def cols : Tile → Finset (Fin 12) := Sum.elim col (fun p => {p.val.2})

theorem singleton_count :
    Fintype.card {p : Fin 12 × Fin 12 // unused p} = 28 := by decide +kernel

theorem decomposition : HasBicliqueDecomposition 12 side := by
  have sizes : ∀ i : Fin 5, (row i).card = big i ∧ (col i).card = big i := by decide
  have exclusive : ∀ i j : Fin 5, ∀ a b : Fin 12,
      a ∈ row i → a ∈ row j → b ∈ col i → b ∈ col j → i = j := by decide +kernel
  refine ⟨rows, cols, ?_, ?_⟩
  · rintro (i|p)
    · exact sizes i
    · simp [rows,cols,side]
  · intro a b
    by_cases covered : ∃ i : Fin 5, a ∈ row i ∧ b ∈ col i
    · obtain ⟨i, ai, bi⟩ := covered
      refine ⟨.inl i, ⟨ai,bi⟩, ?_⟩
      rintro (j|p) ⟨aj,bj⟩
      · exact congrArg Sum.inl (exclusive j i a b aj ai bj bi)
      · simp [rows,cols] at aj bj
        exact False.elim (p.property ⟨i, aj ▸ ai, bj ▸ bi⟩)
    · let p : {p : Fin 12 × Fin 12 // unused p} := ⟨(a,b),covered⟩
      refine ⟨.inr p, by simp [p,rows,cols], ?_⟩
      rintro (i|q) ⟨ai,bi⟩
      · exact False.elim (covered ⟨i,ai,bi⟩)
      · simp [rows,cols] at ai bi
        exact congrArg Sum.inr (Subtype.ext (Prod.ext ai.symm bi.symm))

private theorem distinct_bins {a b u v : ℝ} (left : 0 ≤ a) (right : b+v ≤ 12)
    (large : 4 ≤ u) (together : 9 ≤ u+v) (apart : a+u ≤ b) :
    decide (a < 4) ≠ decide (b < 4) := by
  have ha : a < 4 := by linarith
  have hb : ¬ b < 4 := by linarith
  simp [ha,hb]

theorem no_tiling : ¬ HasSquareTiling 12 side := by
  rintro ⟨x,y,bounds,apart,_⟩
  let mark (i : Fin 5) := (decide (x (.inl i) < 4), decide (y (.inl i) < 4))
  obtain ⟨i,j,diff,eq⟩ := Fintype.exists_ne_map_eq_of_card_lt mark (by decide)
  have low : ∀ a : Fin 5, 4 ≤ big a := by decide
  have pair : ∀ a b : Fin 5, a ≠ b → 9 ≤ big a + big b := by decide
  have sz (a : Fin 5) : 4 ≤ (side (.inl a) : ℝ) := by exact_mod_cast low a
  have total (a b : Fin 5) (ne : a ≠ b) :
      9 ≤ (side (.inl a) : ℝ) + (side (.inl b) : ℝ) := by exact_mod_cast pair a b ne
  have bx := congrArg Prod.fst eq
  have byy := congrArg Prod.snd eq
  have bi := bounds (.inl i)
  have bj := bounds (.inl j)
  rcases apart (.inl i) (.inl j) (by simpa using diff) with h|h|h|h
  · exact distinct_bins bi.1 bj.2.1 (sz i) (total i j diff) h bx
  · exact distinct_bins bj.1 bi.2.1 (sz j) (total j i diff.symm) h bx.symm
  · exact distinct_bins bi.2.2.1 bj.2.2.2 (sz i) (total i j diff) h byy
  · exact distinct_bins bj.2.2.1 bi.2.2.2 (sz j) (total j i diff.symm) h byy.symm

theorem witness :
    (∀ i, 0 < side i ∧ side i < 12) ∧ (∑ i, (side i)^2) = 12^2 ∧
    HasBicliqueDecomposition 12 side ∧ ¬ HasSquareTiling 12 side := by
  refine ⟨?_,?_,decomposition,no_tiling⟩
  · have valid : ∀ i : Fin 5, 0 < big i ∧ big i < 12 := by decide
    rintro (i|p)
    · exact valid i
    · change 0 < 1 ∧ 1 < 12
      decide
  · decide +kernel

end SquaredTwelve

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

private theorem same_bin {u v : ℝ} (hu : 0≤u) (hv : 0≤v)
    (hu' : u+2≤5) (hv' : v+2≤5)
    (eq : decide (u≤3/2) = decide (v≤3/2)) : ¬ (u+2≤v ∨ v+2≤u) := by
  by_cases a : u≤3/2 <;> by_cases b : v≤3/2 <;> simp_all <;> constructor <;> linarith

theorem five_no_tiling : ¬HasSquareTiling 5 side := by
  classical
  rintro ⟨x,y,bdd,apart,_⟩
  let label (i : Fin 5) := (decide (x (.inl i) ≤ 3/2), decide (y (.inl i) ≤ 3/2))
  obtain ⟨i,j,ne,e⟩ := Fintype.exists_ne_map_eq_of_card_lt label (by decide)
  have bi := bdd (.inl i)
  have bj := bdd (.inl j)
  norm_num [side] at bi bj
  have cx := same_bin bi.1 bj.1 bi.2.1 bj.2.1 (congrArg Prod.fst e)
  have cy := same_bin bi.2.2.1 bj.2.2.1 bi.2.2.2 bj.2.2.2 (congrArg Prod.snd e)
  have sep := apart (.inl i) (.inl j) (by simpa using ne)
  norm_num [side] at sep
  tauto

end SquareConverse

theorem OMA.disproof : ¬(type_of% @OMA.S_mo_341688.main) := by
  intro converse
  apply SquareConverse.five_no_tiling
  exact converse 5 SquareConverse.Tiles SquareConverse.side (by decide) (by decide)
      (by decide) SquareConverse.five_decomposition

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

/-! Five enlarged copies of the cyclic two-by-two construction give a counterexample for every
board side in [5t,6t), with singletons on all unused cells. These intervals contain every n≥25. -/
namespace MOCofinite
open OMA.S_mo_341688 Finset

abbrev Vertex := Fin 5

def twins {n t : ℕ} (fit : 5*t≤n) : Vertex × Fin t ↪ Fin n :=
  finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb fit)

def expand {n t : ℕ} (fit : 5*t≤n) (u : Finset Vertex) : Finset (Fin n) :=
  (u ×ˢ (univ : Finset (Fin t))).map (twins fit)

def row {n t : ℕ} (fit : 5*t≤n) (i : Vertex) := expand fit (SquareConverse.rows (.inl i))
def col {n t : ℕ} (fit : 5*t≤n) (i : Vertex) := expand fit (SquareConverse.cols (.inl i))

def unused {n t : ℕ} (fit : 5*t≤n) (p : Fin n × Fin n) : Prop :=
  ¬ ∃ i : Vertex, p.1 ∈ row fit i ∧ p.2 ∈ col fit i
abbrev Tile {n t : ℕ} (fit : 5*t≤n) := Vertex ⊕ {p // unused fit p}

def side {n t : ℕ} (fit : 5*t≤n) : Tile fit → ℕ := Sum.elim (fun _ => 2*t) (fun _ => 1)
def rows {n t : ℕ} (fit : 5*t≤n) : Tile fit → Finset (Fin n) := Sum.elim (row fit) (fun p => {p.val.1})
def cols {n t : ℕ} (fit : 5*t≤n) : Tile fit → Finset (Fin n) := Sum.elim (col fit) (fun p => {p.val.2})

theorem joint {n t : ℕ} (fit : 5*t≤n) (u v : Finset Vertex) {j : Fin n}
    (hu : j ∈ expand fit u) (hv : j ∈ expand fit v) : ∃ x, x ∈ u ∧ x ∈ v := by
  obtain ⟨a,ha,rfl⟩ := mem_map.mp hu
  obtain ⟨b,hb,eq⟩ := mem_map.mp hv
  have := (twins fit).injective eq
  subst b
  exact ⟨a.1,(mem_product.mp ha).1,(mem_product.mp hb).1⟩

theorem exclusive {n t : ℕ} (fit : 5*t≤n) {i j : Vertex} {a b : Fin n}
    (ai : a ∈ row fit i) (aj : a ∈ row fit j) (bi : b ∈ col fit i) (bj : b ∈ col fit j) : i=j := by
  obtain ⟨x,hxi,hxj⟩ := joint fit _ _ ai aj
  obtain ⟨y,hyi,hyj⟩ := joint fit _ _ bi bj
  have checked : ∀ i j x y : Vertex, x ∈ SquareConverse.rows (.inl i) →
      x ∈ SquareConverse.rows (.inl j) → y ∈ SquareConverse.cols (.inl i) →
      y ∈ SquareConverse.cols (.inl j) → i=j := by decide
  exact checked _ _ _ _ hxi hxj hyi hyj

theorem decomp {n t : ℕ} (fit : 5*t≤n) : HasBicliqueDecomposition n (side fit) := by
  classical
  refine ⟨rows fit,cols fit,?_,?_⟩
  · intro i
    rcases i with i|p
    · have c : ∀ i : Vertex, (SquareConverse.rows (.inl i)).card=2 ∧
          (SquareConverse.cols (.inl i)).card=2 := by decide
      simp [rows,cols,row,col,expand,side,(c i).1,(c i).2]
    · simp [side,rows,cols]
  · intro a b
    by_cases big : ∃ i : Vertex, a∈row fit i ∧ b∈col fit i
    · obtain ⟨i,ai,bi⟩ := big
      refine ⟨.inl i, ⟨ai,bi⟩,?_⟩
      rintro (j|p) ⟨aj,bj⟩
      · exact congrArg Sum.inl (exclusive fit aj ai bj bi)
      · simp [rows,cols] at aj bj
        exact False.elim (p.property ⟨i,aj ▸ ai,bj ▸ bi⟩)
    · let p : {p // unused fit p} := ⟨(a,b),big⟩
      refine ⟨.inr p,by simp [p,rows,cols],?_⟩
      rintro (i|q) ⟨ai,bi⟩
      · exact False.elim (big ⟨i,ai,bi⟩)
      · simp [rows,cols] at ai bi
        exact congrArg Sum.inr (Subtype.ext (Prod.ext ai.symm bi.symm))

theorem no_tiling {n t : ℕ} (ht : 0<t) (low : 5*t≤n) (high : n<6*t) :
    ¬HasSquareTiling n (side low) := by
  classical
  rintro ⟨x,y,b,disjoint,_⟩
  have h := MOPacking.packing_bound (ι:=Vertex) (n:ℝ) ((2*t:ℕ):ℝ)
    (by positivity) (fun i => x (.inl i)) (fun i => y (.inl i))
    (fun i => b (.inl i)) (fun i j ne => disjoint (.inl i) (.inl j) (by simpa using ne))
  rw [Nat.floor_div_natCast, Nat.floor_natCast, Fintype.card_fin] at h
  have cap : n / (2*t) < 3 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
  interval_cases v : n/(2*t) <;> omega

theorem all_large (n : ℕ) (hn : 25≤n) :
    ∃ (ι : Type) (_ : Fintype ι) (s : ι → ℕ),
      (∀ i, 0<s i ∧ s i<n) ∧ HasBicliqueDecomposition n s ∧ ¬ HasSquareTiling n s := by
  classical
  let t := n/5
  have ht : 0<t := by dsimp [t]; omega
  have lo : 5*t≤n := by dsimp [t]; omega
  have hi : n<6*t := by dsimp [t]; omega
  refine ⟨Tile lo,inferInstance,side lo,?_,decomp lo,no_tiling ht lo hi⟩
  rintro (i|p) <;> simp [side] <;> omega

end MOCofinite

/-! Enlarge five disjoint bicliques to an odd side using three extra vertices.
The ordinary vertices come in five groups of q, and three special vertices
belong to groups 0, 2 and 4. Every cyclically adjacent pair contains a
distinguished special vertex. -/
namespace MOUneven
open OMA.S_mo_341688 Finset

abbrev Vertex := Fin 5
abbrev Slot (q : ℕ) := (Vertex × Fin q) ⊕ Fin 3

def adjacent (i : Vertex) : Finset Vertex := {i,i+1}

def special (i : Vertex) : Fin 3 :=
  if i.val = 0 then 0 else if i.val ≤ 2 then 1 else 2

def home (j : Fin 3) : Vertex := ⟨2*j.val, by omega⟩

def owner {q : ℕ} : Slot q → Vertex := Sum.elim Prod.fst home

def groupPair (q : ℕ) (i : Vertex) : Finset (Slot q) :=
  ((adjacent i) ×ˢ (univ : Finset (Fin q))).disjSum {special i}

def sites {n q : ℕ} (fit : 5*q+3≤n) : Slot q ↪ Fin n :=
  ((Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin 3))).trans
    finSumFinEquiv).toEmbedding.trans (Fin.castLEEmb fit)

def expand {n q : ℕ} (fit : 5*q+3≤n) (i : Vertex) : Finset (Fin n) :=
  (groupPair q i).map (sites fit)

theorem card_expand {n q : ℕ} (fit : 5*q+3≤n) (i : Vertex) :
    (expand fit i).card = 2*q+1 := by
  have card : ∀ i : Vertex, (adjacent i).card = 2 := by decide
  simp [expand, groupPair, card]

theorem owner_mem {q : ℕ} {v : Slot q} {i : Vertex} (hv : v ∈ groupPair q i) :
    owner v ∈ adjacent i := by
  have good : ∀ j : Vertex, home (special j) ∈ adjacent j := by decide
  rcases v with p|w
  · exact (Finset.mem_product.mp (Finset.inl_mem_disjSum.mp hv)).1
  · have h : w = special i := Finset.mem_singleton.mp (Finset.inr_mem_disjSum.mp hv)
    subst w
    exact good i

theorem joint {n q : ℕ} (fit : 5*q+3≤n) {i j : Vertex} {a : Fin n}
    (ai : a ∈ expand fit i) (aj : a ∈ expand fit j) : ∃ x, x ∈ adjacent i ∧ x ∈ adjacent j := by
  obtain ⟨p,hp,rfl⟩ := mem_map.mp ai
  obtain ⟨v,hv,eq⟩ := mem_map.mp aj
  have := (sites fit).injective eq
  subst v
  exact ⟨owner p, owner_mem hp, owner_mem hv⟩

theorem exclusive {n q : ℕ} (fit : 5*q+3≤n) {i j : Vertex} {a b : Fin n}
    (ai : a ∈ expand fit i) (aj : a ∈ expand fit j)
    (bi : b ∈ expand fit (2*i)) (bj : b ∈ expand fit (2*j)) : i=j := by
  obtain ⟨x,hxi,hxj⟩ := joint fit ai aj
  obtain ⟨y,hyi,hyj⟩ := joint fit bi bj
  have checked : ∀ i j x y : Vertex, x ∈ adjacent i → x ∈ adjacent j →
      y ∈ adjacent (2*i) → y ∈ adjacent (2*j) → i=j := by decide
  exact checked _ _ _ _ hxi hxj hyi hyj

def unused {n q : ℕ} (fit : 5*q+3≤n) (p : Fin n × Fin n) : Prop :=
  ¬ ∃ i : Vertex, p.1 ∈ expand fit i ∧ p.2 ∈ expand fit (2*i)
abbrev Tile {n q : ℕ} (fit : 5*q+3≤n) := Vertex ⊕ {p // unused fit p}

def side {n q : ℕ} (fit : 5*q+3≤n) : Tile fit → ℕ := Sum.elim (fun _ => 2*q+1) (fun _ => 1)
def rows {n q : ℕ} (fit : 5*q+3≤n) : Tile fit → Finset (Fin n) :=
  Sum.elim (expand fit) (fun p => {p.val.1})
def cols {n q : ℕ} (fit : 5*q+3≤n) : Tile fit → Finset (Fin n) :=
  Sum.elim (fun i => expand fit (2*i)) (fun p => {p.val.2})

theorem decomp {n q : ℕ} (fit : 5*q+3≤n) : HasBicliqueDecomposition n (side fit) := by
  classical
  refine ⟨rows fit,cols fit,?_,?_⟩
  · rintro (i|p) <;> simp [rows,cols,side,card_expand]
  · intro a b
    by_cases big : ∃ i : Vertex, a ∈ expand fit i ∧ b ∈ expand fit (2*i)
    · obtain ⟨i,ai,bi⟩ := big
      refine ⟨.inl i, ⟨ai,bi⟩,?_⟩
      rintro (j|p) ⟨aj,bj⟩
      · exact congrArg Sum.inl (exclusive fit aj ai bj bi)
      · simp [rows,cols] at aj bj
        exact False.elim (p.property ⟨i,aj ▸ ai,bj ▸ bi⟩)
    · let p : {p // unused fit p} := ⟨(a,b),big⟩
      refine ⟨.inr p,by simp [p,rows,cols],?_⟩
      rintro (i|v) ⟨ai,bi⟩
      · exact False.elim (big ⟨i,ai,bi⟩)
      · simp [rows,cols] at ai bi
        exact congrArg Sum.inr (Subtype.ext (Prod.ext ai.symm bi.symm))

theorem no_tiling {n q : ℕ} (fit : 5*q+3≤n) (hi : n<3*(2*q+1)) :
    ¬HasSquareTiling n (side fit) := by
  rintro ⟨x,y,b,disjoint,_⟩
  have h := MOPacking.packing_bound (ι:=Vertex) (n:ℝ) ((2*q+1:ℕ):ℝ)
    (by positivity) (fun i => x (.inl i)) (fun i => y (.inl i))
    (fun i => b (.inl i)) (fun i j ne => disjoint (.inl i) (.inl j) (by simpa using ne))
  rw [Nat.floor_div_natCast, Nat.floor_natCast, Fintype.card_fin] at h
  have cap : n / (2*q+1) < 3 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hi
  interval_cases v : n/(2*q+1) <;> omega

theorem odd_interval (n q : ℕ) (lo : 5*q+3≤n) (hi : n<3*(2*q+1)) :
    ∃ (ι : Type) (_ : Fintype ι) (s : ι → ℕ),
      (∀ i, 0<s i ∧ s i<n) ∧ HasBicliqueDecomposition n s ∧ ¬ HasSquareTiling n s := by
  classical
  refine ⟨Tile lo,inferInstance,side lo,?_,decomp lo,no_tiling lo hi⟩
  rintro (i|p) <;> simp [side] <;> omega

theorem even_interval (n t : ℕ) (ht : 0<t) (lo : 5*t≤n) (hi : n<6*t) :
    ∃ (ι : Type) (_ : Fintype ι) (s : ι → ℕ),
      (∀ i, 0<s i ∧ s i<n) ∧ HasBicliqueDecomposition n s ∧ ¬ HasSquareTiling n s := by
  classical
  refine ⟨MOCofinite.Tile lo,inferInstance,MOCofinite.side lo,?_,
    MOCofinite.decomp lo,MOCofinite.no_tiling ht lo hi⟩
  rintro (i|p) <;> simp [MOCofinite.side] <;> omega

end MOUneven

namespace MOPadding

/-- Counting the cells of each balanced biclique recovers the total tiled area. -/
theorem area_of_decomposition {ι : Type} [Fintype ι] {n : ℕ} {s : ι → ℕ}
    (D : OMA.S_mo_341688.HasBicliqueDecomposition n s) : ∑ i, (s i)^2 = n^2 := by
  classical
  obtain ⟨R,C,size,partition⟩ := D
  let e : (Σ i, (R i) × (C i)) ≃ (Fin n × Fin n) :=
    Equiv.ofBijective (fun p => (p.2.1.val,p.2.2.val)) (by
      constructor
      · rintro ⟨i,⟨a,ha⟩,⟨b,hb⟩⟩ ⟨j,⟨u,hu⟩,⟨v,hv⟩⟩ h
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
        obtain ⟨_,_,uniq⟩ := partition a b
        obtain rfl := (uniq i ⟨ha,hb⟩).trans (uniq j ⟨hu,hv⟩).symm
        rfl
      · rintro ⟨a,b⟩
        obtain ⟨i,⟨ha,hb⟩,_⟩ := partition a b
        exact ⟨⟨i,⟨a,ha⟩,⟨b,hb⟩⟩,rfl⟩)
  have h := Fintype.card_congr e
  simp only [Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,Fintype.card_coe] at h
  simpa only [pow_two,fun i => (size i).1,fun i => (size i).2] using h

end MOPadding

/-! A five-point core with any number of two-point groups gives counterexamples at all odd orders at least five. -/

namespace MOPadding

open OMA.S_mo_341688

def width {h : ℕ} : Option (Fin h) → ℕ
  | none => 5
  | some _ => 2

def count {h : ℕ} : Option (Fin h) → Option (Fin h) → ℕ
  | none, none => 10
  | none, some _ | some _, none => 4
  | some _, some _ => 1

def big {h : ℕ} : Option (Fin h) → Option (Fin h) → ℕ
  | none, none => 5
  | none, some _ | some _, none => 2
  | some _, some _ => 1

abbrev Point (h : ℕ) := Σ i : Option (Fin h), Fin (width i)
abbrev Tile (h : ℕ) := Σ i : Option (Fin h), Σ j : Option (Fin h), Fin (count i j)
abbrev Big (h : ℕ) := Σ i : Option (Fin h), Σ j : Option (Fin h), Fin (big i j)

def length {h : ℕ} (t : Tile h) : ℕ := if t.2.2.val < big t.1 t.2.1 then 2 else 1

def rowTest (leftCore rightCore : Bool) (t x : ℕ) : Bool :=
  match leftCore, rightCore with
  | true,true => if t<5 then x==t || x==(t+1)%5 else x==t-5
  | true,false => if t<2 then x/2==t else x==4
  | false,true => t<2 || x==t-2
  | false,false => true

def colTest (leftCore rightCore : Bool) (t y : ℕ) : Bool :=
  if leftCore && rightCore then
    if t<5 then y==(2*t)%5 || y==(2*t+1)%5 else y==(2*(t-5)+2)%5
  else rowTest rightCore leftCore t y

def rows {h : ℕ} (i j : Option (Fin h)) (t : Fin (count i j)) : Finset (Fin (width i)) :=
  Finset.univ.filter (fun x => rowTest i.isNone j.isNone t.val x.val)

def cols {h : ℕ} (i j : Option (Fin h)) (t : Fin (count i j)) : Finset (Fin (width j)) :=
  Finset.univ.filter (fun y => colTest i.isNone j.isNone t.val y.val)

private theorem local_cards {h : ℕ} (i j : Option (Fin h)) : ∀ t : Fin (count i j),
    (rows i j t).card = length (⟨i,j,t⟩ : Tile h) ∧ (cols i j t).card = length (⟨i,j,t⟩ : Tile h) := by
  cases i <;> cases j
  · exact (show ∀ t : Fin 10, (Finset.univ.filter fun x : Fin 5 => rowTest true true t.val x.val).card=(if t.val < 5 then 2 else 1) ∧ (Finset.univ.filter fun y : Fin 5 => colTest true true t.val y.val).card=(if t.val < 5 then 2 else 1) from by decide)
  · exact (show ∀ t : Fin 4, (Finset.univ.filter fun x : Fin 5 => rowTest true false t.val x.val).card=(if t.val < 2 then 2 else 1) ∧ (Finset.univ.filter fun y : Fin 2 => colTest true false t.val y.val).card=(if t.val < 2 then 2 else 1) from by decide)
  · exact (show ∀ t : Fin 4, (Finset.univ.filter fun x : Fin 2 => rowTest false true t.val x.val).card=(if t.val < 2 then 2 else 1) ∧ (Finset.univ.filter fun y : Fin 5 => colTest false true t.val y.val).card=(if t.val < 2 then 2 else 1) from by decide)
  · exact (show ∀ t : Fin 1, (Finset.univ.filter fun x : Fin 2 => rowTest false false t.val x.val).card=(if t.val < 1 then 2 else 1) ∧ (Finset.univ.filter fun y : Fin 2 => colTest false false t.val y.val).card=(if t.val < 1 then 2 else 1) from by decide)

private theorem local_partition {h : ℕ} (i j : Option (Fin h)) :
    ∀ (x : Fin (width i)) (y : Fin (width j)), ∃! t : Fin (count i j),
      x ∈ rows i j t ∧ y ∈ cols i j t := by
  cases i <;> cases j
  · exact (show ∀ (x:Fin 5) (y:Fin 5), ∃! t : Fin 10, x ∈ (Finset.univ.filter fun x : Fin 5 => rowTest true true t.val x.val) ∧ y ∈ (Finset.univ.filter fun y : Fin 5 => colTest true true t.val y.val) from by unfold ExistsUnique; decide)
  · exact (show ∀ (x:Fin 5) (y:Fin 2), ∃! t : Fin 4, x ∈ (Finset.univ.filter fun x : Fin 5 => rowTest true false t.val x.val) ∧ y ∈ (Finset.univ.filter fun y : Fin 2 => colTest true false t.val y.val) from by unfold ExistsUnique; decide)
  · exact (show ∀ (x:Fin 2) (y:Fin 5), ∃! t : Fin 4, x ∈ (Finset.univ.filter fun x : Fin 2 => rowTest false true t.val x.val) ∧ y ∈ (Finset.univ.filter fun y : Fin 5 => colTest false true t.val y.val) from by unfold ExistsUnique; decide)
  · exact (show ∀ (x:Fin 2) (y:Fin 2), ∃! t : Fin 1, x ∈ (Finset.univ.filter fun x : Fin 2 => rowTest false false t.val x.val) ∧ y ∈ (Finset.univ.filter fun y : Fin 2 => colTest false false t.val y.val) from by unfold ExistsUnique; decide)

private theorem point_card (h : ℕ) : Fintype.card (Point h) = 2*h+5 := by
  let e : Point h ≃ Fin 5 ⊕ (Fin h × Fin 2) :=
    { toFun := fun | ⟨none,z⟩ => .inl z | ⟨some i,z⟩ => .inr (i,z)
      invFun := fun | .inl z => ⟨none,z⟩ | .inr (i,z) => ⟨some i,z⟩
      left_inv := by rintro ⟨_|i,z⟩ <;> rfl
      right_inv := by rintro (z | ⟨i,z⟩) <;> rfl }
  rw [Fintype.card_congr e]
  simp; omega

theorem big_card (h : ℕ) : Fintype.card (Big h) = (h+2)^2+1 := by
  let e : Big h ≃ Fin 5 ⊕ ((Fin h × Fin 2) ⊕ ((Fin h × Fin 2) ⊕ (Fin h × Fin h))) :=
    { toFun := fun
        | ⟨none,none,z⟩ => .inl z
        | ⟨none,some j,z⟩ => .inr (.inl (j,z))
        | ⟨some i,none,z⟩ => .inr (.inr (.inl (i,z)))
        | ⟨some i,some j,_⟩ => .inr (.inr (.inr (i,j)))
      invFun := fun
        | .inl z => ⟨none,none,z⟩
        | .inr (.inl (j,z)) => ⟨none,some j,z⟩
        | .inr (.inr (.inl (i,z))) => ⟨some i,none,z⟩
        | .inr (.inr (.inr (i,j))) => ⟨some i,some j,⟨0,by change 0 < 1; decide⟩⟩
      left_inv := by
        rintro ⟨_|i,_|j,z⟩ <;> try rfl
        have hz : z = (⟨0,by decide⟩ : Fin 1) := Subsingleton.elim (α:=Fin 1) _ _
        subst z
        rfl
      right_inv := by rintro (z | ⟨j,z⟩ | ⟨i,z⟩ | ⟨i,j⟩) <;> rfl }
  rw [Fintype.card_congr e]
  simp; ring

theorem decomposition (h : ℕ) : HasBicliqueDecomposition (2*h+5) (length (h:=h)) := by
  classical
  let chart := Fintype.equivFinOfCardEq (point_card h)
  let loc (i : Option (Fin h)) : Fin (width i) ↪ Fin (2*h+5) :=
    (Function.Embedding.sigmaMk (β:=fun j : Option (Fin h) => Fin (width j)) i).trans chart.toEmbedding
  refine ⟨fun t => (rows t.1 t.2.1 t.2.2).map (loc t.1),
    fun t => (cols t.1 t.2.1 t.2.2).map (loc t.2.1),?_,?_⟩
  · rintro ⟨i,j,t⟩
    simpa only [Finset.card_map] using local_cards i j t
  · intro x y
    obtain ⟨⟨i,a⟩,rfl⟩ := chart.surjective x
    obtain ⟨⟨j,b⟩,rfl⟩ := chart.surjective y
    obtain ⟨t,⟨row,col⟩,unique⟩ := local_partition i j a b
    refine ⟨⟨i,j,t⟩,⟨Finset.mem_map.mpr ⟨a,row,rfl⟩,Finset.mem_map.mpr ⟨b,col,rfl⟩⟩,?_⟩
    rintro ⟨i',j',u⟩ ⟨inrow,incol⟩
    obtain ⟨a',ra,ea⟩ := Finset.mem_map.mp inrow
    obtain ⟨b',cb,eb⟩ := Finset.mem_map.mp incol
    have e₁ : (⟨i',a'⟩ : Point h) = ⟨i,a⟩ := chart.injective ea
    have e₂ : (⟨j',b'⟩ : Point h) = ⟨j,b⟩ := chart.injective eb
    cases e₁
    cases e₂
    rw [unique u ⟨ra,cb⟩]

private theorem slots {h : ℕ} (i j : Option (Fin h)) : big i j ≤ count i j := by
  cases i <;> cases j <;> norm_num [big,count]

/-- There is exactly one more side-two tile than the board can contain. -/
theorem strict_surplus (h : ℕ) :
    ((Finset.univ : Finset (Tile h)).filter fun t => 2 ≤ length t).card = (h+2)^2+1 := by
  classical
  let all := (Finset.univ : Finset (Tile h)).filter (fun i => 2 ≤ length i)
  let emb : (Big h) → all := fun ⟨i,j,t⟩ =>
    ⟨⟨i,j,Fin.castLE (slots i j) t⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [length,t.isLt]⟩⟩
  have inj : Function.Injective emb := by
    rintro ⟨i,j,t⟩ ⟨i',j',v⟩ e
    have first : i=i' := congrArg (fun u => u.val.1) e
    subst i'
    have second : j=j' := congrArg (fun u => u.val.2.1) e
    subst j'
    have tv : t.val=v.val := congrArg (fun u => u.val.2.2.val) e
    rw [Fin.ext tv]
  have sur : Function.Surjective emb := by
    rintro ⟨⟨i,j,t⟩,mem⟩
    have two := (Finset.mem_filter.mp mem).2
    have lt : t.val < big i j := by
      by_contra wrong
      simp [length,wrong] at two
    exact ⟨⟨i,j,⟨t.val,lt⟩⟩,rfl⟩
  have number := Fintype.card_congr (Equiv.ofBijective emb ⟨inj,sur⟩)
  rw [big_card,Fintype.card_coe] at number
  exact number.symm

theorem no_tiling (h : ℕ) : ¬ HasSquareTiling (2*h+5) (length (h:=h)) := by
  intro tiling
  have bound := MOPacking.large_tiles (k:=2) (by decide) tiling
  rw [strict_surplus] at bound
  rw [show (2*h+5)/2=h+2 by omega] at bound
  omega

theorem all_odd {n : ℕ} (five : 5≤n) (odd : Odd n) :
    ∃ (ι : Type) (_ : Fintype ι) (s : ι → ℕ),
      (∀ i, s i = 1 ∨ s i = 2) ∧ (∃ i, s i=1) ∧
      (∀ i, 0 < s i ∧ s i < n) ∧ (∑ i, (s i)^2) = n^2 ∧
      HasBicliqueDecomposition n s ∧ ¬ HasSquareTiling n s := by
  obtain ⟨k,hk⟩ := odd
  let h := k-2
  have eq : n=2*h+5 := by dsimp [h]; omega
  rw [eq]
  refine ⟨Tile h,inferInstance,length,?_,⟨⟨none,none,⟨5,by change 5 < 10; decide⟩⟩,rfl⟩,?_,
    area_of_decomposition (decomposition h),decomposition h,no_tiling h⟩
  · intro i
    by_cases c : i.2.2.val < big i.1 i.2.1 <;> simp [length,c]
  · intro i
    by_cases c : i.2.2.val < big i.1 i.2.1 <;> simp [length,c]
end MOPadding

namespace MOUneven
open OMA.S_mo_341688

/-- A list of proper positive side lengths decomposes the graph but cannot tile the square. -/
abbrev CounterexampleAt (n : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (s : ι → ℕ),
    (∀ i, 0 < s i ∧ s i < n) ∧ HasBicliqueDecomposition n s ∧ ¬ HasSquareTiling n s

/-- The intervals from the five equal or unequal blocks cover eight and every
order from thirteen on. The cofinite estimate handles all orders from 25 on. -/
theorem interval_dispatch
    (odd : ∀ n q : ℕ, 5*q+3 ≤ n → n < 3*(2*q+1) → CounterexampleAt n)
    (even : ∀ n t : ℕ, 0 < t → 5*t ≤ n → n < 6*t → CounterexampleAt n)
    (n : ℕ) (h : n = 8 ∨ 13 ≤ n) : CounterexampleAt n := by
  rcases h with rfl | hn
  · exact odd 8 1 (by decide) (by decide)
  by_cases h14 : n ≤ 14
  · exact odd n 2 (by omega) (by omega)
  by_cases h17 : n ≤ 17
  · exact even n 3 (by decide) (by omega) (by omega)
  by_cases h20 : n ≤ 20
  · exact odd n 3 (by omega) (by omega)
  by_cases h23 : n ≤ 23
  · exact even n 4 (by decide) (by omega) (by omega)
  by_cases h24 : n = 24
  · exact odd n 4 (by omega) (by omega)
  exact MOCofinite.all_large n (by omega)

theorem including_small_orders
    (eight_large : ∀ n : ℕ, n = 8 ∨ 13 ≤ n → CounterexampleAt n)
    (even : ∀ n t : ℕ, 0 < t → 5*t ≤ n → n < 6*t → CounterexampleAt n)
    (n : ℕ) (hn : 5 ≤ n) (h6 : n ≠ 6) (h12 : n ≠ 12) : CounterexampleAt n := by
  by_cases odd : Odd n
  · obtain ⟨ι, inst, s, _, _, sides, _, decomp, obstruct⟩ := MOPadding.all_odd hn odd
    exact ⟨ι, inst, s, sides, decomp, obstruct⟩
  by_cases given : n = 8 ∨ 13 ≤ n
  · exact eight_large n given
  have n10 : n = 10 := by rw [Nat.odd_iff] at odd; omega
  exact even n 2 (by decide) (by omega) (by omega)

end MOUneven

namespace MOUneven
open OMA.S_mo_341688

theorem eight_or_all_from_thirteen (n : ℕ) (h : n = 8 ∨ 13 ≤ n) :
    ∃ (ι : Type) (_ : Fintype ι) (s : ι → ℕ),
      (∀ i, 0 < s i ∧ s i < n) ∧ HasBicliqueDecomposition n s ∧ ¬ HasSquareTiling n s :=
  interval_dispatch odd_interval even_interval n h

theorem all_except_six_twelve (n : ℕ) (hn : 5 ≤ n) (h6 : n ≠ 6) (h12 : n ≠ 12) :
    ∃ (ι : Type) (_ : Fintype ι) (s : ι → ℕ),
      (∀ i, 0 < s i ∧ s i < n) ∧ HasBicliqueDecomposition n s ∧ ¬ HasSquareTiling n s :=
  including_small_orders eight_or_all_from_thirteen even_interval n hn h6 h12

end MOUneven

namespace SquaredTwelve
open OMA.S_mo_341688

/-- Realizability of the prescribed bicliques can fail to imply a square tiling
at every board size from five onwards apart from the order six. -/
theorem all_except_six (n : ℕ) (large : 5 ≤ n) (other : n ≠ 6) :
    ∃ (ι : Type) (_ : Fintype ι) (s : ι → ℕ),
      (∀ i, 0 < s i ∧ s i < n) ∧ (∑ i, (s i)^2) = n^2 ∧
      HasBicliqueDecomposition n s ∧ ¬ HasSquareTiling n s := by
  classical
  by_cases twelve : n = 12
  · subst n
    exact ⟨Tile, inferInstance, side, witness⟩
  · obtain ⟨ι, inst, s, proper, cover, bad⟩ :=
      MOUneven.all_except_six_twelve n large other twelve
    exact ⟨ι, inst, s, proper, MOPadding.area_of_decomposition cover, cover, bad⟩

end SquaredTwelve

namespace SquaredTwelve
open OMA.S_mo_341688

/-- The two small positive results complete the positive-order classification. -/
theorem classify_from_small
    (small : ∀ {n : ℕ}, 0 < n → n ≤ 4 → ∀ {ι : Type} [Fintype ι] (s : ι → ℕ),
      (∀ i, 0 < s i ∧ s i < n) → (∑ i, (s i)^2) = n^2 →
      HasBicliqueDecomposition n s → HasSquareTiling n s)
    (six : ∀ {ι : Type} [Fintype ι] (s : ι → ℕ), (∀ i, 0 < s i ∧ s i < 6) →
      (∑ i, (s i)^2) = 6^2 → HasBicliqueDecomposition 6 s → HasSquareTiling 6 s)
    {n : ℕ} (pos : 0 < n) :
    (∀ {ι : Type} [Fintype ι] (s : ι → ℕ),
      (∀ i, 0 < s i ∧ s i < n) → (∑ i, (s i)^2) = n^2 →
      HasBicliqueDecomposition n s → HasSquareTiling n s) ↔ n ≤ 4 ∨ n = 6 := by
  constructor
  · intro all
    by_contra neg
    have big : 5 ≤ n := by omega
    have other : n ≠ 6 := by omega
    obtain ⟨ι, inst, s, proper, area, partition, impossible⟩ := all_except_six n big other
    exact impossible (all s proper area partition)
  · rintro (h|rfl)
    · exact small pos h
    · exact six

end SquaredTwelve

/-! A finite grid-layout certificate supplies an actual tiling in the closed real square. -/
namespace GridLayout
open OMA.S_mo_341688

/-- Entries are side, horizontal coordinate, and vertical coordinate of the lower-left corner. -/
abbrev Tile := ℕ × ℕ × ℕ

def valid (n : ℕ) (tiles : List Tile) : Bool := decide (
  (∀ i : Fin tiles.length, let (s,x,y) := tiles.get i; x+s ≤ n ∧ y+s ≤ n) ∧
  (∀ i j : Fin tiles.length, i ≠ j →
    let (s,x,y) := tiles.get i
    let (t,u,v) := tiles.get j
    x+s ≤ u ∨ u+t ≤ x ∨ y+s ≤ v ∨ v+t ≤ y) ∧
  (∀ u v : Fin n, ∃ i : Fin tiles.length,
    let (s,x,y) := tiles.get i
    x ≤ u.val ∧ u.val < x+s ∧ y ≤ v.val ∧ v.val < y+s))

private theorem cell {n : ℕ} (hn : 0<n) (a : ℝ) (ha : 0≤a) (h : a≤n) :
    ∃ u : Fin n, (u.val:ℝ) ≤ a ∧ a ≤ (u.val:ℝ)+1 := by
  rcases lt_or_eq_of_le h with hlt|rfl
  · have fl := Nat.floor_le ha
    have : ⌊a⌋₊ < n := by exact_mod_cast fl.trans_lt hlt
    exact ⟨⟨_,this⟩,fl,(Nat.lt_floor_add_one a).le⟩
  · refine ⟨⟨n-1,by omega⟩, ?_, ?_⟩
    · exact_mod_cast (Nat.sub_le n 1)
    · change (n:ℝ) ≤ ((n-1:ℕ):ℝ)+1
      exact_mod_cast (show n ≤ n-1+1 by omega)

private theorem matching_sizes {ι κ : Type} [Fintype ι] [Fintype κ] (s : ι → ℕ) (t : κ → ℕ)
    (same : Finset.univ.val.map s = Finset.univ.val.map t) :
    ∃ e : ι ≃ κ, ∀ i, t (e i) = s i := by
  classical
  have card (k : ℕ) : Fintype.card {i // s i = k} = Fintype.card {j // t j = k} := by
    have h := congrArg (Multiset.count k) same
    simp only [Multiset.count_map, ← Finset.filter_val, ← Finset.card_def] at h
    simpa only [Fintype.card_subtype, eq_comm (a:=k)] using h
  let e := fun k => Fintype.equivOfCardEq (card k)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

theorem tiling {n : ℕ} (hn : 0<n) (tiles : List Tile) (hvalid : valid n tiles = true)
    {ι : Type} [Fintype ι] (s : ι→ℕ)
    (hsizes : Finset.univ.val.map s = (tiles.map Prod.fst : Multiset ℕ)) :
    HasSquareTiling n s := by
  classical
  let t := fun i : Fin tiles.length => (tiles.get i).1
  have same : Finset.univ.val.map s = Finset.univ.val.map t := by
    rw [Fin.univ_val_map]
    have lists : List.ofFn t = tiles.map Prod.fst := by
      change List.ofFn (Prod.fst ∘ tiles.get) = tiles.map Prod.fst
      rw [← List.map_ofFn, List.ofFn_get]
    exact hsizes.trans (congrArg (fun z : List ℕ => (z : Multiset ℕ)) lists.symm)
  obtain ⟨e,he⟩ := matching_sizes s t same
  have checked := of_decide_eq_true hvalid
  let X := fun i : Fin tiles.length => (tiles.get i).2.1
  let Y := fun i : Fin tiles.length => (tiles.get i).2.2
  have bounds (i : Fin tiles.length) : X i+t i≤n ∧ Y i+t i≤n := by
    simpa only [X,Y,t] using checked.1 i
  have apart (i j : Fin tiles.length) (ne : i≠j) :
      X i+t i≤X j ∨ X j+t j≤X i ∨ Y i+t i≤Y j ∨ Y j+t j≤Y i := by
    simpa only [X,Y,t] using checked.2.1 i j ne
  have cover (a b : Fin n) : ∃ i : Fin tiles.length,
      X i≤a.val ∧ a.val<X i+t i ∧ Y i≤b.val ∧ b.val<Y i+t i := by
    simpa only [X,Y,t] using checked.2.2 a b
  refine ⟨fun i => X (e i),fun i => Y (e i),?_,?_,?_⟩
  · intro i
    dsimp only
    rw [← he i]
    exact ⟨by positivity,by exact_mod_cast (bounds (e i)).1,by positivity,
      by exact_mod_cast (bounds (e i)).2⟩
  · intro i j hij
    dsimp only
    rw [← he i,← he j]
    exact_mod_cast apart (e i) (e j) (e.injective.ne hij)
  · intro a b ha0 han hb0 hbn
    obtain ⟨u,hu,hu'⟩ := cell hn a ha0 han
    obtain ⟨v,hv,hv'⟩ := cell hn b hb0 hbn
    obtain ⟨i,hx,hx',hy,hy'⟩ := cover u v
    refine ⟨e.symm i,?_⟩
    dsimp only
    rw [← he, e.apply_symm_apply]
    exact ⟨(by exact_mod_cast hx : (X i:ℝ) ≤ u.val) |>.trans hu,
      hu'.trans (by exact_mod_cast hx' : (u.val:ℝ)+1 ≤ X i+t i),
      (by exact_mod_cast hy : (Y i:ℝ) ≤ v.val) |>.trans hv,
      hv'.trans (by exact_mod_cast hy' : (v.val:ℝ)+1 ≤ Y i+t i)⟩
end GridLayout

namespace MOSix
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000

abbrev Profile := ℕ × ℕ × ℕ × ℕ × ℕ

/-- Multiplicities are listed in ascending order of side length. -/
def positiveProfiles : List Profile :=
  [(36,0,0,0,0),(32,1,0,0,0),(28,2,0,0,0),(24,3,0,0,0),(20,4,0,0,0),(16,5,0,0,0),(12,6,0,0,0),(8,7,0,0,0),(4,8,0,0,0),(0,9,0,0,0),(27,0,1,0,0),(23,1,1,0,0),(19,2,1,0,0),(15,3,1,0,0),(11,4,1,0,0),(7,5,1,0,0),(18,0,2,0,0),(14,1,2,0,0),(10,2,2,0,0),(6,3,2,0,0),(9,0,3,0,0),(5,1,3,0,0),(0,0,4,0,0),(20,0,0,1,0),(16,1,0,1,0),(12,2,0,1,0),(8,3,0,1,0),(4,4,0,1,0),(0,5,0,1,0),(11,0,0,0,1)]

theorem layouts {a b c d e : ℕ} (h : (a,b,c,d,e) ∈ positiveProfiles) :
    ∃ t : List GridLayout.Tile, GridLayout.valid 6 t = true ∧
      (t.map Prod.fst).count 1 = a ∧ (t.map Prod.fst).count 2 = b ∧
      (t.map Prod.fst).count 3 = c ∧ (t.map Prod.fst).count 4 = d ∧
      (t.map Prod.fst).count 5 = e ∧ ∀ k ∈ t.map Prod.fst, 0 < k ∧ k < 6 := by
  simp only [positiveProfiles,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩
  · exact ⟨[(1,0,0),(1,0,1),(1,0,2),(1,0,3),(1,0,4),(1,0,5),(1,1,0),(1,1,1),(1,1,2),(1,1,3),(1,1,4),(1,1,5),(1,2,0),(1,2,1),(1,2,2),(1,2,3),(1,2,4),(1,2,5),(1,3,0),(1,3,1),(1,3,2),(1,3,3),(1,3,4),(1,3,5),(1,4,0),(1,4,1),(1,4,2),(1,4,3),(1,4,4),(1,4,5),(1,5,0),(1,5,1),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(2,0,0),(1,0,2),(1,0,3),(1,0,4),(1,0,5),(1,1,2),(1,1,3),(1,1,4),(1,1,5),(1,2,0),(1,2,1),(1,2,2),(1,2,3),(1,2,4),(1,2,5),(1,3,0),(1,3,1),(1,3,2),(1,3,3),(1,3,4),(1,3,5),(1,4,0),(1,4,1),(1,4,2),(1,4,3),(1,4,4),(1,4,5),(1,5,0),(1,5,1),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(2,0,0),(2,0,2),(1,0,4),(1,0,5),(1,1,4),(1,1,5),(1,2,0),(1,2,1),(1,2,2),(1,2,3),(1,2,4),(1,2,5),(1,3,0),(1,3,1),(1,3,2),(1,3,3),(1,3,4),(1,3,5),(1,4,0),(1,4,1),(1,4,2),(1,4,3),(1,4,4),(1,4,5),(1,5,0),(1,5,1),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(2,0,0),(2,0,2),(2,0,4),(1,2,0),(1,2,1),(1,2,2),(1,2,3),(1,2,4),(1,2,5),(1,3,0),(1,3,1),(1,3,2),(1,3,3),(1,3,4),(1,3,5),(1,4,0),(1,4,1),(1,4,2),(1,4,3),(1,4,4),(1,4,5),(1,5,0),(1,5,1),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(2,0,0),(2,0,2),(2,0,4),(2,2,0),(1,2,2),(1,2,3),(1,2,4),(1,2,5),(1,3,2),(1,3,3),(1,3,4),(1,3,5),(1,4,0),(1,4,1),(1,4,2),(1,4,3),(1,4,4),(1,4,5),(1,5,0),(1,5,1),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(2,0,0),(2,0,2),(2,0,4),(2,2,0),(2,2,2),(1,2,4),(1,2,5),(1,3,4),(1,3,5),(1,4,0),(1,4,1),(1,4,2),(1,4,3),(1,4,4),(1,4,5),(1,5,0),(1,5,1),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(2,0,0),(2,0,2),(2,0,4),(2,2,0),(2,2,2),(2,2,4),(1,4,0),(1,4,1),(1,4,2),(1,4,3),(1,4,4),(1,4,5),(1,5,0),(1,5,1),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(2,0,0),(2,0,2),(2,0,4),(2,2,0),(2,2,2),(2,2,4),(2,4,0),(1,4,2),(1,4,3),(1,4,4),(1,4,5),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(2,0,0),(2,0,2),(2,0,4),(2,2,0),(2,2,2),(2,2,4),(2,4,0),(2,4,2),(1,4,4),(1,4,5),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(2,0,0),(2,0,2),(2,0,4),(2,2,0),(2,2,2),(2,2,4),(2,4,0),(2,4,2),(2,4,4)], by decide⟩
  · exact ⟨[(3,0,0),(1,0,3),(1,0,4),(1,0,5),(1,1,3),(1,1,4),(1,1,5),(1,2,3),(1,2,4),(1,2,5),(1,3,0),(1,3,1),(1,3,2),(1,3,3),(1,3,4),(1,3,5),(1,4,0),(1,4,1),(1,4,2),(1,4,3),(1,4,4),(1,4,5),(1,5,0),(1,5,1),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(3,0,0),(2,0,3),(1,0,5),(1,1,5),(1,2,3),(1,2,4),(1,2,5),(1,3,0),(1,3,1),(1,3,2),(1,3,3),(1,3,4),(1,3,5),(1,4,0),(1,4,1),(1,4,2),(1,4,3),(1,4,4),(1,4,5),(1,5,0),(1,5,1),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(3,0,0),(2,0,3),(2,2,3),(1,0,5),(1,1,5),(1,2,5),(1,3,0),(1,3,1),(1,3,2),(1,3,5),(1,4,0),(1,4,1),(1,4,2),(1,4,3),(1,4,4),(1,4,5),(1,5,0),(1,5,1),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(3,0,0),(2,0,3),(2,2,3),(2,3,0),(1,0,5),(1,1,5),(1,2,5),(1,3,2),(1,3,5),(1,4,2),(1,4,3),(1,4,4),(1,4,5),(1,5,0),(1,5,1),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(3,0,0),(2,0,3),(2,2,3),(2,3,0),(2,4,2),(1,0,5),(1,1,5),(1,2,5),(1,3,2),(1,3,5),(1,4,4),(1,4,5),(1,5,0),(1,5,1),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(3,0,0),(2,0,3),(2,2,3),(2,3,0),(2,4,2),(2,4,4),(1,0,5),(1,1,5),(1,2,5),(1,3,2),(1,3,5),(1,5,0),(1,5,1)], by decide⟩
  · exact ⟨[(3,0,0),(3,0,3),(1,3,0),(1,3,1),(1,3,2),(1,3,3),(1,3,4),(1,3,5),(1,4,0),(1,4,1),(1,4,2),(1,4,3),(1,4,4),(1,4,5),(1,5,0),(1,5,1),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(3,0,0),(3,0,3),(2,3,0),(1,3,2),(1,3,3),(1,3,4),(1,3,5),(1,4,2),(1,4,3),(1,4,4),(1,4,5),(1,5,0),(1,5,1),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(3,0,0),(3,0,3),(2,3,0),(2,3,2),(1,3,4),(1,3,5),(1,4,4),(1,4,5),(1,5,0),(1,5,1),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(3,0,0),(3,0,3),(2,3,0),(2,3,2),(2,3,4),(1,5,0),(1,5,1),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(3,0,0),(3,0,3),(3,3,0),(1,3,3),(1,3,4),(1,3,5),(1,4,3),(1,4,4),(1,4,5),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(3,0,0),(3,0,3),(3,3,0),(2,3,3),(1,3,5),(1,4,5),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(3,0,0),(3,0,3),(3,3,0),(3,3,3)], by decide⟩
  · exact ⟨[(4,0,0),(1,0,4),(1,0,5),(1,1,4),(1,1,5),(1,2,4),(1,2,5),(1,3,4),(1,3,5),(1,4,0),(1,4,1),(1,4,2),(1,4,3),(1,4,4),(1,4,5),(1,5,0),(1,5,1),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(4,0,0),(2,0,4),(1,2,4),(1,2,5),(1,3,4),(1,3,5),(1,4,0),(1,4,1),(1,4,2),(1,4,3),(1,4,4),(1,4,5),(1,5,0),(1,5,1),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(4,0,0),(2,0,4),(2,2,4),(1,4,0),(1,4,1),(1,4,2),(1,4,3),(1,4,4),(1,4,5),(1,5,0),(1,5,1),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(4,0,0),(2,0,4),(2,2,4),(2,4,0),(1,4,2),(1,4,3),(1,4,4),(1,4,5),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(4,0,0),(2,0,4),(2,2,4),(2,4,0),(2,4,2),(1,4,4),(1,4,5),(1,5,4),(1,5,5)], by decide⟩
  · exact ⟨[(4,0,0),(2,0,4),(2,2,4),(2,4,0),(2,4,2),(2,4,4)], by decide⟩
  · exact ⟨[(5,0,0),(1,0,5),(1,1,5),(1,2,5),(1,3,5),(1,4,5),(1,5,0),(1,5,1),(1,5,2),(1,5,3),(1,5,4),(1,5,5)], by decide⟩

end MOSix

namespace MOSixParity
open Finset OMA.S_mo_341688

variable {ι : Type} [Fintype ι] (s : ι → ℕ)
variable (R C : ι → Finset (Fin 6))

/-- Every row is partitioned into strips of lengths given by its incident tiles. -/
private theorem row_degree (sizeC : ∀ i, (C i).card = s i)
    (cover : ∀ x y, ∃! i, x ∈ R i ∧ y ∈ C i) (x : Fin 6) :
    (∑ i, if x ∈ R i then s i else 0) = 6 := by
  classical
  let f (i : ι) := if x ∈ R i then C i else ∅
  have disj : (↑(univ : Finset ι) : Set ι).PairwiseDisjoint f := by
    intro i _ j _ ne
    refine Finset.disjoint_left.mpr ?_
    intro y hi hj
    by_cases xi : x ∈ R i <;> by_cases xj : x ∈ R j <;> simp [f,xi,xj] at hi hj
    obtain ⟨_, _, u⟩ := cover x y
    exact ne ((u i ⟨xi,hi⟩).trans (u j ⟨xj,hj⟩).symm)
  have full : univ.biUnion f = univ := by
    apply Finset.eq_univ_of_forall
    intro y
    obtain ⟨i, ⟨hx,hy⟩, _⟩ := cover x y
    exact mem_biUnion.mpr ⟨i, mem_univ _, by simpa [f,hx] using hy⟩
  have card := congrArg Finset.card full
  rw [card_biUnion disj, card_univ, Fintype.card_fin] at card
  simpa [f, apply_ite Finset.card, sizeC] using card

/-- A row meeting exactly one side-three tile must also meet a singleton. -/
private theorem odd_row (sizes : ∀ i, s i = 1 ∨ s i = 2 ∨ s i = 3)
    (degree : ∀ x, (∑ i, if x ∈ R i then s i else 0) = 6)
    (x : Fin 6) (t : ι) (st : s t = 3) (xt : x ∈ R t)
    (unique : ∀ j, s j = 3 → x ∈ R j → j = t) : ∃ i, s i = 1 ∧ x ∈ R i := by
  classical
  by_contra! no
  have term (i : ι) : (if x ∈ R i then s i else 0) =
      (if i=t then 3 else 0) + 2 * (if x ∈ R i ∧ s i = 2 then 1 else 0) := by
    by_cases it : i=t
    · subst i; simp [st,xt]
    · rcases sizes i with h | h | h
      · simp [h, no i h, it]
      · by_cases p : x ∈ R i <;> simp [h,p,it]
      · have hp : x ∉ R i := fun mem => it (unique i h mem)
        simp [h, hp, it]
  have total := degree x
  simp_rw [term, Finset.sum_add_distrib, ←Finset.mul_sum] at total
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at total
  omega

omit [Fintype ι] in
private theorem size_union (sizeR : ∀ i, (R i).card = s i)
    (family : Finset ι) (k : ℕ) (h : ∀ i ∈ family, s i = k) :
    (family.biUnion R).card ≤ family.card*k := by
  classical
  calc
    _ ≤ ∑ i ∈ family, (R i).card := card_biUnion_le
    _ = ∑ _i ∈ family, k := sum_congr rfl (fun i hi => (sizeR i).trans (h i hi))
    _ = _ := by simp

private theorem one_triple (sizes : ∀ i, s i = 1 ∨ s i = 2 ∨ s i = 3)
    (sizeR : ∀ i, (R i).card = s i)
    (degree : ∀ x, (∑ i, if x ∈ R i then s i else 0) = 6)
    (t : ι) (st : s t = 3) (unique : ∀ i, s i = 3 → i = t)
    (singles : (univ.filter (fun i => s i = 1)).card = 3) :
    (univ.filter (fun i => s i = 1)).biUnion R = R t := by
  classical
  let S := univ.filter (fun i => s i = 1)
  have sub : R t ⊆ S.biUnion R := by
    intro x xt
    obtain ⟨j,hj,xj⟩ := odd_row s R sizes degree x t st xt (fun i h _ => unique i h)
    exact mem_biUnion.mpr ⟨j, by simpa [S], xj⟩
  have bound := size_union s R sizeR S 1 (fun i hi => (mem_filter.mp hi).2)
  have rt : (R t).card = 3 := (sizeR t).trans st
  exact (eq_of_subset_of_card_le sub (by simpa [S, singles, rt] using bound)).symm

private theorem two_triples (sizes : ∀ i, s i = 1 ∨ s i = 2 ∨ s i = 3)
    (sizeR : ∀ i, (R i).card = s i)
    (degree : ∀ x, (∑ i, if x ∈ R i then s i else 0) = 6)
    (t u : ι) (ne : t ≠ u) (st : s t = 3) (su : s u = 3) (apart : Disjoint (R t) (R u)) :
    6 ≤ (univ.filter (fun i => s i = 1)).card +
        3*((univ.filter (fun i => s i = 3)).card-2) := by
  classical
  let S := univ.filter (fun i => s i = 1)
  let T := univ.filter (fun i => s i = 3)
  let extra := (T.erase t).erase u
  have tu : R t ∪ R u = univ := by
    apply eq_univ_of_card
    simp [card_union_of_disjoint apart,sizeR,st,su]
  have covered : univ ⊆ S.biUnion R ∪ extra.biUnion R := by
    intro x _
    by_cases hx : x ∈ extra.biUnion R
    · exact mem_union_right _ hx
    apply mem_union_left
    have only (j : ι) (sj : s j = 3) (xj : x ∈ R j) : j=t ∨ j=u := by
      by_contra! h
      exact hx (mem_biUnion.mpr ⟨j, by simp [extra,T,h,sj], xj⟩)
    have mem : x ∈ R t ∪ R u := by simp [tu]
    have forced : ∃ i, s i = 1 ∧ x ∈ R i := by
      rcases mem_union.mp mem with xt | xu
      · exact odd_row s R sizes degree x t st xt (fun j sj xj =>
          (only j sj xj).resolve_right (fun eq => disjoint_left.mp apart xt (eq ▸ xj)))
      · exact odd_row s R sizes degree x u su xu (fun j sj xj =>
          (only j sj xj).resolve_left (fun eq => disjoint_left.mp apart (eq ▸ xj) xu))
    obtain ⟨j,sj,xj⟩ := forced
    exact mem_biUnion.mpr ⟨j, by simpa [S], xj⟩
  have only_extra (i : ι) (hi : i ∈ extra) : s i = 3 :=
    (mem_filter.mp (mem_of_mem_erase (mem_of_mem_erase hi))).2
  have hs := size_union s R sizeR S 1 (fun i hi => (mem_filter.mp hi).2)
  have he := size_union s R sizeR extra 3 only_extra
  have hu : u ∈ T.erase t := by simp [T, ne.symm, su]
  have ht : t ∈ T := by simp [T, st]
  have ec : extra.card = T.card-2 := by
    dsimp [extra]; rw [card_erase_of_mem hu, card_erase_of_mem ht]; omega
  have total := (card_le_card covered).trans (card_union_le _ _)
  rw [ec] at he
  simp only [card_univ, Fintype.card_fin] at total
  change 6 ≤ S.card + 3*(T.card-2)
  omega

/-- The three residual profiles cannot occur in a biclique decomposition of the
six-by-six board. Only the numbers of singleton and side-three tiles matter. -/
theorem excluded (sizes : ∀ i, s i = 1 ∨ s i = 2 ∨ s i = 3)
    (profile :
      ((univ.filter (fun i => s i = 3)).card = 1 ∧ (univ.filter (fun i => s i = 1)).card = 3) ∨
      ((univ.filter (fun i => s i = 3)).card = 2 ∧ (univ.filter (fun i => s i = 1)).card = 2) ∨
      ((univ.filter (fun i => s i = 3)).card = 3 ∧ (univ.filter (fun i => s i = 1)).card = 1)) :
    ¬ HasBicliqueDecomposition 6 s := by
  classical
  rintro ⟨R,C,sz,cover⟩
  have transposed (x y : Fin 6) : ∃! i, x ∈ C i ∧ y ∈ R i := by
    simpa only [and_comm] using cover y x
  have dr := row_degree s R C (fun i => (sz i).2) cover
  have dc := row_degree s C R (fun i => (sz i).1) transposed
  let S := univ.filter (fun i => s i = 1)
  let T := univ.filter (fun i => s i = 3)
  change (T.card = 1 ∧ S.card = 3) ∨ (T.card = 2 ∧ S.card = 2) ∨
    (T.card = 3 ∧ S.card = 1) at profile
  rcases profile with ⟨singleT,threeS⟩ | many
  · obtain ⟨t,eq⟩ := card_eq_one.mp singleT
    have st : s t = 3 := (mem_filter.mp (show t ∈ T by simp [eq])).2
    have only (j : ι) (sj : s j = 3) : j=t := by
      have hj : j ∈ T := by simp [T,sj]
      simpa [eq] using hj
    have row := one_triple s R sizes (fun j => (sz j).1) dr t st only threeS
    have col := one_triple s C sizes (fun j => (sz j).2) dc t st only threeS
    obtain ⟨j,hj⟩ := card_pos.mp (show 0<S.card by omega)
    have sj : s j = 1 := (mem_filter.mp hj).2
    obtain ⟨x,xj⟩ := card_pos.mp (show 0<(R j).card by rw [(sz j).1,sj]; decide)
    obtain ⟨y,yj⟩ := card_pos.mp (show 0<(C j).card by rw [(sz j).2,sj]; decide)
    have xt : x ∈ R t := row ▸ mem_biUnion.mpr ⟨j,hj,xj⟩
    have yt : y ∈ C t := col ▸ mem_biUnion.mpr ⟨j,hj,yj⟩
    obtain ⟨_,_,u⟩ := cover x y
    obtain rfl := (u j ⟨xj,yj⟩).trans (u t ⟨xt,yt⟩).symm
    omega
  · obtain ⟨t,ht,u,hu,ne⟩ := one_lt_card.mp (show 1<T.card by rcases many with h|h <;> omega)
    have st := (mem_filter.mp ht).2
    have su := (mem_filter.mp hu).2
    have cap : 6 ≤ S.card + 3*(T.card-2) := by
      by_cases disj : Disjoint (R t) (R u)
      · exact two_triples s R sizes (fun j => (sz j).1) dr t u ne st su disj
      · obtain ⟨x,xt,xu⟩ := not_disjoint_iff.mp disj
        have dcol : Disjoint (C t) (C u) := by
          refine disjoint_left.mpr (fun y yt yu => ?_)
          obtain ⟨_,_,v⟩ := cover x y
          exact ne ((v t ⟨xt,yt⟩).trans (v u ⟨xu,yu⟩).symm)
        exact two_triples s C sizes (fun j => (sz j).2) dc t u ne st su dcol
    rcases many with h|h <;> omega

end MOSixParity

namespace MOSmall
open OMA.S_mo_341688

/-- If the sizes of two bicliques exceed the board width in sum, then their
row sets and their column sets overlap, covering a common cell twice. -/
theorem pair_size_le {n : ℕ} {ι : Type} {s : ι → ℕ}
    (D : HasBicliqueDecomposition n s) {i j : ι} (diff : i ≠ j) : s i + s j ≤ n := by
  classical
  obtain ⟨R,C,sizes,part⟩ := D
  by_contra! extra
  have overlap (A B : Finset (Fin n)) (bad : n < A.card+B.card) : ∃ a, a ∈ A ∧ a ∈ B := by
    apply Finset.not_disjoint_iff.mp
    intro disj
    have le : (A∪B).card ≤ n := by simpa using Finset.card_le_univ (A∪B)
    rw [Finset.card_union_of_disjoint disj] at le
    omega
  obtain ⟨a,ai,aj⟩ := overlap (R i) (R j) (by simpa only [fun t => (sizes t).1] using extra)
  obtain ⟨b,bi,bj⟩ := overlap (C i) (C j) (by simpa only [fun t => (sizes t).2] using extra)
  obtain ⟨_,_,unique⟩ := part a b
  exact diff ((unique i ⟨ai,bi⟩).trans (unique j ⟨aj,bj⟩).symm)

end MOSmall

namespace MOSix
open OMA.S_mo_341688

set_option maxHeartbeats 2000000 in
private theorem table : ∀ (b : Fin 10) (c : Fin 5) (d e : Fin 2),
      let used := 4*b.val+9*c.val+16*d.val+25*e.val
      let a := 36-used
      used ≤ 36 → (b.val=0 ∨ e.val=0) → (c.val=0 ∨ e.val=0) →
      (d.val=0 ∨ e.val=0) → (c.val=0 ∨ d.val=0) →
      (d.val=0 → e.val=0 → ¬((c.val=1 ∧ a=3) ∨ (c.val=2 ∧ a=2) ∨ (c.val=3 ∧ a=1))) →
      (a,b.val,c.val,d.val,e.val) ∈ positiveProfiles := by
  intro b c d e
  fin_cases d <;> fin_cases e <;> fin_cases c <;> fin_cases b <;> decide

/-- For a board of side six, every balanced biclique decomposition of the prescribed
proper side lengths has a geometric realization with the same sizes. -/
theorem converse {ι : Type} [Fintype ι] (s : ι → ℕ)
    (bounds : ∀ i, 0<s i ∧ s i<6) (area : ∑ i, (s i)^2 = 6^2)
    (D : HasBicliqueDecomposition 6 s) : HasSquareTiling 6 s := by
  classical
  let count (k : ℕ) := (Finset.univ.filter fun i => s i=k).card
  have coeff (k t : ℕ) : (∑ i, if s i=k then t else 0) = count k * t := by
    rw [← Finset.sum_filter]
    simp [count]
  have area' : count 1 + count 2*4 + count 3*9 + count 4*16 + count 5*25 = 36 := by
    rw [←mul_one (count 1),←coeff,←coeff,←coeff,←coeff,←coeff,
      ←Finset.sum_add_distrib,←Finset.sum_add_distrib,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    calc
      _ = ∑ i, (s i)^2 := Finset.sum_congr rfl fun i _ => by
        have h := bounds i
        rcases (show s i=1 ∨ s i=2 ∨ s i=3 ∨ s i=4 ∨ s i=5 by omega)
          with h|h|h|h|h <;> simp [h]
      _ = 36 := area
  have one (k : ℕ) (too : 6<k+k) : count k ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have a := (Finset.mem_filter.mp hi).2
    have b := (Finset.mem_filter.mp hj).2
    by_contra ne
    have := MOSmall.pair_size_le D ne
    omega
  have mixed (k l : ℕ) (ne : k≠l) (too : 6<k+l) : count k=0 ∨ count l=0 := by
    by_contra! pos
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero pos.1)
    obtain ⟨j,hj⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero pos.2)
    have a := (Finset.mem_filter.mp hi).2
    have b := (Finset.mem_filter.mp hj).2
    have diff : i≠j := by rintro rfl; omega
    have := MOSmall.pair_size_le D diff
    omega
  have parity (d0 : count 4=0) (e0 : count 5=0) :
      ¬((count 3=1 ∧ count 1=3) ∨ (count 3=2 ∧ count 1=2) ∨ (count 3=3 ∧ count 1=1)) := by
    intro h
    apply MOSixParity.excluded s ?_ h D
    intro i
    have absent (k : ℕ) (empty : count k=0) : s i≠k := by
      intro eq
      have : 0 < count k := Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,eq⟩⟩
      omega
    have a := absent 4 d0
    have b := absent 5 e0
    have v := bounds i
    omega
  have d1 := one 4 (by decide)
  have e1 := one 5 (by decide)
  have valid := table ⟨count 2,by omega⟩ ⟨count 3,by omega⟩ ⟨count 4,by omega⟩ ⟨count 5,by omega⟩
  dsimp only at valid
  have aeq : 36-(4*count 2 + 9*count 3 + 16*count 4 + 25*count 5) = count 1 := by omega
  rw [aeq] at valid
  have hp := valid (by omega) (mixed 2 5 (by decide) (by decide))
    (mixed 3 5 (by decide) (by decide)) (mixed 4 5 (by decide) (by decide))
    (mixed 3 4 (by decide) (by decide)) parity
  obtain ⟨t,ok,ha,hb,hc,hd,he,support⟩ := layouts hp
  apply GridLayout.tiling (by decide) t ok s
  ext k
  simp only [Multiset.count_map,← Finset.filter_val,← Finset.card_def,Multiset.coe_count]
  rcases (show k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ (k=0 ∨ 6≤k) by omega)
      with rfl|rfl|rfl|rfl|rfl|rest
  · simpa only [count,eq_comm (a:=1)] using ha.symm
  · simpa only [count,eq_comm (a:=2)] using hb.symm
  · simpa only [count,eq_comm (a:=3)] using hc.symm
  · simpa only [count,eq_comm (a:=4)] using hd.symm
  · simpa only [count,eq_comm (a:=5)] using he.symm
  · have left : (Finset.univ.filter fun i => k=s i).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have eq := (Finset.mem_filter.mp hi).2
      have sz := bounds i
      omega
    have right : k ∉ t.map Prod.fst := by
      intro hk
      have sz := support k hk
      omega
    rw [left,List.count_eq_zero.mpr right]
end MOSix

namespace MOSmall
open OMA.S_mo_341688

/-- Entries give the board side and the counts of sides one, two, and three. -/
def profiles : List (ℕ × ℕ × ℕ × ℕ) :=
  [(2,4,0,0), (3,9,0,0), (3,5,1,0), (4,16,0,0), (4,12,1,0), (4,8,2,0),
   (4,4,3,0), (4,0,4,0), (4,7,0,1)]

private theorem count_classification (n a b c : ℕ) (hn : 0<n) (small : n≤4)
    (area : a+4*b+9*c = n^2) (three : c≤1) (mixed : b=0 ∨ c=0)
    (one : n≤1 → a=0) (two : n≤2 → b=0) (noThree : n≤3 → c=0)
    (fewTwo : n≤3 → b≤1) : (n,a,b,c) ∈ profiles := by
  have bmax : b≤4 := by nlinarith [Nat.mul_self_le_mul_self small]
  interval_cases n <;> interval_cases b <;> interval_cases c <;>
    simp_all (config := {decide := true}) [profiles]

theorem small_profiles {n : ℕ} (hn : 0 < n) (small : n ≤ 4) {ι : Type} [Fintype ι]
    (s : ι → ℕ) (sizes : ∀ i, 0 < s i ∧ s i < n) (area : ∑ i, (s i)^2 = n^2)
    (D : HasBicliqueDecomposition n s) :
    let count := fun k : ℕ => (Finset.univ.filter fun i => s i=k).card
    (n,count 1,count 2,count 3) ∈ profiles := by
  classical
  let count (k : ℕ) := (Finset.univ.filter fun i => s i=k).card
  change (n,count 1,count 2,count 3) ∈ profiles
  have coeff (k t : ℕ) : (∑ i, if s i=k then t else 0) = count k * t := by
    rw [← Finset.sum_filter]
    simp [count]
  have area' : count 1 + count 2 * 4 + count 3 * 9 = n^2 := by
    rw [← mul_one (count 1),← coeff,← coeff,← coeff,← Finset.sum_add_distrib,← Finset.sum_add_distrib,← area]
    apply Finset.sum_congr rfl
    intro i _
    have sz := sizes i
    rcases (show s i=1 ∨ s i=2 ∨ s i=3 by omega) with h|h|h <;> simp [h]
  have one (k : ℕ) (tooLarge : n < k+k) : count k ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ea := (Finset.mem_filter.mp ha).2
    have eb := (Finset.mem_filter.mp hb).2
    by_contra different
    have := pair_size_le D different
    omega
  have absent (k : ℕ) (tooLarge : n ≤ k) : count k = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have eq := (Finset.mem_filter.mp hi).2
    have sz := sizes i
    omega
  have mixed : count 2=0 ∨ count 3=0 := by
    by_contra! nonzero
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero nonzero.1)
    obtain ⟨j,hj⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero nonzero.2)
    have e₂ := (Finset.mem_filter.mp hi).2
    have e₃ := (Finset.mem_filter.mp hj).2
    have ne : i ≠ j := by rintro rfl; omega
    have := pair_size_le D ne
    omega
  apply count_classification n _ _ _ hn small (by simpa only [Nat.mul_comm] using area')
    (one 3 (by omega)) mixed (absent 1) (absent 2) (absent 3) (fun h => one 2 (by omega))

end MOSmall

namespace MOSmall
open OMA.S_mo_341688

/-- Each feasible small profile has an explicit grid layout. -/
private theorem layouts {n a b c : ℕ} (h : (n,a,b,c) ∈ profiles) :
    ∃ t : List GridLayout.Tile, GridLayout.valid n t = true ∧
      (t.map Prod.fst).count 1 = a ∧ (t.map Prod.fst).count 2 = b ∧
      (t.map Prod.fst).count 3 = c ∧ ∀ k ∈ t.map Prod.fst, 0 < k ∧ k ≤ 3 := by
  simp only [profiles,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl⟩
  · exact ⟨[(1,0,0),(1,0,1),(1,1,0),(1,1,1)], by decide⟩
  · exact ⟨[(1,0,0),(1,0,1),(1,0,2),(1,1,0),(1,1,1),(1,1,2),(1,2,0),(1,2,1),(1,2,2)], by decide⟩
  · exact ⟨[(2,0,0),(1,0,2),(1,1,2),(1,2,0),(1,2,1),(1,2,2)], by decide⟩
  · exact ⟨[(1,0,0),(1,0,1),(1,0,2),(1,0,3),(1,1,0),(1,1,1),(1,1,2),(1,1,3),(1,2,0),(1,2,1),(1,2,2),(1,2,3),(1,3,0),(1,3,1),(1,3,2),(1,3,3)], by decide⟩
  · exact ⟨[(2,0,0),(1,0,2),(1,0,3),(1,1,2),(1,1,3),(1,2,0),(1,2,1),(1,2,2),(1,2,3),(1,3,0),(1,3,1),(1,3,2),(1,3,3)], by decide⟩
  · exact ⟨[(2,0,0),(2,2,0),(1,0,2),(1,0,3),(1,1,2),(1,1,3),(1,2,2),(1,2,3),(1,3,2),(1,3,3)], by decide⟩
  · exact ⟨[(2,0,0),(2,2,0),(2,0,2),(1,2,2),(1,2,3),(1,3,2),(1,3,3)], by decide⟩
  · exact ⟨[(2,0,0),(2,2,0),(2,0,2),(2,2,2)], by decide⟩
  · exact ⟨[(3,0,0),(1,0,3),(1,1,3),(1,2,3),(1,3,0),(1,3,1),(1,3,2),(1,3,3)], by decide⟩

theorem converse_of_le_four {n : ℕ} (hn : 0<n) (small : n≤4) {ι : Type} [Fintype ι]
    (s : ι → ℕ) (sizes : ∀ i, 0<s i ∧ s i<n) (area : ∑ i, (s i)^2 = n^2)
    (D : HasBicliqueDecomposition n s) : HasSquareTiling n s := by
  classical
  obtain ⟨t,valid,ha,hb,hc,other⟩ := layouts (small_profiles hn small s sizes area D)
  apply GridLayout.tiling hn t valid s
  ext k
  simp only [Multiset.count_map,← Finset.filter_val,← Finset.card_def,Multiset.coe_count]
  rcases (show k=1 ∨ k=2 ∨ k=3 ∨ (k=0 ∨ 3<k) by omega) with rfl|rfl|rfl|rest
  · simpa only [eq_comm (a:=1)] using ha.symm
  · simpa only [eq_comm (a:=2)] using hb.symm
  · simpa only [eq_comm (a:=3)] using hc.symm
  · have left : (Finset.univ.filter fun i => k=s i).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have eq := (Finset.mem_filter.mp hi).2
      have sz := sizes i
      omega
    have right : k ∉ t.map Prod.fst := by
      intro hk
      have sz := other k hk
      omega
    simp only [left,List.count_eq_zero.mpr right]

end MOSmall

namespace SquaredTwelve
open OMA.S_mo_341688

/-- Positive boards for which every prescribed balanced biclique partition
can be realized by an axis-aligned square tiling. -/
theorem classification {n : ℕ} (positive : 0 < n) :
    (∀ {ι : Type} [Fintype ι] (s : ι → ℕ),
      (∀ i, 0 < s i ∧ s i < n) → (∑ i, (s i)^2) = n^2 →
      HasBicliqueDecomposition n s → HasSquareTiling n s) ↔ n ≤ 4 ∨ n = 6 :=
  classify_from_small (fun hn small => MOSmall.converse_of_le_four hn small)
    MOSix.converse positive

end SquaredTwelve

namespace MOSmall
open OMA.S_mo_341688

/-- Five is the smallest positive board side for which the registered converse fails. -/
theorem least_counterexample : IsLeast
    {n : ℕ | 0 < n ∧ ∃ (ι : Type) (_ : Fintype ι) (s : ι → ℕ),
      (∀ i, 0 < s i ∧ s i < n) ∧ (∑ i, (s i)^2) = n^2 ∧
      HasBicliqueDecomposition n s ∧ ¬ HasSquareTiling n s} 5 := by
  constructor
  · exact ⟨by decide, SquareConverse.Tiles, inferInstance, SquareConverse.side,
      by decide, by decide, SquareConverse.five_decomposition, SquareConverse.five_no_tiling⟩
  · rintro n ⟨hn,ι,inst,s,sz,area,d,failure⟩
    by_contra! small
    exact failure (converse_of_le_four hn (by omega) s sz area d)

end MOSmall

/-! A cyclic family of balanced biclique decompositions of boards of order 4s+1. -/
namespace SquareConverseFamily

abbrev Board (s : ℕ) := ZMod (4 * s + 1)
abbrev Tiles (s : ℕ) := (Board s × Fin s) ⊕ Board s

def side (s : ℕ) : Tiles s → ℕ := Sum.elim (fun _ => 2) (fun _ => 1)

def rows (s : ℕ) : Tiles s → Finset (Board s) :=
  Sum.elim (fun p => {p.1, p.1 + 1}) (fun a => {a})

def cols (s : ℕ) : Tiles s → Finset (Board s) :=
  Sum.elim (fun p =>
    {2 * p.1 + 4 * (p.2.val : Board s), 2 * p.1 + 4 * (p.2.val : Board s) + 1})
    (fun a => {2 * a - 3})

/-- Exactly enough area for the board, as there are ns large and n small tiles. -/
theorem area (s : ℕ) : (∑ i : Tiles s, (side s i)^2) = (4*s+1)^2 := by
  simp [Tiles, side, Fintype.sum_sum_type, Board, ZMod.card]
  ring

theorem side_bounds (s : ℕ) (hs : 0 < s) (i : Tiles s) :
    0 < side s i ∧ side s i < 4*s+1 := by
  cases i <;> simp [side] <;> omega

theorem card_rows_cols (s : ℕ) (hs : 0 < s) (i : Tiles s) :
    (rows s i).card = side s i ∧ (cols s i).card = side s i := by
  let _ : Fact (1 < 4*s+1) := ⟨by omega⟩
  have distinct (x : Board s) : x ≠ x+1 := by
    intro h
    have h' : (1 : Board s) = 0 := by linear_combination -h
    exact one_ne_zero h'
  cases i <;> simp [rows, cols, side, distinct]

/-- Decode a cell by the residue of b+2−2a; the last residue gives a singleton. -/
theorem covers (s : ℕ) (a b : Board s) :
    ∃ i : Tiles s, a ∈ rows s i ∧ b ∈ cols s i := by
  let z : Board s := b + 2 - 2*a
  have hv : z.val < 4*s+1 := ZMod.val_lt z
  have hcast : (z.val : Board s) = z := ZMod.natCast_zmod_val z
  by_cases last : z.val = 4*s
  · have end_at_zero : z + 1 = 0 := by
      rw [← hcast, last]
      simpa only [Nat.cast_add, Nat.cast_one] using ZMod.natCast_self (4*s+1)
    have col : b = 2*a-3 := by
      dsimp [z] at end_at_zero
      linear_combination end_at_zero
    exact ⟨.inr a, by simp [rows], by simp [cols, col]⟩
  · let t : Fin s := ⟨z.val/4, by omega⟩
    have chunks (d : ℕ) (hd : z.val%4 = d) :
        b = 2*a - 2 + 4*(t.val : Board s) + (d : Board s) := by
      have hn : z.val = 4*t.val + d := by dsimp [t]; omega
      have hc := congrArg (fun x : ℕ => (x : Board s)) hn
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hc
      rw [hcast] at hc
      dsimp [z] at hc
      linear_combination hc
    have cases4 : z.val%4=0 ∨ z.val%4=1 ∨ z.val%4=2 ∨ z.val%4=3 := by omega
    rcases cases4 with h | h | h | h
    · refine ⟨.inl (a-1,t), by simp [rows], ?_⟩
      simp only [cols, Sum.elim_inl, Finset.mem_insert, Finset.mem_singleton]
      left
      rw [chunks 0 h]
      push_cast
      ring
    · refine ⟨.inl (a-1,t), by simp [rows], ?_⟩
      simp only [cols, Sum.elim_inl, Finset.mem_insert, Finset.mem_singleton]
      right
      rw [chunks 1 h]
      push_cast
      ring
    · refine ⟨.inl (a,t), by simp [rows], ?_⟩
      simp only [cols, Sum.elim_inl, Finset.mem_insert, Finset.mem_singleton]
      left
      rw [chunks 2 h]
      push_cast
      ring
    · refine ⟨.inl (a,t), by simp [rows], ?_⟩
      simp only [cols, Sum.elim_inl, Finset.mem_insert, Finset.mem_singleton]
      right
      rw [chunks 3 h]
      push_cast
      ring

/-- A cover by Cartesian products of exactly the total area is a partition. -/
private theorem unique_of_area {ι V : Type} [Fintype ι] [Fintype V] (R C : ι → Finset V)
    (count : (∑ i, (R i).card * (C i).card) = Fintype.card V * Fintype.card V)
    (cover : ∀ a b, ∃ i, a ∈ R i ∧ b ∈ C i) :
    ∀ a b, ∃! i, a ∈ R i ∧ b ∈ C i := by
  classical
  let F := Σ i, (↥(R i) × ↥(C i))
  let forget : F → V × V := fun x => (x.2.1.val, x.2.2.val)
  have onto : Function.Surjective forget := by
    rintro ⟨a,b⟩
    obtain ⟨i,ha,hb⟩ := cover a b
    exact ⟨⟨i,⟨a,ha⟩,⟨b,hb⟩⟩, rfl⟩
  have size : Fintype.card F = Fintype.card (V × V) := by simpa [F] using count
  have inj := ((Fintype.bijective_iff_surjective_and_card forget).2 ⟨onto, size⟩).1
  intro a b
  obtain ⟨i,ha,hb⟩ := cover a b
  refine ⟨i,⟨ha,hb⟩,?_⟩
  rintro j ⟨haj,hbj⟩
  have h : (⟨j,⟨a,haj⟩,⟨b,hbj⟩⟩ : F) = ⟨i,⟨a,ha⟩,⟨b,hb⟩⟩ := inj rfl
  exact congrArg Sigma.fst h

/-- For every positive s the cyclic tiles partition K_{4s+1,4s+1}. -/
theorem biclique (s : ℕ) (hs : 0 < s) :
    OMA.S_mo_341688.HasBicliqueDecomposition (4*s+1) (side s) := by
  refine ⟨rows s, cols s, card_rows_cols s hs, unique_of_area (V := Board s) (rows s) (cols s) ?_ (covers s)⟩
  calc
    _ = ∑ i : Tiles s, (side s i)^2 := Finset.sum_congr rfl fun i _ => by
      rw [(card_rows_cols s hs i).1, (card_rows_cols s hs i).2, sq]
    _ = (4*s+1)^2 := area s
    _ = _ := by simp [Board, ZMod.card, sq]

end SquareConverseFamily

namespace SquareConverseFamily

/-- Exact multiplicities of the two side lengths in the cyclic partition. -/
theorem multiplicities (s : ℕ) :
    ((Finset.univ : Finset (Tiles s)).filter fun i => 2 ≤ side s i).card = (4*s+1)*s ∧
    ((Finset.univ : Finset (Tiles s)).filter fun i => side s i = 1).card = 4*s+1 := by
  have large : ((Finset.univ : Finset (Tiles s)).filter fun i => 2 ≤ side s i) =
      (Finset.univ : Finset (Board s × Fin s)).disjSum (∅ : Finset (Board s)) := by
    apply Finset.ext
    intro i
    rw [Finset.mem_filter]
    cases i <;> simp [side]
  have small : ((Finset.univ : Finset (Tiles s)).filter fun i => side s i = 1) =
      (∅ : Finset (Board s × Fin s)).disjSum (Finset.univ : Finset (Board s)) := by
    apply Finset.ext
    intro i
    rw [Finset.mem_filter]
    cases i <;> simp [side]
  rw [large, small]
  simp [Board, ZMod.card]

/-- The family contains exactly s more side-two tiles than any tiling permits. -/
theorem packing_surplus (s : ℕ) :
    ((Finset.univ : Finset (Tiles s)).filter fun i => 2 ≤ side s i).card =
      ((4*s+1)/2)^2 + s := by
  rw [(multiplicities s).1, show (4*s+1)/2 = 2*s by omega]
  ring

/-- The geometric tiling fails even when its squares have arbitrary real coordinates. -/
theorem no_tiling (s : ℕ) (hs : 0 < s) :
    ¬ OMA.S_mo_341688.HasSquareTiling (4*s+1) (side s) := by
  intro tiling
  have bound := MOPacking.large_tiles (k := 2) (by decide) tiling
  rw [packing_surplus] at bound
  omega

theorem counterexample (s : ℕ) (hs : 0 < s) :
    (∀ i, 0 < side s i ∧ side s i < 4*s+1) ∧
    (∑ i : Tiles s, (side s i)^2) = (4*s+1)^2 ∧
    OMA.S_mo_341688.HasBicliqueDecomposition (4*s+1) (side s) ∧
    ¬ OMA.S_mo_341688.HasSquareTiling (4*s+1) (side s) :=
  ⟨side_bounds s hs, area s, biclique s hs, no_tiling s hs⟩

end SquareConverseFamily

namespace MixedSquarePacking
/-- If three of the chosen squares cannot fit end to end, at most four of them can pack. -/
theorem four {ι : Type*} [Fintype ι] (L : ℝ) (s x y : ι → ℝ)
    (pos : ∀ i, 0 < s i)
    (bounds : ∀ i, 0≤x i ∧ x i+s i≤L ∧ 0≤y i ∧ y i+s i≤L)
    (apart : ∀ i j, i≠j → x i+s i≤x j ∨ x j+s j≤x i ∨ y i+s i≤y j ∨ y j+s j≤y i)
    (three : ∀ i j k, i≠j → j≠k → i≠k → L<s i+s j+s k) :
    Fintype.card ι ≤ 4 := by
  classical
  let bit (a : ι→ℝ) (i : ι) := decide (∃ j, a j+s j≤a i)
  have split (a : ι→ℝ) (inside : ∀ i, 0≤a i ∧ a i+s i≤L)
      {i j : ι} (sep : a i+s i≤a j) : bit a i ≠ bit a j := by
    have ij : i ≠ j := by rintro rfl; linarith [pos i]
    have pre : ∃ k, a k+s k≤a j := ⟨i,sep⟩
    have first : ¬∃ k, a k+s k≤a i := by
      rintro ⟨k,hk⟩
      have ki : k≠i := by rintro rfl; linarith [pos k]
      have kj : k≠j := by rintro rfl; linarith [pos i,pos k]
      linarith [three k i j ki ij kj,(inside k).1,(inside j).2]
    simp [bit,pre,first]
  let code (i : ι) := (bit x i,bit y i)
  have inj : Function.Injective code := by
    intro i j eq
    by_contra ne
    rcases apart i j ne with h|h|h|h
    · exact split x (fun v => ⟨(bounds v).1,(bounds v).2.1⟩) h (congrArg Prod.fst eq)
    · exact split x (fun v => ⟨(bounds v).1,(bounds v).2.1⟩) h (congrArg Prod.fst eq.symm)
    · exact split y (fun v => (bounds v).2.2) h (congrArg Prod.snd eq)
    · exact split y (fun v => (bounds v).2.2) h (congrArg Prod.snd eq.symm)
  simpa using Fintype.card_le_of_injective code inj
end MixedSquarePacking
