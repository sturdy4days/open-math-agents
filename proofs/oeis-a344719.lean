import OMAStatements.S_oeis_a344719

/-!
# A344719: the minimum size of an exact two-neighbor painting

Dmitry Kamenetsky introduced the sequence. Shinji Oda conjectured the exact
formula and the existence of striped minimizers, and exhibited an extendible
family proving the upper bound (OEIS A344719, October 4, 2026).
The registered Lean statement first appeared in commit 516383ffa17e.
Here the initial stripe templates of sides 13, 14, 15 are checked directly.
Their central bands can be duplicated to give all larger side lengths.

The lower bound counts unused incidences along the four sides of the board.
The loss method for ordinary 2-domination of grids is due to Michaël Rao
and Alexandre Talon (DMTCS 21:1, 2019, no. 9, doi:10.23638/dmtcs-21-1-9).
For exact two-neighbor paintings the width-six certificates below check
the transfer inequalities including the corner terms, and the four corner
pairs have constant total charge. The file contains all the numerical
witnesses and checks used in the proof.
-/

section

/-! The proposed generating series for A344719 uniquely encodes the seven
initial values and the ceiling formula. The geometric optimization problem is
concentrated in those exact values and the striped witnesses. -/

namespace OMA.A344719Series
open PowerSeries

/-- Coefficient sequence specified by the conjectured series. -/
def target (n : ℕ) : ℕ :=
  if n < 7 then [0,1,2,5,8,11,17][n]! else ((n+2)^2+2)/3-6

private noncomputable def den : PowerSeries ℤ := (1-X)^3 * (1+X+X^2)
private noncomputable def num : PowerSeries ℤ := X * (1+2*X^2-X^3+X^5-2*X^6+3*X^7-3*X^8+2*X^9-X^10)

def Formula (f : ℕ → ℕ) : Prop := den * PowerSeries.mk (fun n => (f n : ℤ)) = num

private theorem add_three (n : ℕ) (hn : 7 ≤ n) : target (n+3) = target n + 2*n+7 := by
  have h₁ : (n+3+2)^2+2 = (n+2)^2+2+(2*n+7)*3 := by ring
  have h₂ : (n+2)^2 ≥ 64 := by nlinarith [Nat.zero_le ((n-7)*(n-7))]
  simp only [target, if_neg (by omega : ¬n+3 < 7), if_neg (by omega : ¬n < 7), h₁,
    Nat.add_mul_div_right _ _ (by decide : 0 < 3)]
  omega

private theorem den_apply (s : PowerSeries ℤ) : den*s =
    s-X^1*s-X^1*s+X^2*s-X^3*s+X^4*s+X^4*s-X^5*s := by unfold den; ring

private theorem num_expand : num = ((X^1 + X^3 + X^3 - X^4 + X^6 - X^7 - X^7
    + X^8 + X^8 + X^8 - X^9 - X^9 - X^9 + X^10 + X^10 - X^11) : PowerSeries ℤ) := by
  unfold num; ring

theorem series_target : Formula target := by
  unfold Formula
  ext n
  rw [den_apply, num_expand]
  simp only [map_add, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  by_cases small : n < 12
  · interval_cases n <;> norm_num [target]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m+5 := ⟨n-5, by omega⟩
    have h₁ := add_three m (by omega)
    have h₂ := add_three (m+1) (by omega)
    have h₃ := add_three (m+2) (by omega)
    rw [show m+1+3=m+4 by omega] at h₂
    rw [show m+2+3=m+5 by omega] at h₃
    simp (disch := omega) only [if_pos, if_neg,
      show m+5-1=m+4 by omega, show m+5-2=m+3 by omega, show m+5-3=m+2 by omega,
      show m+5-4=m+1 by omega, show m+5-5=m by omega]
    omega

/-- The generating function is equivalent to term-by-term equality, in both
directions and without any enumeration of paintings. -/
theorem formula_iff (f : ℕ → ℕ) : Formula f ↔ ∀ n, f n = target n := by
  constructor
  · intro hf n
    have hden : den ≠ 0 := by
      intro hh
      have h := congrArg PowerSeries.constantCoeff hh
      norm_num [den] at h
    have he := mul_left_cancel₀ hden (hf.trans series_target.symm)
    have h := congrArg (PowerSeries.coeff (R := ℤ) n) he
    simpa using h
  · intro hf
    rw [show f = target from funext hf]
    exact series_target

end OMA.A344719Series

/-! An exact reduction of the three conjunctions in the registered A344719
conjecture to striped optimality, the seven initial values and the tail formula. -/

namespace OMA.A344719Series
open OMA.S_oeis_a344719

def StripedOptimal : Prop := ∀ n : ℕ, 6 ≤ n → ∃ painted : Finset (Cell n),
  Fair painted ∧ Striped painted ∧ painted.card = a n

def InitialValues : Prop := ∀ n : Fin 7, a n = [0,1,2,5,8,11,17][n.val]!

def TailValues : Prop := ∀ n : ℕ, 7 ≤ n → a n = ((n+2)^2+2)/3-6

/-- The formal power-series identity by itself forces the entire numerical
claim, including seven initial coefficients that are absent from the tail. -/
theorem series_iff_initial_and_tail : Formula a ↔ InitialValues ∧ TailValues := by
  rw [formula_iff]
  constructor
  · intro h
    constructor
    · intro n
      simpa only [target, if_pos n.isLt] using h n
    · intro n hn
      simpa only [target, if_neg (by omega : ¬n < 7)] using h n
  · rintro ⟨hi, ht⟩ n
    by_cases hn : n < 7
    · simpa only [target, if_pos hn] using hi ⟨n,hn⟩
    · simpa only [target, if_neg hn] using ht n (by omega)

/-- Exact equivalence with the project statement. -/
theorem original_iff : (type_of% @OMA.S_oeis_a344719.main) ↔
    StripedOptimal ∧ InitialValues ∧ TailValues := by
  constructor
  · rintro ⟨hs, _, hf⟩
    exact ⟨hs, series_iff_initial_and_tail.mp hf⟩
  · rintro ⟨hs, hi, ht⟩
    exact ⟨hs, ht, series_iff_initial_and_tail.mpr ⟨hi, ht⟩⟩

end OMA.A344719Series

end

section

/-! Reduce the registered painting problem to its sharp lower bound once the
striped constructions and the small finite optima have been verified. -/

namespace OMA.A344719Series
open OMA.S_oeis_a344719

def BoundaryLower : Prop := ∀ n : ℕ, 7 ≤ n → ∀ P : Finset (Cell n),
  Fair P → n^2+4*n ≤ 3*P.card+14

/-- Conversion between the cost of a fair painting and the integer inequality
that the boundary discharging argument needs to certify. -/
theorem cost_le_iff (n k : ℕ) : ((n+2)^2+2)/3-6 ≤ k ↔ n^2+4*n ≤ 3*k+14 := by
  rw [show (n+2)^2 = n^2+4*n+4 by ring]
  omega

theorem reduce_with_witnesses
    (valuesSmall : ∀ {n : ℕ}, n ≤ 6 → a n = [0,1,2,5,8,11,17].getD n 0)
    (six : ∃ P : Finset (Cell 6), Fair P ∧ Striped P ∧ P.card = a 6)
    (upper : ∀ n : ℕ, 7 ≤ n → ∃ P : Finset (Cell n),
      Fair P ∧ Striped P ∧ P.card = ((n+2)^2+2)/3-6) :
    (type_of% @OMA.S_oeis_a344719.main) ↔ BoundaryLower := by
  constructor
  · intro orig n hn P fair
    apply (cost_le_iff _ _).mp
    rw [← orig.2.1 n hn]
    exact Nat.sInf_le ⟨P, fair, rfl⟩
  · intro hl
    have tail : TailValues := by
      intro n hn
      obtain ⟨P,hp,_,hc⟩ := upper n hn
      let costs := {k : ℕ | ∃ Q : Finset (Cell n), Fair Q ∧ k=Q.card}
      have attain : P.card ∈ costs := ⟨P,hp,rfl⟩
      change sInf costs = _
      apply le_antisymm (hc ▸ Nat.sInf_le attain)
      obtain ⟨Q,hq,eq⟩ := Nat.sInf_mem (Set.nonempty_of_mem attain)
      rw [eq]
      exact (cost_le_iff _ _).mpr (hl n hn Q hq)
    apply original_iff.mpr
    refine ⟨?_, ?_, tail⟩
    · intro n hn
      obtain rfl | hn := eq_or_lt_of_le hn
      · exact six
      · obtain ⟨P,hp,hs,hc⟩ := upper n hn
        exact ⟨P,hp,hs,hc.trans (tail n hn).symm⟩
    · intro j
      have hj := valuesSmall (n := j.val) (by omega)
      fin_cases j <;> exact hj

end OMA.A344719Series

end

section

namespace PaintingRows
open OMA.S_oeis_a344719
def encode (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | w+1 => (if f w then 2^w else 0) + encode f w
theorem encode_lt (f : ℕ → Bool) (w : ℕ) : encode f w < 2^w := by
  induction w with
  | zero => simp [encode]
  | succ w ih => simp only [encode, pow_succ]; split <;> omega
theorem encode_bit (f : ℕ → Bool) {i w : ℕ} (h : i < w) :
    (encode f w).testBit i = f i := by
  induction w with
  | zero => omega
  | succ w ih =>
    by_cases lt : i < w
    · simp only [encode]; split
      · rw [Nat.testBit_two_pow_add_gt lt]; exact ih lt
      · simpa using ih lt
    · have eq : i=w := by omega
      subst i; have off := Nat.testBit_lt_two_pow (encode_lt f w)
      cases hw : f w <;> simp [encode, hw, Nat.testBit_two_pow_add_eq, off]
def pos {n : ℕ} (v : Cell n) : ℕ × ℕ := (v.1.val+1,v.2.val+1)
theorem pos_injective {n : ℕ} : Function.Injective (@pos n) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  change (a.val+1,b.val+1)=(c.val+1,d.val+1) at h
  obtain ⟨h1,h2⟩ := Prod.mk.inj h
  congr 1 <;> apply Fin.ext <;> omega
def lit {n : ℕ} (p : Finset (Cell n)) (r c : ℕ) : Bool := decide ((r,c) ∈ p.image pos)
theorem lit_at {n : ℕ} (p : Finset (Cell n)) (i j : Fin n) :
    lit p (i.val+1) (j.val+1) = decide ((i,j)∈p) := by
  unfold lit
  change decide (pos (i,j) ∈ p.image pos) = _
  simp [Finset.mem_image,pos_injective.eq_iff]
theorem dark {n : ℕ} (p : Finset (Cell n)) (i j : ℕ)
    (h : i=0 ∨ j=0 ∨ n < i ∨ n < j) : lit p i j = false := by
  simp only [lit, decide_eq_false_iff_not, Finset.mem_image]
  rintro ⟨⟨a,b⟩,_,eq⟩
  change (a.val+1,b.val+1) = (i,j) at eq
  obtain ⟨e1,e2⟩ := Prod.mk.inj eq
  have ha:=a.isLt; have hb:=b.isLt; omega
def nbr (r c : ℕ) : Finset (ℕ × ℕ) :=
  {(r,c+1),(r+2,c+1),(r+1,c),(r+1,c+2)}
theorem adj_iff {n : ℕ} (u : Cell n) (i j : Fin n) :
    adjacent u (i,j) ↔ pos u ∈ nbr i.val j.val := by
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩:=u
  rcases i with ⟨i,hi⟩; rcases j with ⟨j,hj⟩
  simp [adjacent,pos,nbr,Prod.ext_iff,Fin.ext_iff]
  omega
theorem bool_count (P : Prop) [Decidable P] : (decide P).toNat = if P then 1 else 0 := by
  by_cases h : P <;> simp [h]
theorem neighbor_sum {n : ℕ} (p : Finset (Cell n)) (i j : Fin n) :
    (p.filter (fun u => adjacent u (i,j))).card =
      (lit p i.val (j.val+1)).toNat + (lit p (i.val+2) (j.val+1)).toNat +
      (lit p (i.val+1) j.val).toNat + (lit p (i.val+1) (j.val+2)).toNat := by
  have same : (p.filter (fun u => adjacent u (i,j))).image pos =
      (nbr i.val j.val).filter (fun z => z ∈ p.image pos) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_filter,adj_iff]
    constructor
    · rintro ⟨u,⟨hu,had⟩,rfl⟩; exact ⟨had,u,hu,rfl⟩
    · rintro ⟨had,u,hu,rfl⟩; exact ⟨u,⟨hu,had⟩,rfl⟩
  rw [← Finset.card_image_of_injective _ pos_injective,same,Finset.card_filter]
  unfold nbr
  rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton] <;>
    simp [lit, bool_count, Prod.ext_iff, Nat.add_assoc]
def row {n : ℕ} (p : Finset (Cell n)) (r : ℕ) := encode (fun c => lit p r (c+1)) n
def val (x c : ℕ) := (x.testBit c).toNat
def left (x c : ℕ) := if c=0 then 0 else val x (c-1)
def weight (n x : ℕ) := ∑ j ∈ Finset.range n, val x j
def ok (n prev curr next : ℕ) : Bool := (List.range n).all (fun c =>
    curr.testBit c || decide (val prev c + val next c + left curr c + val curr (c+1) = 2))
theorem row_off {n : ℕ} (p : Finset (Cell n)) (r : ℕ) (h : r=0 ∨ n < r) : row p r = 0 := by
  have hd : ∀ c, lit p r (c+1)=false := fun _ => dark _ _ _ (by omega)
  unfold row; simp_rw [hd]
  generalize n = w
  induction w with | zero => rfl | succ w ih => simp [encode,ih]
theorem row_bit {n : ℕ} (p : Finset (Cell n)) (r c : ℕ) :
    (row p r).testBit c = lit p r (c+1) := by
  by_cases h:c < n
  · exact encode_bit _ h
  · rw [dark _ _ _ (by omega)]
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (encode_lt _ n) (Nat.pow_le_pow_right (by decide) (by omega)))
theorem row_sum {n : ℕ} (p : Finset (Cell n)) :
    (∑ i ∈ Finset.range n, weight n (row p (i+1)))=p.card := by
  simp only [weight,val,row_bit]
  rw [← Fin.sum_univ_eq_sum_range _ n]
  simp_rw [← Fin.sum_univ_eq_sum_range _ n]
  simp_rw [lit_at]
  rw [← Fintype.sum_prod_type']
  simp [bool_count]
theorem row_ok {n : ℕ} (p : Finset (Cell n)) (h : Fair p) {i : ℕ} (hi : i < n) :
    ok n (row p i) (row p (i+1)) (row p (i+2)) = true := by
  rw [ok,List.all_eq_true]
  intro j hmem
  have hj := List.mem_range.mp hmem
  let a : Fin n := ⟨i,hi⟩; let b : Fin n := ⟨j,hj⟩
  have eq := lit_at p a b
  change lit p (i+1) (j+1) = decide ((a,b)∈p) at eq
  simp only [Bool.or_eq_true,decide_eq_true_eq, val,row_bit]
  by_cases hcell:(a,b)∈p
  · exact Or.inl (by simpa [hcell] using eq)
  · right
    have cnt := (neighbor_sum p a b).symm.trans (h (a,b) hcell)
    change (lit p i (j+1)).toNat + (lit p (i+2) (j+1)).toNat + (lit p (i+1) j).toNat + (lit p (i+1) (j+2)).toNat = 2 at cnt
    rw [show left (row p (i+1)) j = (lit p (i+1) j).toNat by
      by_cases z:j=0
      · subst j; simp [left,dark _ _ _ (Or.inr (Or.inl rfl))]
      · simp [left,z,val,row_bit,Nat.sub_add_cancel (by omega : 1≤j)]]
    exact cnt
end PaintingRows

end

section

namespace PaintingRows
open OMA.S_oeis_a344719
/-- Construct all choices for the next row from the bottom-neighbor requirements
of the unpainted cells in the current row, one column at a time. -/
def nexts (a b : ℕ) : ℕ → List ℕ
  | 0 => [0]
  | w+1 =>
    let xs := nexts a b w
    let cnt := val a w + left b w + val b (w+1)
    (if b.testBit w || decide (cnt=2) then xs else []) ++
      (if b.testBit w || decide (cnt=1) then xs.map (2^w+·) else [])

theorem nexts_complete {n a b c : ℕ} (hc : c < 2^n) (pass : ok n a b c = true) :
    c ∈ nexts a b n := by
  have each := List.all_eq_true.mp pass
  have aux (w : ℕ) (hw : w ≤ n) :
      encode (c.testBit ·) w ∈ nexts a b w := by
    induction w with
    | zero => simp [nexts,encode]
    | succ w ih =>
      have valid := each w (List.mem_range.mpr (by omega))
      simp only [Bool.or_eq_true,decide_eq_true_eq] at valid
      have hmem := ih (by omega)
      unfold val at valid
      cases hbit : c.testBit w with
      | false =>
        have choice : (b.testBit w || decide (val a w + left b w + val b (w+1) = 2)) = true := by
          simp only [Bool.or_eq_true, val]
          rcases valid with e|e
          · exact Or.inl e
          · right
            apply decide_eq_true
            simp only [hbit,Bool.toNat_false,Nat.add_zero] at e
            omega
        exact List.mem_append_left _ (by simpa [encode,hbit,choice] using hmem)
      | true =>
        have choice : (b.testBit w || decide (val a w + left b w + val b (w+1) = 1)) = true := by
          simp only [Bool.or_eq_true, val]
          rcases valid with e|e
          · exact Or.inl e
          · right
            apply decide_eq_true
            simp only [hbit,Bool.toNat_true] at e
            omega
        apply List.mem_append_right
        simpa [encode,hbit,choice] using hmem
  have rep : encode (c.testBit ·) n = c := by
    apply Nat.eq_of_testBit_eq; intro j
    by_cases h : j < n
    · exact encode_bit _ h
    · have step : 2^n ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow ((encode_lt _ n).trans_le step),Nat.testBit_lt_two_pow (hc.trans_le step)]
  simpa only [rep] using aux n le_rfl

/-- `budget` counts all remaining painted cells, including the current row. -/
def search (n : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0,a,b,budget => decide (weight n b ≤ budget) && ok n a b 0
  | t+1,a,b,budget => decide (weight n b ≤ budget) &&
      (nexts a b n).any (fun c => search n t b c (budget-weight n b))

def fits (n budget : ℕ) : Bool :=
  (List.range (2^n)).any (fun first => search n (n-1) 0 first budget)

theorem search_complete {n : ℕ} (rows : ℕ → ℕ) (bound : ∀ i, rows i < 2^n) (t r budget : ℕ)
    (legal : ∀ j ≤ t, ok n (rows (r+j)) (rows (r+j+1)) (rows (r+j+2)) = true)
    (last : rows (r+t+2) = 0)
    (total : (∑ j ∈ Finset.range (t+1), weight n (rows (r+j+1))) ≤ budget) :
    search n t (rows r) (rows (r+1)) budget = true := by
  induction t generalizing r budget with
  | zero =>
    have pass := legal 0 le_rfl
    simp only [Nat.add_zero] at pass last
    rw [last] at pass
    simpa [search,pass] using total
  | succ t ih =>
    have pass := legal 0 (by omega)
    simp only [Nat.add_zero] at pass
    rw [Finset.sum_range_succ'] at total
    simp only [Nat.add_zero] at total
    have fit : weight n (rows (r+1)) ≤ budget := by omega
    simp only [search,fit,decide_true,Bool.true_and,List.any_eq_true]
    refine ⟨rows (r+2),nexts_complete (bound _) pass,?_⟩
    apply ih (r+1) (budget-weight n (rows (r+1)))
    · intro j hj
      convert legal (j+1) (by omega) using 2 <;> congr 1 <;> omega
    · convert last using 2; omega
    · have eq : (∑ j ∈ Finset.range (t+1), weight n (rows (r+(j+1)+1))) =
          ∑ j ∈ Finset.range (t+1), weight n (rows (r+1+j+1)) := by
        apply Finset.sum_congr rfl; intro j _; congr 2; omega
      omega

theorem fits_complete {n budget : ℕ} (p : Finset (Cell n)) (hn : 0 < n)
    (fair : Fair p) (size : p.card ≤ budget) : fits n budget = true := by
  apply List.any_eq_true.mpr
  refine ⟨row p 1,List.mem_range.mpr (encode_lt _ n),?_⟩
  have initial := row_off p 0 (Or.inl rfl)
  rw [← initial]
  apply search_complete (row p) (fun _ => encode_lt _ n)
  · intro j hj; exact row_ok p fair (by omega)
  · apply row_off; omega
  · simp only [Nat.zero_add,Nat.sub_add_cancel hn]
    rwa [row_sum]
end PaintingRows

end

section

namespace PaintingRows
set_option maxHeartbeats 15000000 in
set_option maxRecDepth 20000 in
theorem fail1 : fits 1 0 = false := by decide +kernel
set_option maxHeartbeats 15000000 in
set_option maxRecDepth 20000 in
theorem fail2 : fits 2 1 = false := by decide +kernel
set_option maxHeartbeats 15000000 in
set_option maxRecDepth 20000 in
theorem fail3 : fits 3 4 = false := by decide +kernel
set_option maxHeartbeats 15000000 in
set_option maxRecDepth 20000 in
theorem fail4 : fits 4 7 = false := by decide +kernel
set_option maxHeartbeats 15000000 in
set_option maxRecDepth 20000 in
theorem fail5 : fits 5 10 = false := by decide +kernel
end PaintingRows

end

section

namespace PaintingRows
open OMA.S_oeis_a344719

/-- Break the two ties in population between the two middle rows of an
eight-pixel half board. Masks 9 and 36 are horizontal reflections. -/
def middleRank (r : ℕ) : ℕ := 2 * weight 6 r + if r=9 ∨ r=36 then 1 else 0

/-- A prefix of three rows with at most eight painted cells has only 73
possible extensions to a fourth row. -/
private theorem halfCheck :
    ((List.range 64).all fun a => (nexts 0 a 6).all fun b =>
      if 8 < weight 6 a + weight 6 b then true else
      (nexts a b 6).all fun c =>
        let cost := weight 6 a + weight 6 b + weight 6 c
        if 8 < cost then true else
        (nexts b c 6).all fun d => decide (8 ≤ cost ∧ middleRank c < middleRank d)) = true := by
  decide +kernel

theorem half_six {a b c d : ℕ} (ha : a < 64) (hb : b < 64) (hc : c < 64) (hd : d < 64)
    (ab : ok 6 0 a b = true) (bc : ok 6 a b c = true) (cd : ok 6 b c d = true) :
    8 ≤ weight 6 a + weight 6 b + weight 6 c ∧
      (weight 6 a + weight 6 b + weight 6 c ≤ 8 → middleRank c < middleRank d) := by
  by_cases lo : weight 6 a + weight 6 b + weight 6 c ≤ 8
  · have aStep := List.all_eq_true.mp halfCheck a (List.mem_range.mpr ha)
    have bStep := List.all_eq_true.mp aStep b (nexts_complete hb ab)
    simp only [if_neg (by omega : ¬8 < weight 6 a + weight 6 b)] at bStep
    have cStep := List.all_eq_true.mp bStep c (nexts_complete hc bc)
    simp only [if_neg (Nat.not_lt.mpr lo)] at cStep
    have dStep := of_decide_eq_true (List.all_eq_true.mp cStep d (nexts_complete hd cd))
    exact ⟨dStep.1, fun _ => dStep.2⟩
  · omega

theorem ok_reverse {n a b c : ℕ} (pass : ok n a b c = true) : ok n c b a = true := by
  apply List.all_eq_true.mpr
  intro x hx
  have q := List.all_eq_true.mp pass x hx
  simpa only [Nat.add_comm (val c x) (val a x)] using q

/-- Apply the three-row classification twice on opposite sides of the
horizontal midline. With sixteen painted cells both middle ranks would have
to be strictly larger than the other. -/
theorem minimum_six_lower (p : Finset (Cell 6)) (fair : Fair p) : 17 ≤ p.card := by
  let r := row p
  have bounded (i : ℕ) : r i < 64 := encode_lt _ 6
  have v (i : ℕ) (h : i < 6) : ok 6 (r i) (r (i+1)) (r (i+2)) = true := row_ok p fair h
  have zero : r 0=0 := row_off p _ (Or.inl rfl)
  have last : r 7=0 := row_off p _ (Or.inr (by decide))
  have t0 := v 0 (by decide)
  rw [zero] at t0
  have top := half_six (bounded 1) (bounded 2) (bounded 3) (bounded 4)
    t0 (v 1 (by decide)) (v 2 (by decide))
  have t5 := ok_reverse (v 5 (by decide))
  change ok 6 (r 7) (r 6) (r 5) = true at t5
  rw [last] at t5
  have bottom := half_six (bounded 6) (bounded 5) (bounded 4) (bounded 3)
    t5 (ok_reverse (v 4 (by decide))) (ok_reverse (v 3 (by decide)))
  have total := row_sum p
  change (∑ i ∈ Finset.range 6, weight 6 (r (i+1))) = p.card at total
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.zero_add] at total
  change weight 6 (r 1) + weight 6 (r 2) + weight 6 (r 3) + weight 6 (r 4) +
    weight 6 (r 5) + weight 6 (r 6) = p.card at total
  omega
end PaintingRows

end

section

namespace PaintingSmall
open OMA.S_oeis_a344719

/-- Column zero is the least significant bit of a row mask. -/
def board (n : ℕ) (rows : List ℕ) : Finset (Cell n) :=
  Finset.univ.filter fun v => (rows[v.1.val]?.getD 0).testBit v.2.val

theorem witness0 : Fair (board 0 []) ∧ (board 0 []).card = 0 := by
  unfold Fair
  decide +kernel

theorem witness1 : Fair (board 1 [1]) ∧ (board 1 [1]).card = 1 := by
  unfold Fair
  decide +kernel

theorem witness2 : Fair (board 2 [1, 2]) ∧ (board 2 [1, 2]).card = 2 := by
  unfold Fair
  decide +kernel

theorem witness3 : Fair (board 3 [2, 7, 2]) ∧ (board 3 [2, 7, 2]).card = 5 := by
  unfold Fair
  decide +kernel

theorem witness4 : Fair (board 4 [5, 12, 3, 10]) ∧ (board 4 [5, 12, 3, 10]).card = 8 := by
  unfold Fair
  decide +kernel

theorem witness5 : Fair (board 5 [10, 19, 4, 25, 10]) ∧ (board 5 [10, 19, 4, 25, 10]).card = 11 := by
  unfold Fair
  decide +kernel

theorem witness6 : Fair (board 6 [21, 37, 9, 50, 6, 57]) ∧ (board 6 [21, 37, 9, 50, 6, 57]).card = 17 := by
  unfold Fair
  decide +kernel

theorem stripe6 : Striped (board 6 [21, 37, 9, 50, 6, 57]) := by
  unfold Striped
  decide +kernel

end PaintingSmall

end

section

namespace PaintingSmall
open OMA.S_oeis_a344719 PaintingRows

theorem minimum_of_search {n k : ℕ} (positive : 0 < n)
    (p : Finset (Cell n)) (fair : Fair p) (size : p.card = k)
    (exclusion : fits n (k-1) = false) : a n = k := by
  let costs := {j : ℕ | ∃ P : Finset (Cell n), Fair P ∧ j = P.card}
  have member : k ∈ costs := ⟨p, fair, size.symm⟩
  change sInf costs = k
  apply Nat.le_antisymm (Nat.sInf_le member)
  obtain ⟨q,hq,hcard⟩ := Nat.sInf_mem (show costs.Nonempty from ⟨k,member⟩)
  by_contra! small
  have check := fits_complete q positive hq (by omega : q.card ≤ k-1)
  rw [exclusion] at check
  contradiction

theorem min0 : a 0 = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le ⟨_,witness0.1,witness0.2.symm⟩)

theorem min1 : a 1 = 1 :=
  minimum_of_search (by decide) _ witness1.1 witness1.2 fail1

theorem min2 : a 2 = 2 :=
  minimum_of_search (by decide) _ witness2.1 witness2.2 fail2

theorem min3 : a 3 = 5 :=
  minimum_of_search (by decide) _ witness3.1 witness3.2 fail3

theorem min4 : a 4 = 8 :=
  minimum_of_search (by decide) _ witness4.1 witness4.2 fail4

theorem min5 : a 5 = 11 :=
  minimum_of_search (by decide) _ witness5.1 witness5.2 fail5

theorem min6 : a 6 = 17 := by
  let costs := {j : ℕ | ∃ P : Finset (Cell 6), Fair P ∧ j = P.card}
  have member : 17 ∈ costs := ⟨_, witness6.1, witness6.2.symm⟩
  change sInf costs = 17
  apply Nat.le_antisymm (Nat.sInf_le member)
  obtain ⟨P,hP,cost⟩ := Nat.sInf_mem (show costs.Nonempty from ⟨17,member⟩)
  rw [cost]
  exact minimum_six_lower P hP

theorem small_values {n : ℕ} (h : n ≤ 6) :
    a n = [0,1,2,5,8,11,17].getD n 0 := by
  interval_cases n <;> first | exact min0 | exact min1 | exact min2 | exact min3 | exact min4 | exact min5 | exact min6

theorem striped_minimum_six : ∃ p : Finset (Cell 6), Fair p ∧ Striped p ∧ p.card = a 6 :=
  ⟨_,witness6.1,stripe6,witness6.2.trans min6.symm⟩
end PaintingSmall

end

section

namespace A344719Stripes

/-- Lattice coordinates start at 1. The zero row and zero column are padding. -/
def foldAxis (b i : ℕ) : ℕ := if i < b+3 then i else i-3

def pump (b : ℕ) (g : ℕ → ℕ → Bool) (x y : ℕ) := g (foldAxis b x) (foldAxis b y)

def Seam {α : Type*} (b : ℕ) (f : ℕ → α) := f (b-1) = f (b+2) ∧ f b = f (b+3)

def Seams (b : ℕ) (g : ℕ → ℕ → Bool) :=
  (∀ y, Seam b (fun x => g x y)) ∧ (∀ x, Seam b (g x))

def Good (n : ℕ) (g : ℕ → ℕ → Bool) : Prop :=
  (∀ x y, (x=0 ∨ y=0 ∨ n < x ∨ n < y) → g x y = false) ∧
  (∀ x y, 0 < x → x ≤ n → 0 < y → y ≤ n → g x y = false →
    (g x (y-1)).toNat + (g x (y+1)).toNat +
    (g (x-1) y).toNat + (g (x+1) y).toNat = 2) ∧
  ∀ x y, 3 ≤ x → x+2 ≤ n → 3 ≤ y → y+2 ≤ n → g x y = decide (x%3 = y%3)

theorem foldAxis_left {α : Type*} (b i : ℕ) (hb : 0 < b)
    (f : ℕ → α) (seam : Seam b f) :
    f (foldAxis b (i-1)) = f (foldAxis b i - 1) := by
  by_cases hi : i = b+3
  · subst i
    convert seam.1.symm using 1 <;> dsimp [foldAxis] <;> congr 1 <;> split_ifs <;> omega
  · congr 1
    unfold foldAxis
    split_ifs <;> omega

theorem foldAxis_right {α : Type*} (b i : ℕ) (f : ℕ → α) (seam : Seam b f) :
    f (foldAxis b (i+1)) = f (foldAxis b i + 1) := by
  by_cases hi : i = b+2
  · subst i
    convert seam.2 using 1 <;> dsimp [foldAxis] <;> congr 1 <;> split_ifs <;> omega
  · congr 1
    unfold foldAxis
    split_ifs <;> omega

theorem pump_seams (b : ℕ) (hb : 0 < b) (g : ℕ → ℕ → Bool) (hs : Seams b g) :
    Seams b (pump b g) := by
  have a : foldAxis b (b - 1) = b-1 := if_pos (by omega)
  have e : foldAxis b b = b := if_pos (by omega)
  have c : foldAxis b (b + 2) = b+2 := if_pos (by omega)
  have d : foldAxis b (b + 3) = b := by unfold foldAxis; split_ifs <;> omega
  constructor
  · intro y
    simpa [Seam, pump, a,e,c,d] using (hs.1 (foldAxis b y)).1
  · intro x
    simpa [Seam, pump, a,e,c,d] using (hs.2 (foldAxis b x)).1

theorem pump_good (n b : ℕ) (hb : 3 ≤ b) (bound : b+4 ≤ n)
    (g : ℕ → ℕ → Bool) (h : Good n g) (hs : Seams b g) :
    Good (n+3) (pump b g) := by
  have boundary (i : ℕ) : i=0 ∨ n+3 < i → foldAxis b i=0 ∨ n < foldAxis b i := by
    unfold foldAxis
    split_ifs <;> omega
  have inside (i : ℕ) (a : 0 < i) (c : i ≤ n+3) : 0 < foldAxis b i ∧ foldAxis b i ≤ n := by
    unfold foldAxis
    split_ifs <;> omega
  have interior (i : ℕ) (a : 3 ≤ i) (c : i+2 ≤ n+3) : 3 ≤ foldAxis b i ∧ foldAxis b i+2 ≤ n := by
    unfold foldAxis
    split_ifs <;> omega
  have residue (i : ℕ) : foldAxis b i%3 = i%3 := by
    unfold foldAxis
    split_ifs <;> omega
  refine ⟨?_,?_,?_⟩
  · intro x y conditions
    apply h.1
    rcases conditions with hx|hy|hx|hy
    · exact (boundary x (.inl hx)).elim Or.inl (fun v => .inr (.inr (.inl v)))
    · exact (boundary y (.inl hy)).elim (fun v => .inr (.inl v)) (fun v => .inr (.inr (.inr v)))
    · exact (boundary x (.inr hx)).elim Or.inl (fun v => .inr (.inr (.inl v)))
    · exact (boundary y (.inr hy)).elim (fun v => .inr (.inl v)) (fun v => .inr (.inr (.inr v)))
  · intro x y x0 xn y0 yn off
    obtain ⟨X0,Xn⟩ := inside x x0 xn
    obtain ⟨Y0,Yn⟩ := inside y y0 yn
    have a := foldAxis_left b y (by omega) _ (hs.2 (foldAxis b x))
    have c := foldAxis_right b y _ (hs.2 (foldAxis b x))
    have d := foldAxis_left b x (by omega) _ (hs.1 (foldAxis b y))
    have e := foldAxis_right b x _ (hs.1 (foldAxis b y))
    dsimp only [pump]
    rw [a,c,d,e]
    exact h.2.1 _ _ X0 Xn Y0 Yn off
  · intro x y x0 xn y0 yn
    obtain ⟨X0,Xn⟩ := interior x x0 xn
    obtain ⟨Y0,Yn⟩ := interior y y0 yn
    simpa only [pump,residue] using h.2.2 _ _ X0 Xn Y0 Yn

end A344719Stripes

end

section

namespace A344719Stripes

def board (n : ℕ) (rows : List ℕ) (x y : ℕ) : Bool :=
  decide (0 < x ∧ x ≤ n ∧ 0 < y ∧ y ≤ n) && ((rows[x-1]?).getD 0).testBit (y-1)

def SeedTest (n : ℕ) (g : ℕ → ℕ → Bool) (r c : Fin n) : Prop :=
  let x := r.val+1
  let y := c.val+1
  (g x y = false →
    (g x (y-1)).toNat + (g x (y+1)).toNat +
    (g (x-1) y).toNat + (g (x+1) y).toNat = 2) ∧
  (3 ≤ x → x+2 ≤ n → 3 ≤ y → y+2 ≤ n → g x y = decide (x%3=y%3))

instance (n : ℕ) (g : ℕ → ℕ → Bool) (r c : Fin n) : Decidable (SeedTest n g r c) := by
  unfold SeedTest; infer_instance

theorem board_good (n : ℕ) (rows : List ℕ)
    (h : ∀ r c : Fin n, SeedTest n (board n rows) r c) : Good n (board n rows) := by
  refine ⟨?_,?_,?_⟩
  · intro x y H
    have hh : ¬ (0 < x ∧ x ≤ n ∧ 0 < y ∧ y ≤ n) := by omega
    simp [board,hh]
  · intro x y x0 xn y0 yn H
    obtain ⟨x,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0)
    obtain ⟨y,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : y ≠ 0)
    exact (h ⟨x, by omega⟩ ⟨y, by omega⟩).1 H
  · intro x y x0 xn y0 yn
    obtain ⟨x,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0)
    obtain ⟨y,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : y ≠ 0)
    exact (h ⟨x, by omega⟩ ⟨y, by omega⟩).2 x0 xn y0 yn

theorem board_seams (n b : ℕ) (rows : List ℕ)
    (h : ∀ i : Fin (n+1),
      (board n rows (b-1) i = board n rows (b+2) i ∧ board n rows b i = board n rows (b+3) i) ∧
      (board n rows i (b-1) = board n rows i (b+2) ∧ board n rows i b = board n rows i (b+3))) :
    Seams b (board n rows) := by
  constructor
  · intro y
    by_cases hy : y ≤ n
    · exact (h ⟨y, by omega⟩).1
    · simp [Seam,board,hy]
  · intro x
    by_cases hx : x ≤ n
    · exact (h ⟨x, by omega⟩).2
    · simp [Seam,board,hx]

def rows7 : List ℕ := [74, 51, 36, 73, 18, 102, 41]
theorem good7 : Good 7 (board 7 rows7) := board_good _ _ (by decide +kernel)

def rows8 : List ℕ := [85, 148, 39, 200, 19, 228, 41, 170]
theorem good8 : Good 8 (board 8 rows8) := board_good _ _ (by decide +kernel)

def rows9 : List ℕ := [202, 307, 292, 201, 146, 294, 73, 409, 166]
theorem good9 : Good 9 (board 9 rows9) := board_good _ _ (by decide +kernel)

def rows10 : List ℕ := [597, 404, 295, 584, 147, 804, 73, 914, 166, 681]
theorem good10 : Good 10 (board 10 rows10) := board_good _ _ (by decide +kernel)

def rows11 : List ℕ := [725, 1172, 295, 1608, 1171, 292, 1609, 147, 1828, 329, 1370]
theorem good11 : Good 11 (board 11 rows11) := board_good _ _ (by decide +kernel)

def rows12 : List ℕ := [1621, 2452, 2343, 1608, 1171, 2340, 585, 3218, 294, 3657, 665, 2726]
theorem good12 : Good 12 (board 12 rows12) := board_good _ _ (by decide +kernel)

def rows13 : List ℕ := [4821, 3220, 2343, 4680, 1171, 6436, 4681, 1171, 6436, 585, 7314, 1318, 5481]
theorem good13 : Good 13 (board 13 rows13) := board_good _ _ (by decide +kernel)
theorem seams13 : Seams 6 (board 13 rows13) := board_seams _ _ _ (by decide +kernel)

def rows14 : List ℕ := [5845, 9364, 2343, 12872, 9363, 2340, 12873, 9363, 2340, 12873, 1171, 14628, 2633, 10970]
theorem good14 : Good 14 (board 14 rows14) := board_good _ _ (by decide +kernel)
theorem seams14 : Seams 6 (board 14 rows14) := board_seams _ _ _ (by decide +kernel)

def rows15 : List ℕ := [13013, 19604, 18727, 12872, 9363, 18724, 4681, 25747, 18724, 4681, 25746, 2342, 29257, 5273, 21926]
theorem good15 : Good 15 (board 15 rows15) := board_good _ _ (by decide +kernel)
theorem seams15 : Seams 7 (board 15 rows15) := board_seams _ _ _ (by decide +kernel)

end A344719Stripes

end

section

/-! Counting painted cells when a three-row and a three-column band are duplicated. -/

namespace A344719Stripes

open Finset

def line (n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ i ∈ range n, f (i+1)

def band (b : ℕ) (f : ℕ → ℕ) : ℕ := f b + f (b+1) + f (b+2)

def total (n : ℕ) (g : ℕ → ℕ → Bool) : ℕ :=
  line n fun x => line n fun y => (g x y).toNat

def bands (n b : ℕ) (g : ℕ → ℕ → Bool) : ℕ :=
  (band b fun x => line n fun y => (g x y).toNat) +
  (line n fun x => band b fun y => (g x y).toNat)

def core (b : ℕ) (g : ℕ → ℕ → Bool) : ℕ :=
  band b fun x => band b fun y => (g x y).toNat

theorem line_succ (n) (f : ℕ → ℕ) : line (n+1) f = line n f + f (n+1) := by
  simp [line, sum_range_succ]

private theorem line_add (n) (f g : ℕ → ℕ) :
    (line n fun i => f i + g i) = line n f + line n g := by simp [line, sum_add_distrib]

private theorem band_add (b) (f g : ℕ → ℕ) :
    (band b fun i => f i + g i) = band b f + band b g := by simp only [band]; omega

private theorem band_fold (b) (f : ℕ → ℕ) : (band b fun i => f (foldAxis b i)) = band b f := by
  simp (disch := omega) only [band, foldAxis, if_pos]

theorem line_fold (n b : ℕ) (hn : b+2 ≤ n) (f : ℕ → ℕ) :
    (line (n+3) fun i => f (foldAxis b i)) = line n f + band b f := by
  induction n, hn using Nat.le_induction with
  | base =>
    have base : (line (b+2) fun i => f (foldAxis b i)) = line (b+2) f := by
      unfold line
      apply Finset.sum_congr rfl
      intro i hi
      have lim := Finset.mem_range.mp hi
      simp only [foldAxis, if_pos (by omega : i+1 < b+3)]
    rw [line_succ, line_succ, line_succ, base]
    simp (disch := omega) only [band, foldAxis, if_neg]
    simp only [show b+2+1-3=b by omega, show b+2+2-3=b+1 by omega,
      show b+2+3-3=b+2 by omega]
    omega
  | succ n hn ih =>
    rw [show n+1+3=(n+3)+1 by omega, line_succ, ih, line_succ n f]
    simp only [foldAxis, if_neg (by omega : ¬n+3+1 < b+3), show n+3+1-3=n+1 by omega]
    omega

theorem pump_total (n b : ℕ) (g : ℕ → ℕ → Bool) (_hb : 0 < b) (hn : b+2 ≤ n) :
    total (n+3) (pump b g) = total n g + bands n b g + core b g := by
  let row x := line n (fun y => (g x y).toNat)
  let strip x := band b (fun y => (g x y).toNat)
  have inner (x : ℕ) : (line (n+3) fun y => (pump b g x y).toNat) =
      row (foldAxis b x) + strip (foldAxis b x) :=
    line_fold n b hn (fun y => (g (foldAxis b x) y).toNat)
  change (line (n+3) fun x => line (n+3) fun y => (pump b g x y).toNat) = _
  simp_rw [inner]
  rw [line_fold n b hn (fun x => row x + strip x), line_add, band_add]
  change _ = line n row + (band b row + line n strip) + band b strip
  omega

theorem pump_bands (n b : ℕ) (g : ℕ → ℕ → Bool) (_hb : 0 < b) (hn : b+2 ≤ n) :
    bands (n+3) b (pump b g) = bands n b g + 2*core b g := by
  let row x := line n (fun y => (g x y).toNat)
  let strip x := band b (fun y => (g x y).toNat)
  have inner (x : ℕ) : (line (n+3) fun y => (pump b g x y).toNat) =
      row (foldAxis b x) + strip (foldAxis b x) :=
    line_fold n b hn (fun y => (g (foldAxis b x) y).toNat)
  have retained (x : ℕ) : (band b fun y => (pump b g x y).toNat) = strip (foldAxis b x) :=
    band_fold b (fun y => (g (foldAxis b x) y).toNat)
  change (band b fun x => line (n+3) fun y => (pump b g x y).toNat) +
      (line (n+3) fun x => band b fun y => (pump b g x y).toNat) = _
  simp_rw [inner, retained]
  rw [band_fold b (fun x => row x + strip x), band_add, line_fold n b hn strip]
  change _ = (band b row + line n strip) + 2*band b strip
  omega

theorem pump_core (b : ℕ) (g : ℕ → ℕ → Bool) : core b (pump b g) = core b g := by
  let strip x := band b (fun y => (g x y).toNat)
  have retained (x : ℕ) : (band b fun y => (pump b g x y).toNat) = strip (foldAxis b x) :=
    band_fold b (fun y => (g (foldAxis b x) y).toNat)
  change (band b fun x => band b fun y => (pump b g x y).toNat) = _
  simp_rw [retained]
  exact band_fold b strip

end A344719Stripes

end

section

namespace FairGrid
open Finset OMA.S_oeis_a344719

private def pos {n : ℕ} (q : Cell n) : ℤ × ℤ :=
  (q.1.val,q.2.val)

private theorem pos_injective (n : ℕ) : Function.Injective (@pos n) := by
  intro x y h
  exact Prod.ext (Fin.ext (Int.ofNat.inj (congrArg Prod.fst h)))
    (Fin.ext (Int.ofNat.inj (congrArg Prod.snd h)))

/-- Coordinates outside the square do not contribute any painted neighbor. -/
theorem neighbor_signed {n : ℕ} (P : Finset (Cell n)) (q : Cell n) :
    (P.filter (fun v => adjacent v q)).card =
      let r : ℤ := q.1.val
      let c : ℤ := q.2.val
      let has (a b : ℤ) : Prop := ∃ v ∈ P, (v.1.val : ℤ) = a ∧ (v.2.val : ℤ) = b
      (if has r (c-1) then 1 else 0) + (if has r (c+1) then 1 else 0) +
      (if has (r-1) c then 1 else 0) + (if has (r+1) c then 1 else 0) := by
  classical
  let r : ℤ := q.1.val
  let c : ℤ := q.2.val
  let D : Finset (ℤ × ℤ) := {(r,c-1),(r,c+1),(r-1,c),(r+1,c)}
  let has (a : ℤ × ℤ) : Prop := ∃ v ∈ P, (v.1.val : ℤ) = a.1 ∧ (v.2.val : ℤ) = a.2
  have step (v : Cell n) : adjacent v q = true ↔ pos v ∈ D := by
    simp only [adjacent, decide_eq_true_eq, D, mem_insert, mem_singleton, pos, Prod.mk.injEq, r, c, Fin.ext_iff]
    omega
  have he : (P.filter (fun v => adjacent v q)).image pos = D.filter has := by
    ext z
    constructor
    · intro hz
      obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
      obtain ⟨hv,adj⟩ := mem_filter.mp hv
      exact mem_filter.mpr ⟨(step v).mp adj,v,hv,rfl,rfl⟩
    · intro hz
      obtain ⟨hz,v,hv,h1,h2⟩ := mem_filter.mp hz
      have hzv : pos v = z := Prod.ext h1 h2
      exact mem_image.mpr ⟨v,mem_filter.mpr ⟨hv,(step v).mpr (hzv ▸ hz)⟩,hzv⟩
  rw [← Finset.card_image_of_injective _ (pos_injective n), he]
  conv_lhs => rw [← Nat.cast_id (D.filter has).card, ← Finset.sum_boole (R := ℕ)]
  have n1 : (r,c-1) ∉ ({(r,c+1),(r-1,c),(r+1,c)} : Finset (ℤ × ℤ)) := by
    simp [Prod.mk.injEq]
    omega
  have n2 : (r,c+1) ∉ ({(r-1,c),(r+1,c)} : Finset (ℤ × ℤ)) := by simp [Prod.mk.injEq]
  have n3 : (r-1,c) ∉ ({(r+1,c)} : Finset (ℤ × ℤ)) := by
    simp [Prod.mk.injEq]
    omega
  simp only [D, Finset.sum_insert n1, Finset.sum_insert n2, Finset.sum_insert n3, sum_singleton]
  ac_rfl

/-- Evaluate all four neighbor indicators for a finite-board Boolean painting. -/
theorem neighbor_model {n : ℕ} (paint : ℕ → ℕ → Bool) (q : Cell n) :
    ((univ.filter (fun v : Cell n => paint v.1.val v.2.val)).filter (fun v => adjacent v q)).card =
      let r := q.1.val
      let c := q.2.val
      (if 0 < c ∧ paint r (c-1) then 1 else 0) +
      (if c+1 < n ∧ paint r (c+1) then 1 else 0) +
      (if 0 < r ∧ paint (r-1) c then 1 else 0) +
      (if r+1 < n ∧ paint (r+1) c then 1 else 0) := by
  classical
  rw [neighbor_signed]
  dsimp only
  have general (a b : ℤ) : (∃ v ∈ (univ.filter (fun v : Cell n => paint v.1.val v.2.val)),
      (v.1.val : ℤ) = a ∧ (v.2.val : ℤ) = b) ↔
      0 ≤ a ∧ a < (n : ℤ) ∧ 0 ≤ b ∧ b < (n : ℤ) ∧ paint a.toNat b.toNat := by
    constructor
    · rintro ⟨v,hv,rfl,rfl⟩
      have := v.1.isLt
      have := v.2.isLt
      simp only [mem_filter,mem_univ,true_and] at hv
      exact ⟨by omega,by omega,by omega,by omega,by simpa using hv⟩
    · rintro ⟨ha,ha',hb,hb',h⟩
      let v : Cell n := (⟨a.toNat,by omega⟩,⟨b.toNat,by omega⟩)
      exact ⟨v,mem_filter.mpr ⟨mem_univ _,h⟩,by simpa [v] using Int.toNat_of_nonneg ha,by simpa [v] using Int.toNat_of_nonneg hb⟩
  have hr := q.1.isLt
  have hc := q.2.isLt
  let r := q.1.val
  let c := q.2.val
  have tm1 (z : ℕ) : (↑z-1 : ℤ).toNat = z-1 := by omega
  have tp1 (z : ℕ) : (↑z+1 : ℤ).toNat = z+1 := by omega
  have left : (0 ≤ (q.1.val : ℤ) ∧ ↑q.1.val < (n : ℤ) ∧ 0 ≤ (q.2.val : ℤ)-1 ∧ (q.2.val : ℤ)-1 < (n : ℤ) ∧ paint q.1.val (q.2.val-1)) ↔
      (0 < q.2.val ∧ paint q.1.val (q.2.val-1)) := by
    constructor
    · rintro ⟨h1,h2,h3,h4,hp⟩
      exact ⟨by omega,hp⟩
    · rintro ⟨h,hp⟩
      exact ⟨by omega,by omega,by omega,by omega,hp⟩
  have right : (0 ≤ (q.1.val : ℤ) ∧ ↑q.1.val < (n : ℤ) ∧ 0 ≤ (q.2.val : ℤ)+1 ∧ (q.2.val : ℤ)+1 < (n : ℤ) ∧ paint q.1.val (q.2.val+1)) ↔
      (q.2.val+1 < n ∧ paint q.1.val (q.2.val+1)) := by
    constructor
    · rintro ⟨h1,h2,h3,h4,hp⟩
      exact ⟨by omega,hp⟩
    · rintro ⟨h,hp⟩
      exact ⟨by omega,by omega,by omega,by omega,hp⟩
  have up : (0 ≤ (q.1.val : ℤ)-1 ∧ (q.1.val : ℤ)-1 < (n : ℤ) ∧ 0 ≤ (q.2.val : ℤ) ∧ (q.2.val : ℤ) < (n : ℤ) ∧ paint (q.1.val-1) q.2.val) ↔
      (0 < q.1.val ∧ paint (q.1.val-1) q.2.val) := by
    constructor
    · rintro ⟨h1,h2,h3,h4,hp⟩
      exact ⟨by omega,hp⟩
    · rintro ⟨h,hp⟩
      exact ⟨by omega,by omega,by omega,by omega,hp⟩
  have down : (0 ≤ (q.1.val : ℤ)+1 ∧ (q.1.val : ℤ)+1 < (n : ℤ) ∧ 0 ≤ (q.2.val : ℤ) ∧ (q.2.val : ℤ) < (n : ℤ) ∧ paint (q.1.val+1) q.2.val) ↔
      (q.1.val+1 < n ∧ paint (q.1.val+1) q.2.val) := by
    constructor
    · rintro ⟨h1,h2,h3,h4,hp⟩
      exact ⟨by omega,hp⟩
    · rintro ⟨h,hp⟩
      exact ⟨by omega,by omega,by omega,by omega,hp⟩
  simp only [general,Int.toNat_natCast,tm1,tp1,left,right,up,down]

end FairGrid

end

section

namespace A344719Stripes
open OMA.S_oeis_a344719 Finset

def selected (n : ℕ) (g : ℕ → ℕ → Bool) : Finset (Cell n) :=
  univ.filter (fun q => g (q.1.val+1) (q.2.val+1))

theorem selected_card (n : ℕ) (g : ℕ → ℕ → Bool) :
    (selected n g).card = ∑ x ∈ range n, ∑ y ∈ range n, (g (x+1) (y+1)).toNat := by
  classical
  have key (a : Bool) : (if a then 1 else 0) = a.toNat := by cases a <;> rfl
  unfold selected
  rw [← Nat.cast_id (univ.filter _).card, ← Finset.sum_boole (R := ℕ), Fintype.sum_prod_type]
  simp only [key, ← Fin.sum_univ_eq_sum_range]

theorem lower_indicator (f : ℕ → Bool) (h : f 0 = false) (i : ℕ) :
    (if 0 < i ∧ f (i-1+1) then 1 else 0) = (f i).toNat := by
  cases i with
  | zero => simp [h]
  | succ i =>
    cases h' : f (i+1) <;> simp [h']

theorem upper_indicator (n : ℕ) (f : ℕ → Bool) (h : ∀ x, n < x → f x = false) (i : ℕ) :
    (if i+1 < n ∧ f (i+1+1) then 1 else 0) = (f (i+1+1)).toNat := by
  by_cases h' : i+1 < n
  · cases f (i+1+1) <;> simp [h']
  · simp [h',h (i+1+1) (by omega)]

theorem selected_fair {n : ℕ} {g : ℕ → ℕ → Bool} (h : Good n g) : Fair (selected n g) := by
  intro q unpainted
  obtain ⟨r,c⟩ := q
  have off : g (r.val+1) (c.val+1) = false := by simpa [selected] using unpainted
  have loc := h.2.1 (r.val+1) (c.val+1) (by omega) (by omega) (by omega) (by omega) off
  unfold selected
  rw [FairGrid.neighbor_model (fun i j => g (i+1) (j+1))]
  dsimp only
  rw [lower_indicator (fun j => g (r.val+1) j) (h.1 _ _ (.inr (.inl rfl))) c.val,
    upper_indicator n (fun j => g (r.val+1) j) (fun j hj => h.1 _ _ (.inr (.inr (.inr hj)))) c.val,
    lower_indicator (fun i => g i (c.val+1)) (h.1 _ _ (.inl rfl)) r.val,
    upper_indicator n (fun i => g i (c.val+1)) (fun i hi => h.1 _ _ (.inr (.inr (.inl hi)))) r.val]
  simpa using loc

theorem selected_striped {n : ℕ} {g : ℕ → ℕ → Bool} (h : Good n g) :
    Striped (selected n g) := by
  intro r r0 rn
  refine ⟨⟨r.val%3, Nat.mod_lt _ (by decide)⟩,?_⟩
  intro c c0 cn
  simp only [selected, mem_filter,mem_univ,true_and,h.2.2 (r.val+1) (c.val+1) (by omega)
    (by omega) (by omega) (by omega), decide_eq_true_eq]
  omega

end A344719Stripes

end

section

namespace A344719Stripes
open OMA.S_oeis_a344719

def target (n : ℕ) := ((n+2)^2+2)/3-6

theorem target_step (n : ℕ) (hn : 7 ≤ n) : target (n+3) = target n + 2*n+7 := by
  have h : 9*9 ≤ (n+2)^2 := by
    simpa only [sq] using Nat.mul_le_mul (show 9 ≤ n+2 by omega) (show 9 ≤ n+2 by omega)
  have e : (n+3+2)^2 = (n+2)^2 + 3*(2*n+7) := by ring
  simp only [target,e]
  omega

def Ready (n : ℕ) : Prop := ∃ (b : ℕ) (g : ℕ → ℕ → Bool),
  3 ≤ b ∧ b+4 ≤ n ∧ Good n g ∧ Seams b g ∧
  total n g = target n ∧ bands n b g = 2*n+4 ∧ core b g = 3

theorem ready_step {n : ℕ} (h : Ready n) : Ready (n+3) := by
  obtain ⟨b,g,hb,hn,hg,hs,ht,hd,hc⟩ := h
  refine ⟨b,pump b g,hb,by omega,pump_good n b hb hn g hg hs,pump_seams b (by omega) g hs,?_,?_,?_⟩
  · rw [pump_total, ht,hd,hc,target_step n (by omega)] <;> omega
  · rw [pump_bands,hd,hc] <;> omega
  · rw [pump_core,hc]

theorem ready_range (n : ℕ) (hn : 13 ≤ n) : Ready n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hi : n ≤ 15
    · interval_cases n
      · exact ⟨6,board 13 rows13,by decide,by decide,good13,seams13,by decide +kernel,by decide +kernel,by decide +kernel⟩
      · exact ⟨6,board 14 rows14,by decide,by decide,good14,seams14,by decide +kernel,by decide +kernel,by decide +kernel⟩
      · exact ⟨7,board 15 rows15,by decide,by decide,good15,seams15,by decide +kernel,by decide +kernel,by decide +kernel⟩
    · have eq : n-3+3=n := by omega
      rw [← eq]
      exact ready_step (ih (n-3) (by omega) (by omega))

/-- The three checked stripe templates and six small boards attain Oda's upper bound. -/
theorem upper (n : ℕ) (hn : 7 ≤ n) :
    ∃ p : Finset (Cell n), Fair p ∧ Striped p ∧ p.card = ((n+2)^2+2)/3-6 := by
  suffices h : ∃ g, Good n g ∧ total n g = target n by
    obtain ⟨g,hg,ht⟩ := h
    exact ⟨selected n g, selected_fair hg, selected_striped hg, (selected_card n g).trans ht⟩
  by_cases h : 13 ≤ n
  · obtain ⟨_,g,_,_,hg,_,ht,_,_⟩ := ready_range n h
    exact ⟨g,hg,ht⟩
  · have hi : n ≤ 12 := by omega
    interval_cases n
    · exact ⟨_,good7,by decide +kernel⟩
    · exact ⟨_,good8,by decide +kernel⟩
    · exact ⟨_,good9,by decide +kernel⟩
    · exact ⟨_,good10,by decide +kernel⟩
    · exact ⟨_,good11,by decide +kernel⟩
    · exact ⟨_,good12,by decide +kernel⟩

theorem minimum_le (n : ℕ) (hn : 7 ≤ n) : a n ≤ ((n+2)^2+2)/3-6 := by
  obtain ⟨p,hp,_,size⟩ := upper n hn
  exact Nat.sInf_le ⟨p,hp,size.symm⟩

end A344719Stripes

end

section

/-! The complete registered conjecture is equivalent to the remaining lower bound. -/
namespace OMA.A344719Series

theorem remaining : (type_of% @OMA.S_oeis_a344719.main) ↔ BoundaryLower :=
  reduce_with_witnesses PaintingSmall.small_values PaintingSmall.striped_minimum_six A344719Stripes.upper

end OMA.A344719Series

end

section

namespace GridStrip

def bit (b y : ℕ) : ℕ := (b >>> y) &&& 1

def vertical (b y : ℕ) : ℕ := (if y=0 then 0 else bit b (y-1)) + bit b (y+1)

def legal (a b c : ℕ) : Bool :=
  (List.range 5).all fun y =>
    decide (bit b y = 1 ∨ bit a y + bit c y + vertical b y = 2)

def w (d y : ℕ) (skip : Bool) : ℕ :=
  if y ≤ d then
    if y=d then if skip then 0 else 1 else 2
  else 0

def rawCost (d : ℕ) (skip : Bool) (a b c : ℕ) : ℕ :=
  ∑ y ∈ Finset.range 5, w d y skip * bit b y *
    ((if y=0 then 1 else 0) + (if d=0 then 1 else 0) + bit a y + bit c y + vertical b y)

def deposit (d b : ℕ) : ℕ :=
  match d with
  | 0 => 2*bit b 1 + bit b 2
  | 1 => 2*(1-bit b 0) + bit b 2
  | 2 => (1-bit b 0) + (1-bit b 1)
  | _ => 0

def charge (d : ℕ) (skip : Bool) (a b c : ℕ) : ℕ :=
  rawCost d skip a b c + deposit d b

def stageGood (before after : ℕ → ℕ) (d : ℕ) (skip : Bool) : Prop :=
  ∀ a < 64, ∀ b < 64, ∀ c < 64, legal a b c = true →
    4 + before (a*64+b) ≤ charge d skip a b c + after (b*64+c)

def depth (n x : ℕ) := min 5 (min x (n-1-x))

def omitCenter (n x : ℕ) := decide (2*x+1=n ∧ x < 5)

def stationaryArcs : List (ℕ × ℕ × ℕ × Bool) :=
  [(1,0,0,false),
   (2,1,1,false),
   (3,2,2,false),
   (4,3,3,false),
   (5,4,4,false),
   (6,4,4,false),
   (6,6,5,false),
   (8,6,4,false),
   (9,8,3,false),
   (10,9,2,false),
   (11,10,1,false),
   (12,11,0,false),
   (13,3,3,true),
   (14,13,2,false),
   (15,14,1,false),
   (16,15,0,false),
   (17,4,3,false),
   (18,17,2,false),
   (19,18,1,false),
   (20,19,0,false),
   (21,4,4,true),
   (22,21,3,false),
   (23,22,2,false),
   (24,23,1,false),
   (25,24,0,false)]

theorem telescope {n : ℕ} (m : ℕ → ℕ) (r : ℕ → ℕ → ℕ) (d : ℕ → ℕ) (o : ℕ → Bool)
    (masks : ∀ x ≤ n+1, m x < 64)
    (valid : ∀ x < n, legal (m x) (m (x+1)) (m (x+2)) = true)
    (steps : ∀ x < n, stageGood (r x) (r (x+1)) (d x) (o x)) :
    4*n + r 0 (m 0*64 + m 1) ≤
      (∑ x ∈ Finset.range n, charge (d x) (o x) (m x) (m (x+1)) (m (x+2))) +
      r n (m n*64+m (n+1)) := by
  have aux (k : ℕ) (hk : k ≤ n) :
      4*k + r 0 (m 0*64+m 1) ≤
        (∑ x ∈ Finset.range k, charge (d x) (o x) (m x) (m (x+1)) (m (x+2))) +
        r k (m k*64 + m (k+1)) := by
    induction k with
    | zero => simp
    | succ j ih =>
      have hj : j < n := by omega
      have a := (steps j hj) (m j) (masks j (by omega)) (m (j+1)) (masks _ (by omega))
        (m (j+2)) (masks _ (by omega)) (valid j hj)
      have b := ih (by omega)
      rw [Finset.sum_range_succ]
      rw [show j+1+1=j+2 from by omega]
      omega
  exact aux n le_rfl

end GridStrip

end

section

namespace FairGrid

open OMA.S_oeis_a344719

/-- One word contains the six boundary-layer pixels of a board column. At both
ends of the physical board an extra zero word encodes the missing neighbors. -/
def word {n : ℕ} (paint : ℕ → ℕ → Bool) (i : ℕ) : ℕ :=
  if 0 < i ∧ i ≤ n then PaintingRows.encode (fun y => paint (i-1) y) 6 else 0

theorem word_masks {n : ℕ} (paint : ℕ → ℕ → Bool) (i : ℕ) (_hi : i ≤ n+1) :
    word (n:=n) paint i < 64 := by
  unfold word
  split
  · exact PaintingRows.encode_lt _ 6
  · decide

theorem word_zero {n : ℕ} (paint : ℕ → ℕ → Bool) : word (n:=n) paint 0 = 0 := by
  simp [word]

theorem word_end {n : ℕ} (paint : ℕ → ℕ → Bool) : word (n:=n) paint (n+1) = 0 := by
  simp [word]

theorem bit_as_testBit (w y : ℕ) : GridStrip.bit w y = (w.testBit y).toNat := by
  rw [GridStrip.bit, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.toNat_testBit]

theorem word_bit {n : ℕ} (paint : ℕ → ℕ → Bool) (i : ℕ) {y : ℕ} (hy : y < 6) :
    GridStrip.bit (word (n:=n) paint i) y =
      if 0 < i ∧ i ≤ n then (paint (i-1) y).toNat else 0 := by
  rw [bit_as_testBit]
  unfold word
  split
  · rw [PaintingRows.encode_bit _ hy]
  · simp

theorem word_physical {n : ℕ} (paint : ℕ → ℕ → Bool) {x y : ℕ}
    (hx : x < n) (hy : y < 6) :
    GridStrip.bit (word (n:=n) paint (x+1)) y = (paint x y).toNat := by
  simp [word_bit paint _ hy,show x+1≤n by omega]

private theorem word_bit_eq_row {n : ℕ} (hn : 7 ≤ n) (paint : ℕ → ℕ → Bool)
    (i : ℕ) {y : ℕ} (hy : y < 6) :
    GridStrip.bit (word (n:=n) paint i) y = PaintingRows.val
      (PaintingRows.row (Finset.univ.filter (fun v : Cell n => paint v.1.val v.2.val)) i) y := by
  rw [word_bit paint i hy,PaintingRows.val,PaintingRows.row_bit]
  split
  · rename_i h
    let x : Fin n := ⟨i-1,by omega⟩
    let c : Fin n := ⟨y,by omega⟩
    have hit := PaintingRows.lit_at (Finset.univ.filter (fun v : Cell n => paint v.1.val v.2.val)) x c
    have coord : x.val+1=i := by dsimp [x]; omega
    rw [coord] at hit
    simp [x,c] at hit
    rw [hit]
  · rw [PaintingRows.dark _ _ _ (by omega)]
    rfl

theorem word_legal {n : ℕ} (hn : 7 ≤ n) (paint : ℕ → ℕ → Bool)
    (fair : Fair (Finset.univ.filter (fun v : Cell n => paint v.1.val v.2.val)))
    (x : ℕ) (hx : x < n) :
    GridStrip.legal (word (n:=n) paint x) (word (n:=n) paint (x+1))
      (word (n:=n) paint (x+2)) = true := by
  let p : Finset (Cell n) := Finset.univ.filter (fun v => paint v.1.val v.2.val)
  have passes := List.all_eq_true.mp (PaintingRows.row_ok p fair hx)
  apply List.all_eq_true.mpr
  intro y hy
  have lo := List.mem_range.mp hy
  have cell := passes y (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true,decide_eq_true_eq] at cell
  apply decide_eq_true
  rcases cell with one|two
  · left
    rw [word_bit_eq_row hn paint _ (by omega),PaintingRows.val,one]
    rfl
  · right
    simp only [GridStrip.vertical,word_bit_eq_row hn paint _ (show y < 6 by omega),
      word_bit_eq_row hn paint _ (show y-1 < 6 by omega),
      word_bit_eq_row hn paint _ (show y+1 < 6 by omega)]
    unfold PaintingRows.left at two
    exact (Nat.add_assoc _ _ _).symm.trans two

end FairGrid

end

section

namespace FairGrid
open Finset OMA.S_oeis_a344719

theorem adjacent_symm {n : ℕ} (u v : Cell n) : adjacent u v = adjacent v u := by
  unfold adjacent
  congr 1
  apply propext
  grind

/-- In natural coordinates every red neighbor is one of four explicit locations.
Coinciding boundary candidates are harmless for this upper bound. -/
theorem degree_le_four {n : ℕ} (v : Cell n) :
    (univ.filter (adjacent v ·)).card ≤ 4 := by
  let e : Cell n → ℕ × ℕ := fun u => (u.1.val,u.2.val)
  have inj : Function.Injective e := fun x y h =>
    Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
  let D : Finset (ℕ × ℕ) := {(v.1.val,v.2.val+1),(v.1.val,v.2.val-1),
                              (v.1.val+1,v.2.val),(v.1.val-1,v.2.val)}
  have sub : (univ.filter (adjacent v ·)).image e ⊆ D := by
    intro b hb
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hb
    have h := (mem_filter.mp hu).2
    simp [adjacent] at h
    simp only [D,e,mem_insert,mem_singleton,Prod.mk.injEq]
    rcases h with ⟨h,h'|h'⟩ | ⟨h,h'|h'⟩ <;>
      first | exact Or.inl ⟨by simpa using congrArg Fin.val h.symm, by omega⟩
            | exact Or.inr (Or.inl ⟨by simpa using congrArg Fin.val h.symm, by omega⟩)
            | exact Or.inr (Or.inr (Or.inl ⟨by omega, by simpa using congrArg Fin.val h.symm⟩))
            | exact Or.inr (Or.inr (Or.inr ⟨by omega, by simpa using congrArg Fin.val h.symm⟩))
  exact (Finset.card_image_of_injective _ inj).symm.le.trans ((card_le_card sub).trans card_le_four)

theorem boundary_identity {n : ℕ} (P : Finset (Cell n)) (fair : Fair P) :
    6*P.card = 2*n^2 + (∑ v ∈ P, (P.filter (adjacent v ·)).card) +
      ∑ v ∈ P, (4 - (univ.filter (adjacent v ·)).card) := by
  classical
  let N (S : Finset (Cell n)) (v : Cell n) := (S.filter (adjacent v ·)).card
  have back : (∑ v ∈ P, N Pᶜ v) = ∑ w ∈ Pᶜ, N P w := by
    simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow, N, adjacent_symm] using
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := P) (t := Pᶜ) (fun v w => adjacent v w = true)
  have cut : (∑ v ∈ P, N Pᶜ v) = Pᶜ.card * 2 :=
    back.trans (Finset.sum_const_nat (fun w hw => by
      change (P.filter _).card = 2
      simpa only [adjacent_symm] using fair w (Finset.mem_compl.mp hw)))
  have split (v : Cell n) : N P v + N Pᶜ v = N univ v := by
    change (P.filter _).card + (Pᶜ.filter _).card = (univ.filter _).card
    have h : Disjoint (P.filter (adjacent v ·)) (Pᶜ.filter (adjacent v ·)) :=
      Finset.disjoint_left.mpr (fun x hx hh => (Finset.mem_compl.mp (Finset.mem_filter.mp hh).1) (Finset.mem_filter.mp hx).1)
    rw [← card_union_of_disjoint h, ← Finset.filter_union, Finset.union_compl]
  have hfour (v : Cell n) : N P v + N Pᶜ v + (4 - N univ v) = 4 := by
    rw [split]
    exact Nat.add_sub_of_le (degree_le_four v)
  have sum : (∑ v ∈ P, N P v) + (∑ v ∈ P, N Pᶜ v) +
      (∑ v ∈ P, (4-N univ v)) = P.card * 4 := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    exact Finset.sum_const_nat (fun v _ => hfour v)
  have cells : P.card + Pᶜ.card = n^2 := by
    simp [Cell,pow_two]
  change 6*P.card = 2*n^2 + (∑ v ∈ P, N P v) + (∑ v ∈ P, (4-N univ v))
  omega

end FairGrid

end

section

namespace FairGrid
open Finset OMA.S_oeis_a344719

def localLoss {n : ℕ} (P : Finset (Cell n)) (v : Cell n) :=
  if v ∈ P then (P.filter (adjacent v ·)).card + (4-(univ.filter (adjacent v ·)).card) else 0

theorem total_loss {n : ℕ} (P : Finset (Cell n)) (fair : Fair P) :
    2*n^2 + (∑ q, localLoss P q) = 6*P.card := by
  unfold localLoss
  rw [← Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_add_distrib]
  simpa only [Nat.add_assoc] using (boundary_identity P fair).symm

theorem model_loss {n : ℕ} (paint : ℕ → ℕ → Bool) (q : Cell n) :
    localLoss (univ.filter (fun v : Cell n => paint v.1.val v.2.val)) q =
      let r := q.1.val
      let c := q.2.val
      (paint r c).toNat * (((if 0 < c ∧ paint r (c-1) then 1 else 0) +
        (if c+1 < n ∧ paint r (c+1) then 1 else 0) +
        (if 0 < r ∧ paint (r-1) c then 1 else 0) +
        (if r+1 < n ∧ paint (r+1) c then 1 else 0)) +
        ((if c=0 then 1 else 0) + (if c+1=n then 1 else 0) +
         (if r=0 then 1 else 0) + (if r+1=n then 1 else 0))) := by
  have ht := neighbor_model (fun _ _ => true) q
  simp at ht
  have hc := q.2.isLt
  have hr := q.1.isLt
  have miss : 4 - (univ.filter (fun v : Cell n => adjacent v q)).card =
      (if q.2.val=0 then 1 else 0) + (if q.2.val+1=n then 1 else 0) +
      (if q.1.val=0 then 1 else 0) + (if q.1.val+1=n then 1 else 0) := by
    rw [ht]
    split_ifs <;> omega
  dsimp only
  unfold localLoss
  have adj (v : Cell n) : adjacent q v = adjacent v q := adjacent_symm _ _
  simp only [adj,miss,neighbor_model,mem_filter,mem_univ,true_and]
  cases h : paint q.1.val q.2.val <;> simp

end FairGrid

end

section

namespace FairGrid
open OMA.S_oeis_a344719

private theorem gatedBit (P : Prop) [Decidable P] (b : Bool) :
    (if P ∧ b then (1 : ℕ) else 0) = if P then b.toNat else 0 := by
  by_cases h : P <;> cases b <;> simp [h]

/-- The two across-word neighbors and the two within-word neighbors count
exactly the painted cells adjacent to this strip cell. -/
theorem strip_neighbor_count {n : ℕ} (hn : 7 ≤ n) (paint : ℕ → ℕ → Bool)
    (x y : ℕ) (hx : x < n) (hy : y < 5) :
    GridStrip.bit (word (n:=n) paint x) y + GridStrip.bit (word (n:=n) paint (x+2)) y +
      GridStrip.vertical (word (n:=n) paint (x+1)) y =
      ((Finset.univ.filter (fun v : Cell n => paint v.1.val v.2.val)).filter
        (fun v => adjacent v (⟨x,hx⟩,⟨y,by omega⟩))).card := by
  rw [neighbor_model]
  dsimp only
  have leftBit : GridStrip.bit (word (n:=n) paint x) y =
      if 0 < x then (paint (x-1) y).toNat else 0 := by
    simp [word_bit paint _ (by omega : y < 6), hx.le]
  have rightBit : GridStrip.bit (word (n:=n) paint (x+2)) y =
      if x+1 < n then (paint (x+1) y).toNat else 0 := by
    rw [word_bit paint _ (by omega)]
    simp [show x+2 ≤ n ↔ x+1 < n by omega]
  rw [leftBit,rightBit,GridStrip.vertical,word_physical paint hx (by omega),
    word_physical paint hx (by omega)]
  simp only [gatedBit, if_pos (show y+1 < n by omega)]
  by_cases h : y=0
  · subst y; simp [Nat.add_comm,Nat.add_assoc]
  · simp [h,show 0 < y by omega,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

theorem word_localLoss {n : ℕ} (hn : 7 ≤ n) (paint : ℕ → ℕ → Bool)
    (x y : ℕ) (hx : x < n) (hy : y < 5) :
    GridStrip.bit (word (n:=n) paint (x+1)) y *
      ((if y=0 then 1 else 0) + (if GridStrip.depth n x=0 then 1 else 0) +
        GridStrip.bit (word (n:=n) paint x) y + GridStrip.bit (word (n:=n) paint (x+2)) y +
        GridStrip.vertical (word (n:=n) paint (x+1)) y) =
      localLoss (Finset.univ.filter (fun v : Cell n => paint v.1.val v.2.val))
        (⟨x,hx⟩,⟨y,by omega⟩) := by
  rw [model_loss,word_physical paint hx (by omega)]
  dsimp only
  congr 1
  have neigh := (strip_neighbor_count hn paint x y hx hy).trans
    (neighbor_model paint ((⟨x,hx⟩,⟨y,by omega⟩) : Cell n))
  dsimp only at neigh
  have rightOff : y+1 ≠ n := by omega
  have edge : (if GridStrip.depth n x = 0 then 1 else 0) =
      (if x=0 then 1 else 0) + (if x+1=n then 1 else 0) := by
    unfold GridStrip.depth
    split_ifs <;> omega
  rw [edge,if_neg rightOff]
  omega
end FairGrid

end

section

namespace FairGrid

/-- The contribution of one end of a side in the local inward coordinates. -/
def tax (b : ℕ → ℕ → ℕ) : ℕ :=
  (2*b 0 1 + b 0 2) + (2*(1-b 1 0) + b 1 2) + ((1-b 2 0) + (1-b 2 1))

theorem tax_transpose (b : ℕ → ℕ → ℕ) (bits : ∀ x y, b x y ≤ 1) :
    tax b + tax (fun x y => b y x) = 8 := by
  have a := bits 0 1
  have b' := bits 0 2
  have c := bits 1 0
  have d := bits 1 2
  have e := bits 2 0
  have f := bits 2 1
  dsimp only [tax]
  omega

def columnTax (i : ℕ) (B : ℕ → ℕ) : ℕ :=
  if i=0 then 2*B 1 + B 2 else if i=1 then 2*(1-B 0)+B 2
  else if i=2 then (1-B 0)+(1-B 1) else 0

theorem tax_split {n : ℕ} (hn : 7 ≤ n) (b : ℕ → ℕ → ℕ) :
    (∑ x ∈ Finset.range n, columnTax (min 5 (min x (n-1-x))) (b x)) =
      tax b + tax (fun x y => b (n-1-x) y) := by
  have h0 : 0 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have h1 : 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have h2 : 2 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have h3 : n-3 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have h4 : n-2 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have h5 : n-1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have point (x : ℕ) (hx : x ∈ Finset.range n) :
      columnTax (min 5 (min x (n-1-x))) (b x) =
      (if x=0 then columnTax 0 (b x) else 0) +
      (if x=1 then columnTax 1 (b x) else 0) +
      (if x=2 then columnTax 2 (b x) else 0) +
      (if x=n-1 then columnTax 0 (b x) else 0) +
      (if x=n-2 then columnTax 1 (b x) else 0) +
      (if x=n-3 then columnTax 2 (b x) else 0) := by
    have hx' := Finset.mem_range.mp hx
    by_cases k0 : x=0
    · have edge : min 5 (min x (n-1-x)) = 0 := by omega
      simp only [edge, if_pos k0, if_neg (show x≠1 by omega), if_neg (show x≠2 by omega), if_neg (show x≠n-1 by omega), if_neg (show x≠n-2 by omega), if_neg (show x≠n-3 by omega), Nat.add_zero]
    by_cases k1 : x=1
    · have edge : min 5 (min x (n-1-x)) = 1 := by omega
      simp only [edge, if_neg (show x≠0 by omega), if_pos k1, if_neg (show x≠2 by omega), if_neg (show x≠n-1 by omega), if_neg (show x≠n-2 by omega), if_neg (show x≠n-3 by omega), Nat.add_zero, Nat.zero_add]
    by_cases k2 : x=2
    · have edge : min 5 (min x (n-1-x)) = 2 := by omega
      simp only [edge, if_neg (show x≠0 by omega), if_neg (show x≠1 by omega), if_pos k2, if_neg (show x≠n-1 by omega), if_neg (show x≠n-2 by omega), if_neg (show x≠n-3 by omega), Nat.add_zero, Nat.zero_add]
    by_cases k3 : x=n-1
    · have edge : min 5 (min x (n-1-x)) = 0 := by omega
      simp only [edge, if_neg (show x≠0 by omega), if_neg (show x≠1 by omega), if_neg (show x≠2 by omega), if_pos k3, if_neg (show x≠n-2 by omega), if_neg (show x≠n-3 by omega), Nat.add_zero, Nat.zero_add]
    by_cases k4 : x=n-2
    · have edge : min 5 (min x (n-1-x)) = 1 := by omega
      simp only [edge, if_neg (show x≠0 by omega), if_neg (show x≠1 by omega), if_neg (show x≠2 by omega), if_neg (show x≠n-1 by omega), if_pos k4, if_neg (show x≠n-3 by omega), Nat.add_zero, Nat.zero_add]
    by_cases k5 : x=n-3
    · have edge : min 5 (min x (n-1-x)) = 2 := by omega
      simp only [edge, if_neg (show x≠0 by omega), if_neg (show x≠1 by omega), if_neg (show x≠2 by omega), if_neg (show x≠n-1 by omega), if_neg (show x≠n-2 by omega), if_pos k5, Nat.add_zero, Nat.zero_add]
    have edge : 2 < min 5 (min x (n-1-x)) := by omega
    simp only [if_neg k0, if_neg k1, if_neg k2, if_neg k3, if_neg k4, if_neg k5, Nat.add_zero]
    simp [columnTax,show min 5 (min x (n-1-x)) ≠ 0 by omega,
      show min 5 (min x (n-1-x)) ≠ 1 by omega, show min 5 (min x (n-1-x)) ≠ 2 by omega]
  rw [Finset.sum_congr rfl point]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',h0,h1,h2,h3,h4,h5,if_true,
    tax,columnTax,Nat.reduceEqDiff,if_false, Nat.sub_zero]
  have e₁ : n-1-1=n-2 := by omega
  have e₂ : n-1-2=n-3 := by omega
  rw [e₁,e₂]
  omega

end FairGrid

end

section

namespace FairGrid.Wedge
open OMA.S_oeis_a344719 Finset

def turn {n : ℕ} : Cell n ≃ Cell n where
  toFun q := (q.2.rev,q.1)
  invFun q := (q.2,q.1.rev)
  left_inv q := by simp
  right_inv q := by simp

def orient {n : ℕ} (d : Fin 4) : Cell n ≃ Cell n :=
  match d.val with
  | 0 => Equiv.refl _
  | 1 => turn
  | 2 => turn.trans turn
  | _ => turn.symm

/-- Twice the weight of a cell at the lower edge, split equally
on diagonal ties and omitting the common midpoint on an odd square. -/
def paidWeight {n : ℕ} (q : Cell n) : ℕ :=
  let x := q.1.val
  let y := q.2.val
  let d := min 5 (min x (n-1-x))
  if y < 5 ∧ y ≤ d ∧ 2*y+1 ≠ n then if y=d then 1 else 2 else 0

def sideCost {n : ℕ} (d : Fin 4) (loss : Cell n → ℕ) : ℕ :=
  ∑ q : Cell n, paidWeight q * loss (orient d q)

private def grade (a b : ℕ) := if a < b then 2 else if a = b then 1 else 0

private theorem grade_flip (a b : ℕ) : grade a b + grade b a = 2 := by
  unfold grade
  split_ifs <;> omega

private theorem one_bound {n : ℕ} (q : Cell n) :
    paidWeight q ≤
      if q.2.val < q.2.rev.val then grade q.2.val (min q.1.val q.1.rev.val) else 0 := by
  obtain ⟨x,y⟩ := q
  have hx := x.isLt
  have hy := y.isLt
  simp only [paidWeight, grade, Fin.rev]
  split_ifs <;> omega

private theorem opposite {a b c : ℕ} :
    (if a < b then grade a c else 0) + (if b < a then grade b c else 0) ≤ grade (min a b) c := by
  rcases lt_trichotomy a b with h|rfl|h
  · simp [h, not_lt_of_ge h.le, Nat.min_eq_left h.le]
  · simp
  · simp [h, not_lt_of_ge h.le, Nat.min_eq_right h.le]

theorem four_weights {n : ℕ} (q : Cell n) :
    (∑ d : Fin 4, paidWeight ((orient d).symm q)) ≤ 2 := by
  rw [Fin.sum_univ_four]
  change paidWeight q + paidWeight (q.2,q.1.rev) + paidWeight (q.1.rev,q.2.rev) +
    paidWeight (q.2.rev,q.1) ≤ 2
  have a := one_bound q
  have b := one_bound (q.2,q.1.rev)
  have c := one_bound (q.1.rev,q.2.rev)
  have d := one_bound (q.2.rev,q.1)
  simp only [Fin.rev_rev] at b c d
  rw [min_comm q.1.rev.val q.1.val] at c
  rw [min_comm q.2.rev.val q.2.val] at d
  have p := opposite (a := q.2.val) (b := q.2.rev.val) (c := min q.1.val q.1.rev.val)
  have s := opposite (a := q.1.val) (b := q.1.rev.val) (c := min q.2.val q.2.rev.val)
  have eq := grade_flip (min q.1.val q.1.rev.val) (min q.2.val q.2.rev.val)
  omega

theorem four_sides {n : ℕ} (loss : Cell n → ℕ) :
    (∑ d : Fin 4, sideCost d loss) ≤ 2 * ∑ q : Cell n, loss q := by
  have move (d : Fin 4) : sideCost d loss =
      ∑ q : Cell n, paidWeight ((orient d).symm q) * loss q := by
    apply Fintype.sum_equiv (orient d)
    intro q
    simp
  simp_rw [move]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  rw [← Finset.sum_mul]
  exact Nat.mul_le_mul_right _ (four_weights q)

end FairGrid.Wedge

end

section

namespace FairGrid.Wedge
open OMA.S_oeis_a344719 Finset

theorem adjacent_turn {n : ℕ} (p q : Cell n) :
    adjacent (turn p) (turn q) = adjacent p q := by
  have h1 := p.1.isLt
  have h2 := p.2.isLt
  have h3 := q.1.isLt
  have h4 := q.2.isLt
  simp only [turn,Equiv.coe_fn_mk,adjacent,Fin.ext_iff,Fin.rev]
  congr 1
  apply propext
  omega

theorem adjacent_orient {n : ℕ} (d : Fin 4) (p q : Cell n) :
    adjacent ((orient d) p) ((orient d) q) = adjacent p q := by
  fin_cases d
  · rfl
  · exact adjacent_turn _ _
  · exact (adjacent_turn _ _).trans (adjacent_turn _ _)
  · change adjacent (turn.symm p) (turn.symm q) = adjacent p q
    simpa only [Equiv.apply_symm_apply] using
      (adjacent_turn (turn.symm p) (turn.symm q)).symm

def pull {n : ℕ} (d : Fin 4) (p : Finset (Cell n)) :=
  p.map (orient d).symm.toEmbedding

@[simp] theorem mem_pull {n : ℕ} (d : Fin 4) (p : Finset (Cell n)) (q : Cell n) :
    q ∈ pull d p ↔ (orient d) q ∈ p := by simp [pull]

theorem neighbors_pull {n : ℕ} (d : Fin 4) (p : Finset (Cell n)) (q : Cell n) :
    ((pull d p).filter (fun v => adjacent v q)).card =
      (p.filter (fun v => adjacent v ((orient d) q))).card := by
  have eq : ((pull d p).filter (fun v => adjacent v q)).map (orient d).toEmbedding =
      p.filter (fun v => adjacent v ((orient d) q)) := by
    ext x
    simp only [Finset.mem_map_equiv,Finset.mem_filter,mem_pull,
      Equiv.apply_symm_apply]
    simpa only [Equiv.apply_symm_apply] using
      (show ((x ∈ p ∧ adjacent ((orient d).symm x) q = true) ↔
        x ∈ p ∧ adjacent ((orient d) ((orient d).symm x)) ((orient d) q) = true) by
        rw [adjacent_orient])
  rw [← eq,Finset.card_map]

theorem fair_pull {n : ℕ} (d : Fin 4) (p : Finset (Cell n)) (h : Fair p) :
    Fair (pull d p) := by
  intro q hq
  rw [neighbors_pull]
  exact h _ (fun H => hq ((mem_pull d p q).mpr H))

end FairGrid.Wedge

end

section

namespace FairGrid.Wedge
open OMA.S_oeis_a344719 Finset

def ink {n : ℕ} (P : Finset (Cell n)) (d : Fin 4) (x y : ℕ) : Bool :=
  if h : x < n ∧ y < n then decide (orient d (⟨x,h.1⟩,⟨y,h.2⟩) ∈ P) else false

def board {n : ℕ} (P : Finset (Cell n)) (d : Fin 4) : Finset (Cell n) :=
  univ.filter (fun q : Cell n => ink P d q.1.val q.2.val)

@[simp] theorem ink_fin {n : ℕ} (P : Finset (Cell n)) (d : Fin 4) (x y : Fin n) :
    ink P d x y = decide (orient d (x,y) ∈ P) := by simp [ink,x.isLt,y.isLt]

theorem orient_next {n : ℕ} (d : Fin 4) (x y : Fin n) :
    orient d (x.rev,y) = orient (d+1) (y,x) := by
  fin_cases d <;> simp [orient,turn,Fin.reduceFinMk, Fin.rev_rev]

theorem ink_corner {n : ℕ} (P : Finset (Cell n)) (d : Fin 4) (x y : ℕ)
    (hx : x < n) (hy : y < n) :
    ink P d (n-1-x) y = ink P (d+1) y x := by
  let X : Fin n := ⟨x,hx⟩
  let Y : Fin n := ⟨y,hy⟩
  have xx : n-1-x=X.rev.val := by simp only [Fin.rev,X]; omega
  rw [xx]
  change ink P d X.rev Y = ink P (d+1) Y X
  rw [ink_fin, ink_fin, orient_next]

end FairGrid.Wedge

end

section

namespace FairGrid.Wedge
open OMA.S_oeis_a344719 Finset

theorem board_eq {n : ℕ} (P : Finset (Cell n)) (d : Fin 4) :
    board P d = pull d P := by
  ext q
  simp [board]

theorem board_fair {n : ℕ} (P : Finset (Cell n)) (d : Fin 4) (h : Fair P) :
    Fair (board P d) := by
  rw [board_eq]
  exact fair_pull d P h

theorem board_loss {n : ℕ} (P : Finset (Cell n)) (d : Fin 4) (q : Cell n) :
    FairGrid.localLoss (board P d) q = FairGrid.localLoss P (orient d q) := by
  have symmetry (x y : Cell n) : adjacent x y = adjacent y x := FairGrid.adjacent_symm x y
  have all : pull d (univ : Finset (Cell n)) = univ := by ext; simp
  have matchP := neighbors_pull d P q
  have matchU := neighbors_pull d (univ : Finset (Cell n)) q
  rw [all] at matchU
  simp only [board_eq,FairGrid.localLoss,mem_pull, symmetry q, symmetry ((orient d) q), matchP, matchU]

end FairGrid.Wedge

end

section

namespace FairGrid
open Finset OMA.S_oeis_a344719 GridStrip

theorem paid_eq {n : ℕ} (hn : 7 ≤ n) (x y : Fin n) (hy : y.val < 5) :
    Wedge.paidWeight (x,y) = w (depth n x) y (omitCenter n x) := by
  have hx := x.isLt
  have hy' := y.isLt
  let D := min 5 (min x.val (n-1-x.val))
  change (if y.val < 5 ∧ y.val≤D ∧ 2*y.val+1≠n then if y.val=D then 1 else 2 else 0) =
    (if y.val≤D then if y.val=D then if decide (2*x.val+1=n ∧ x.val < 5) then 0 else 1 else 2 else 0)
  simp only [hy,true_and,decide_eq_true_eq]
  dsimp only [D]
  split_ifs <;> omega

theorem raw_side {n : ℕ} (hn : 7 ≤ n) (P : Finset (Cell n)) (d : Fin 4) :
    let m := word (n:=n) (Wedge.ink P d)
    (∑ x ∈ range n, rawCost (depth n x) (omitCenter n x) (m x) (m (x+1)) (m (x+2))) =
      Wedge.sideCost d (localLoss P) := by
  dsimp only
  let paint := Wedge.ink P d
  let m := word (n:=n) paint
  let line (x y : ℕ) := if y < 5 then w (depth n x) y (omitCenter n x) * bit (m (x+1)) y *
    ((if y=0 then 1 else 0) + (if depth n x=0 then 1 else 0) +
      bit (m x) y + bit (m (x+2)) y + vertical (m (x+1)) y) else 0
  have values (x y : Fin n) :
      Wedge.paidWeight (x,y) * localLoss P (Wedge.orient d (x,y)) = line x y := by
    by_cases hy : y.val < 5
    · rw [paid_eq hn x y hy,← Wedge.board_loss]
      simp only [line,if_pos hy,Nat.mul_assoc]
      exact congrArg (fun z => w (depth n x) y (omitCenter n x) * z) (word_localLoss hn paint x y x.isLt hy).symm
    · simp [Wedge.paidWeight,line,hy]
  have col (x : ℕ) : rawCost (depth n x) (omitCenter n x) (m x) (m (x+1)) (m (x+2)) =
      ∑ y ∈ range n, line x y := by
    calc
      _ = ∑ y ∈ range 5, line x y := by
        apply sum_congr rfl
        intro y hy
        simp [line,mem_range.mp hy]
      _ = _ := sum_subset (range_mono (by omega)) (fun y _ hy => by
        simp [line,show ¬ y < 5 from fun h => hy (mem_range.mpr h)])
  rw [Wedge.sideCost,Fintype.sum_prod_type]
  simp only [values]
  simp_rw [Fin.sum_univ_eq_sum_range (line _)]
  rw [Fin.sum_univ_eq_sum_range (fun x => ∑ y ∈ range n, line x y)]
  exact sum_congr rfl (fun x _ => col x)

theorem deposit_column {n : ℕ} (paint : ℕ → ℕ → Bool) (x : ℕ) (hx : x < n) :
    deposit (depth n x) (word (n:=n) paint (x+1)) =
      columnTax (depth n x) (fun y => (paint x y).toNat) := by
  generalize depth n x = k
  match k with
  | 0 | 1 | 2 => simp [deposit,columnTax,word_physical paint hx (by decide : 1 < 6),
      word_physical paint hx (by decide : 2 < 6),word_physical paint hx (by decide : 0 < 6)]
  | k+3 => simp [deposit,columnTax]

def leftTax {n : ℕ} (P : Finset (Cell n)) (d : Fin 4) :=
  tax (fun x y => (Wedge.ink P d x y).toNat)

def rightTax {n : ℕ} (P : Finset (Cell n)) (d : Fin 4) :=
  tax (fun x y => (Wedge.ink P d (n-1-x) y).toNat)

theorem total_charge {n : ℕ} (hn : 7 ≤ n) (P : Finset (Cell n)) (d : Fin 4) :
    let m := word (n:=n) (Wedge.ink P d)
    (∑ x ∈ range n, charge (depth n x) (omitCenter n x) (m x) (m (x+1)) (m (x+2))) =
      Wedge.sideCost d (localLoss P) + (leftTax P d + rightTax P d) := by
  dsimp only
  simp only [charge,sum_add_distrib,raw_side hn P d]
  congr 1
  calc
    _ = ∑ x ∈ range n, columnTax (depth n x) (fun y => (Wedge.ink P d x y).toNat) :=
      sum_congr rfl (fun x hx => deposit_column _ _ (mem_range.mp hx))
    _ = _ := tax_split hn _

theorem rotated_tax {n : ℕ} (hn : 7 ≤ n) (P : Finset (Cell n)) (d : Fin 4) :
    rightTax P d + leftTax P (d+1) = 8 := by
  let b := fun x y => (Wedge.ink P (d+1) x y).toNat
  have h : rightTax P d = tax (fun x y => b y x) := by
    dsimp only [rightTax,tax,b]
    simp only [Wedge.ink_corner P d _ _ (by omega : 0 < n) (by omega : 1 < n),
      Wedge.ink_corner P d _ _ (by omega : 0 < n) (by omega : 2 < n),
      Wedge.ink_corner P d _ _ (by omega : 1 < n) (by omega : 0 < n),
      Wedge.ink_corner P d _ _ (by omega : 1 < n) (by omega : 2 < n),
      Wedge.ink_corner P d _ _ (by omega : 2 < n) (by omega : 0 < n),
      Wedge.ink_corner P d _ _ (by omega : 2 < n) (by omega : 1 < n)]
  rw [h,add_comm]
  exact tax_transpose b (fun x y => Bool.toNat_le _)

end FairGrid

end

section

namespace FairGrid
open Finset OMA.S_oeis_a344719 GridStrip

/-- The four side certificates account for every corner deposit exactly once,
and at most twice for each unit of painting loss. -/
theorem lower_of_word_bound {n : ℕ} (hn : 7≤n) (P : Finset (Cell n)) (fair : Fair P)
    (strip : ∀ m : ℕ → ℕ, (∀ x ≤ n+1, m x < 64) → m 0 = 0 → m (n+1)=0 →
      (∀ x < n, legal (m x) (m (x+1)) (m (x+2)) = true) →
      4*n ≤ (∑ x ∈ range n, charge (depth n x) (omitCenter n x)
        (m x) (m (x+1)) (m (x+2))) + 6) :
    n^2+4*n ≤ 3*P.card+14 := by
  have each (d : Fin 4) : 4*n ≤ Wedge.sideCost d (localLoss P) +
      (leftTax P d + rightTax P d) + 6 := by
    let paint := Wedge.ink P d
    have h := strip (word (n:=n) paint) (word_masks paint) (word_zero paint) (word_end paint)
      (word_legal hn paint (Wedge.board_fair P d fair))
    rwa [total_charge hn P d] at h
  have side := Wedge.four_sides (localLoss P)
  rw [Fin.sum_univ_four] at side
  have total := total_loss P fair
  have a := each 0
  have b := each 1
  have c := each 2
  have d := each 3
  have ha : rightTax P 0 + leftTax P 1 = 8 := rotated_tax hn P 0
  have hb : rightTax P 1 + leftTax P 2 = 8 := rotated_tax hn P 1
  have hc : rightTax P 2 + leftTax P 3 = 8 := rotated_tax hn P 2
  have hd : rightTax P 3 + leftTax P 0 = 8 := rotated_tax hn P 3
  omega

end FairGrid

end

section

namespace GridStrip

def packedR : ℕ → ℕ
  | 0 => 0xc183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183028
  | 1 => 0x569f05dc1813dcc183060549afdcc183060c183060569f05dc17afdc569f05dc1813dcc183060549afdc569f05dc1813dcc17f05dc17afdc557f060c181360c183060537af60c183060c183060557f060c17af60557f060c181360c183060537af60557f060c181360c17f060c17af60569d45dc182fe0c183060549afe0c183060c183060569d45dc17afe0569d45dc182fe0c183060549afe0569d45dc182fe0c17f05dc17afe0557d3e0c182f60c183060537af60c183060c183060557d3e0c17af60557d3e0c182f60c183060537af60557d3e0c182f60c17efe0c17af60569f05d549afdcc183060c17b060c183060c183060569f05dc17b060569f05d549afdcc183060c17b060569f05d549afdcc17f05dc17b060557f060537af60c183060c17b060c183060c183060557f060c17b060557f060537af60c183060c17b060557f060537af60c17f060c17b060569d45d549afe0c183060c17b060c183060c183060569d45dc17b060569d45d549afe0c183060c17b060569d45d549afe0c17f05dc17b060557d3e0537af60c183060c17b060c183060c183060557d3e0c17b060557d3e0537af60c183060c17b060557d3e0537af60c17efe0c17b060569f05dc1813dc569f05dc17afdcc183060c183060c17f05dc183060569f05dc1813dc569f05dc17afdc569f05dc1813dcc17f05dc183060557f060c181360557f060c17af60c183060c183060c17f060c183060557f060c181360557f060c17af60557f060c181360c17f060c183060569d45dc182fe0569d45dc17afe0c183060c183060c17f05dc183060569d45dc182fe0569d45dc17afe0569d45dc182fe0c17f05dc183060557d3e0c182f60557d3e0c17af60c183060c183060c17efe0c183060557d3e0c182f60557d3e0c17af60557d3e0c182f60c17efe0c183060569f05d549afdc569f05dc17b060c183060c183060c17f05dc183060569f05d549afdc569f05dc17b060569f05d549afdcc17f05dc183060557f060537af60557f060c17b060c183060c183060c17f060c183060557f060537af60557f060c17b060557f060537af60c17f060c183060569d45d549afe0569d45dc17b060c183060c183060c17f05dc183060569d45d549afe0569d45dc17b060569d45d549afe0c17f05dc183060557d3e0537af60557d3e0c17b060c183060c183060c17efe0c183060557d3e0537af60557d3e0c17b060557d3e0537af60c17efe0c183060569f05dc1813dcc183060549afdc569f05dc1813dcc17f05dc17afdc569f05dc1813dcc183060549afdcc17f05dc182fdcc183060c183060557f060c181360c183060537af60557f060c181360c17f060c17af60557f060c181360c183060537af60c17f060c182f60c183060c183060569d45dc182fe0c183060549afe0569d45dc182fe0c17f05dc17afe0569d45dc182fe0c183060549afe0c17f05dc182fe0c183060c183060557d3e0c182f60c183060537af60557d3e0c182f60c17efe0c17af60557d3e0c182f60c183060537af60c17efe0c182f60c183060c183060569f05d549afdcc183060c17b060569f05d549afdcc17f05dc17b060569f05d549afdcc183060c17b060c17f05dc17afdcc183060c183060557f060537af60c183060c17b060557f060537af60c17f060c17b060557f060537af60c183060c17b060c17f060c17af60c183060c183060569d45d549afe0c183060c17b060569d45d549afe0c17f05dc17b060569d45d549afe0c183060c17b060c17f05dc17afe0c183060c183060557d3e0537af60c183060c17b060557d3e0537af60c17efe0c17b060557d3e0537af60c183060c17b060c17efe0c17af60c183060c183060569f05dc1813dc569f05dc17afdc569f05dc1813dcc17f05dc183060569f05dc1813dc569f05dc17afdcc17f05dc182fdcc183060c183060557f060c181360557f060c17af60557f060c181360c17f060c183060557f060c181360557f060c17af60c17f060c182f60c183060c183060569d45dc182fe0569d45dc17afe0569d45dc182fe0c17f05dc183060569d45dc182fe0569d45dc17afe0c17f05dc182fe0c183060c183060557d3e0c182f60557d3e0c17af60557d3e0c182f60c17efe0c183060557d3e0c182f60557d3e0c17af60c17efe0c182f60c183060c183060569f05d549afdc569f05dc17b060569f05d549afdcc17f05dc183060569f05d549afdc569f05dc17b060c17f05dc17afdcc183060c183060557f060537af60557f060c17b060557f060537af60c17f060c183060557f060537af60557f060c17b060c17f060c17af60c183060c183060569d45d549afe0569d45dc17b060569d45d549afe0c17f05dc183060569d45d549afe0569d45dc17b060c17f05dc17afe0c183060c183060557d3e0537af60557d3e0c17b060557d3e0537af60c17efe0c183060557d3e0537af60557d3e0c17b060c17efe0c17af60c183060c183060
  | 2 => 0x5b83026c183027c183060c179528c183060c183060c18305e57795285b83026c183027c183060c1795285d83026c1830275d830265779528569f060c182f60c183060c17d460c183060c183060c18306052a5460569f060c182f60c183060c17d460589f060c182f6058b306052a5460597d5a8c181360c183060c1753e0c183060c183060c182f5f55753e0597d5a8c181360c183060c1753e05b7d5a9c1813605b7d5a955753e054994e0c181260c183060c1792e0c183060c183060c182e6050a12e054994e0c181260c183060c1792e056994e0c18126056ad4e050a12e05b830265779528c183060597f060c183060c183060c18305e597f0605b830265779528c183060597f0605d8302657795285d83026597f060569f06052a5460c18306054ab060c183060c183060c18306054ab060569f06052a5460c18306054ab060589f06052a546058b306054ab060597d5a855753e0c183060577b060c183060c183060c182f5f577b060597d5a855753e0c183060577b0605b7d5a955753e05b7d5a9577b06054994e050a12e0c18306052a7060c183060c183060c182e6052a706054994e050a12e0c18306052a706056994e050a12e056ad4e052a70605b83026c1830275d830265779528c183060c1830605d83026c1830605b83026c1830275d8302657795285d83026c1830275d83026c183060569f060c182f6058b306052a5460c183060c183060589f060c183060569f060c182f6058b306052a5460589f060c182f60589f060c183060597d5a8c1813605b7d5a955753e0c183060c1830605b815a9c183060597d5a8c1813605b7d5a955753e05b7d5a9c1813605b815a9c18306054994e0c18126056ad4e050a12e0c183060c18306056994e0c18306054994e0c18126056ad4e050a12e056994e0c18126056994e0c1830605b8302657795285d83026597f060c183060c1830605d83026c1830605b8302657795285d83026597f0605d8302657795285d83026c183060569f06052a546058b306054ab060c183060c183060589f060c183060569f06052a546058b306054ab060589f06052a5460589f060c183060597d5a855753e05b7d5a9577b060c183060c1830605b815a9c183060597d5a855753e05b7d5a9577b0605b7d5a955753e05b815a9c18306054994e050a12e056ad4e052a7060c183060c18306056994e0c18306054994e050a12e056ad4e052a706056994e050a12e056994e0c1830605b83026c183027c183060c1795285d83026c1830275d8302657795285b83026c183027c183060c1795285b83026c183027c183060c183060569f060c182f60c183060c17d460589f060c182f6058b306052a5460569f060c182f60c183060c17d460569f060c182f60c183060c183060597d5a8c181360c183060c1753e05b7d5a9c1813605b7d5a955753e0597d5a8c181360c183060c1753e0597d5a8c181360c183060c18306054994e0c181260c183060c1792e056994e0c18126056ad4e050a12e054994e0c181260c183060c1792e054994e0c181260c183060c1830605b830265779528c183060597f0605d8302657795285d83026597f0605b830265779528c183060597f0605b830265779528c183060c183060569f06052a5460c18306054ab060589f06052a546058b306054ab060569f06052a5460c18306054ab060569f06052a5460c183060c183060597d5a855753e0c183060577b0605b7d5a955753e05b7d5a9577b060597d5a855753e0c183060577b060597d5a855753e0c183060c18306054994e050a12e0c18306052a706056994e050a12e056ad4e052a706054994e050a12e0c18306052a706054994e050a12e0c183060c1830605b83026c1830275d8302657795285d83026c1830275d83026c1830605b83026c1830275d8302657795285b83026c183027c183060c183060569f060c182f6058b306052a5460589f060c182f60589f060c183060569f060c182f6058b306052a5460569f060c182f60c183060c183060597d5a8c1813605b7d5a955753e05b7d5a9c1813605b815a9c183060597d5a8c1813605b7d5a955753e0597d5a8c181360c183060c18306054994e0c18126056ad4e050a12e056994e0c18126056994e0c18306054994e0c18126056ad4e050a12e054994e0c181260c183060c1830605b8302657795285d83026597f0605d8302657795285d83026c1830605b8302657795285d83026597f0605b830265779528c183060c183060569f06052a546058b306054ab060589f06052a5460589f060c183060569f06052a546058b306054ab060569f06052a5460c183060c183060597d5a855753e05b7d5a9577b0605b7d5a955753e05b815a9c183060597d5a855753e05b7d5a9577b060597d5a855753e0c183060c18306054994e050a12e056ad4e052a706056994e050a12e056994e0c18306054994e050a12e056ad4e052a706054994e050a12e0c183060c183060
  | 3 => 0x64bb024c181526c1830606cad529c183060c18306062b70295ca94a864bb024c181526c1830606cad52964bb024c18152662bb0245ca94a860b3060c181460c18306068ad460c183060c1830605ecb060589d3e060b3060c181460c18306068ad46060b3060c1814605eaf060589d3e060b15a8c1816e0c18306068a5860c183060c1830605ead62b58a17e060b15a8c1816e0c18306068a586060b15a8c1816e05eb15a758a17e05ca94e0c1815e0c18306064a5760c183060c1830605ac156054956e05ca94e0c1815e0c18306064a57605ca94e0c1815e05aa54e054956e062b70235ca94a8c18306058a3060c183060c18306060b302858a306062b70235ca94a8c18306058a306062b70235ca94a860b702358a30605eaf060589d3e0c18306054b7060c183060c1830605cc706054b30605eaf060589d3e0c18306054b70605eaf060589d3e05cab06054b30605ead52758a17e0c183060549b060c183060c1830605ca95aa549b0605ead52758a17e0c183060549b0605ead52758a17e05cad526549b0605aa546054956e0c18306050af060c183060c18306058bd4e050ab0605aa546054956e0c18306050af0605aa546054956e058a146050ab06064bb024c18152662b70245ca94a8c183060c18306062b7023c18306064bb024c18152662b70245ca94a864bb024c18152662b7023c18306060b3060c1814605eaf060589d3e0c183060c1830605ec7060c18306060b3060c1814605eaf060589d3e060b3060c1814605ec7060c18306060b15a8c1816e05ead5a758a17e0c183060c1830605ead52ac18306060b15a8c1816e05ead5a758a17e060b15a8c1816e05ead52ac1830605ca94e0c1815e05aa54e054956e0c183060c1830605abd460c1830605ca94e0c1815e05aa54e054956e05ca94e0c1815e05abd460c18306062b70235ca94a860b302358a3060c183060c18306060b3022c18306062b70235ca94a860b302358a306062b70235ca94a860b3022c1830605eaf060589d3e05cab06054b3060c183060c1830605cc3060c1830605eaf060589d3e05cab06054b30605eaf060589d3e05cc3060c1830605ead52758a17e05ca9526549b060c183060c1830605ca94a9c1830605ead52758a17e05ca9526549b0605ead52758a17e05ca94a9c1830605aa546054956e058a146050ab060c183060c18306058b93e0c1830605aa546054956e058a146050ab0605aa546054956e058b93e0c18306064bb024c181526c1830606cad52964bb024c18152662bb0245ca94a864bb024c181526c1830606cad52964bb024c181526c183060c18306060b3060c181460c18306068ad46060b3060c1814605eaf060589d3e060b3060c181460c18306068ad46060b3060c181460c183060c18306060b15a8c1816e0c18306068a586060b15a8c1816e05eb15a758a17e060b15a8c1816e0c18306068a586060b15abc1816e0c183060c1830605ca94e0c1815e0c18306064a57605ca94e0c1815e05aa54e054956e05ca94e0c1815e0c18306064a57605ca94e0c1815e0c183060c18306062b70235ca94a8c18306058a306062b70235ca94a860b702358a306062b70235ca94a8c18306058a306062b70235ca94a8c183060c1830605eaf060589d3e0c18306054b70605eaf060589d3e05cab06054b30605eaf060589d3e0c18306054b70605eaf060589d3e0c183060c1830605ead52758a17e0c183060549b0605ead52758a17e05cad526549b0605ead52758a17e0c183060549b0605ead52a58a17e0c183060c1830605aa546054956e0c18306050af0605aa546054956e058a146050ab0605aa546054956e0c18306050af0605aa546054956e0c183060c18306064bb024c18152662b70245ca94a864bb024c18152662b7023c18306064bb024c18152662b70245ca94a864bb024c181526c183060c18306060b3060c1814605eaf060589d3e060b3060c1814605ec7060c18306060b3060c1814605eaf060589d3e060b3060c181460c183060c18306060b15a8c1816e05ead5a758a17e060b15a8c1816e05ead52ac18306060b15a8c1816e05ead5a758a17e060b15abc1816e0c183060c1830605ca94e0c1815e05aa54e054956e05ca94e0c1815e05abd460c1830605ca94e0c1815e05aa54e054956e05ca94e0c1815e0c183060c18306062b70235ca94a860b302358a306062b70235ca94a860b3022c18306062b70235ca94a860b302358a306062b70235ca94a8c183060c1830605eaf060589d3e05cab06054b30605eaf060589d3e05cc3060c1830605eaf060589d3e05cab06054b30605eaf060589d3e0c183060c1830605ead52758a17e05ca9526549b0605ead52758a17e05ca94a9c1830605ead52758a17e05ca9526549b0605ead52a58a17e0c183060c1830605aa546054956e058a146050ab0605aa546054956e058b93e0c1830605aa546054956e058a146050ab0605aa546054956e0c183060c183060
  | 4 => 0x6ecb02ec181a26c18306060b1328c183060c18306062e70285c9d3a96ecb02ec181a26c18306060b13286cc702dc1819a564b70295c9d3a96ac3060c181960c1830605ca9260c183060c1830605edf06058952e06ac3060c181960c1830605ca926068bf060c1818e060af06058952e06ac182dc181460c1830605ca9560c183060c1830605edd72d58955e06ac182dc181460c1830605ca956068bd7acc1813e060ad5a858955e066b9760c181360c18306058a1460c183060c1830605ad5660548d4e066b9760c181360c18306058a146064b56e0c1812e05ca54e0548d4e06ac302c62a942ac18306050ab060c183060c1830605edf02652af0606ac302c62a942ac18306050ab06068bf02b60a53a960af02752af06066bb0605ea1360c1830604cbb060c183060c1830605ad70604ebf06066bb0605ea1360c1830604cbb06064b70605c9d2e05ca70604ebf06066b972b5ea1660c1830604ca3060c183060c1830605ad562b4ea706066b972b5ea1660c1830604ca306064b56aa5c9d6605ca54a64ea706062b16605a99560c18306048b3060c183060c18306056cd5604ab706062b16605a99560c18306048b306060ad5e05895560589d3e04ab70606cc702dc1819a562b70285c9d3a9c183060c18306064d3029c1830606cc702dc1819a562b70285c9d3a96ac302cc18192464d3029c18306068bf060c1818e05eaf06058952e0c183060c18306060b3060c18306068bf060c1818e05eaf06058952e066bb060c18186060b3060c18306068bd7acc1813e05ead5a858955e0c183060c18306060c962ec18306068bd7acc1813e05ead5a858955e066b972bc18136060c962ec18306064b56e0c1812e05aa54e0548d4e0c183060c1830605ca9560c18306064b56e0c1812e05aa54e0548d4e062b1660c1812605ca9560c18306068bf02b60a53a95eaf02652af060c183060c18306060cb027c18306068bf02b60a53a95eaf02652af06066bb02a5ea132860cb027c18306064b70605c9d2e05aa70604ebf060c183060c1830605cab060c18306064b70605c9d2e05aa70604ebf06062b30605a992605cab060c18306064b56aa5c9d5e05aa54a64ea7060c183060c1830605cc152cc18306064b56aa5c9d5e05aa54a64ea706062b16295a995e05cc152cc18306060ad5e058954e0569d3e04ab7060c183060c18306058a1460c18306060ad5e058954e0569d3e04ab70605ea956056914e058a1460c1830606ecb02ec181a26c18306060b13286cc702dc1819a564b70295c9d3a96ecb02ec181a26c18306060b13286ed702ec1819a5c183060c1830606ac3060c181960c1830605ca926068bf060c1818e060af06058952e06ac3060c181960c1830605ca92606ac3060c1818e0c183060c1830606ac182dc181460c1830605ca956068bd7acc1813e060ad5a858955e06ac182dc181460c1830605ca95606acd8b3c1813e0c183060c18306066b9760c181360c18306058a146064b56e0c1812e05ca54e0548d4e066b9760c181360c18306058a146066b97e0c1812e0c183060c1830606ac302c62a942ac18306050ab06068bf02b60a53a960af02752af0606ac302c62a942ac18306050ab0606acf02c60a54abc183060c18306066bb0605ea1360c1830604cbb06064b70605c9d2e05ca70604ebf06066bb0605ea1360c1830604cbb06066bb0605c9d3e0c183060c18306066b972b5ea1660c1830604ca306064b56aa5c9d6605ca54a64ea706066b972b5ea1660c1830604ca306066c57b15c9d6e0c183060c18306062b16605a99560c18306048b306060ad5e05895560589d3e04ab706062b16605a99560c18306048b306062b16e058955e0c183060c1830606cc702dc1819a562b70285c9d3a96ac302cc18192464d3029c1830606cc702dc1819a562b70285c9d3a96cd302dc181924c183060c18306068bf060c1818e05eaf06058952e066bb060c18186060b3060c18306068bf060c1818e05eaf06058952e068bf060c181860c183060c18306068bd7acc1813e05ead5a858955e066b972bc18136060c962ec18306068bd7acc1813e05ead5a858955e068c9832c181360c183060c18306064b56e0c1812e05aa54e0548d4e062b1660c1812605ca9560c18306064b56e0c1812e05aa54e0548d4e064b5760c181260c183060c18306068bf02b60a53a95eaf02652af06066bb02a5ea132860cb027c18306068bf02b60a53a95eaf02652af06068cb02b5ea142ac183060c18306064b70605c9d2e05aa70604ebf06062b30605a992605cab060c18306064b70605c9d2e05aa70604ebf06064b70605a99360c183060c18306064b56aa5c9d5e05aa54a64ea706062b16295a995e05cc152cc18306064b56aa5c9d5e05aa54a64ea706064c17305a99660c183060c18306060ad5e058954e0569d3e04ab70605ea956056914e058a1460c18306060ad5e058954e0569d3e04ab706060ad6605691560c183060c183060
  | 5 => 0x7cdb030c181a28c1830606cc94a4c183060c18306062d30295c914a678d302fc181927c1830606ac542268bf02bc18162366a30255e9d52c78d3060c181960c18306068a93e0c183060c1830605edb06058893e074cf060c181860c18306066a536064bf060c18156062a70605a8d46078d1bb3c181860c18306068c1660c183060c1830605ec98ac58894e074c9b32c1817e0c18306066bd56064b592ec18156062995285a9566074c9ae0c181760c18306064a1560c183060c1830605ad17e054813e070c5a60c1816e0c183060629d46060b5860c1814605e9d460568556078d302e70c16aec18306054b3060c183060c1830605ecb02758ab06074cb02d6ebd62dc18306050af06064b702966a942a629b02360b706074cb0606cb15e0c18306050ab060c183060c1830605ad306054b306070c70606aad560c1830604ca306060b7060629d3605e9f0605ccb06074c9ab16cb9760c18306050ab060c183060c1830605ac17aa54a306070c1a306ab5660c1830604ca706060ad82c62a13605e914265caf06070c19e068a9660c1830604ca3060c183060c18306056c96e050ab0606cbd96066a5560c183060489b0605cad7605e952605a9536058c306078d302ec18192668bb02a60a15acc183060c18306054d3022c18306074cb02dc18182564b70295e9d52a64b7029c18152160df023c18306074cb060c18186064b30605c914e0c183060c18306050b3060c18306070c7060c18176060af0605a8d46060b7060c1814605cc3060c18306074c9ab1c18176064b17aa5c996e0c183060c18306050c952cc18306070c1a30c1816e060ad7285a955e060ad82cc1814605cd55b2c18306070c19e0c18166060a96e058895e0c183060c1830604ca9460c1830606cbd960c1815e05ca566056854e05cad760c18136058b94e0c18306074cb02c6cb95ac64b302862bb060c183060c18306050cb020c18306070c302b6ab552b60af0275eb706060af02762a13285cd7021c18306070c306068a94e060ab0605ecb060c183060c1830604cab060c1830606cbf06066a54605ca70605ac30605caf0605e9526058bb060c18306070c19af68b166060a96a85eb3060c183060c1830604cc142ac1830606cb992e66ad5605ca56265aaf0605ca572a5e9926058cd4b0c1830606cb98e064a15605ca15e05ac3060c183060c18306048a1360c18306068b5860629d460589d56056bb06058a56605a8d16054b13e0c18306078d302fc181927c1830606ac542268bf02bc18162366a30255e9d52c74cb02ec181826c18306068c13a064d302ac181820c183060c18306074cf060c181860c18306066a536064bf060c18156062a70605a8d46070cb060c181760c18306064a12e060bb060c181760c183060c18306074c9b32c1817e0c18306066bd56064b592ec18156062995285a9566070c1ab1c181760c18306064b946060c9930c181460c183060c18306070c5a60c1816e0c183060629d46060b5860c1814605e9d46056855606cc19e0c181660c18306060993605cb1860c181360c183060c18306074cb02d6ebd62dc18306050af06064b702966a942a629b02360b706070c302c6cb95acc1830604cab06060cb02864a17b1c183060c18306070c70606aad560c1830604ca306060b7060629d3605e9f0605ccb0606cc306068a94e0c183060489b0605cb306060996e0c183060c18306070c1a306ab5660c1830604ca706060ad82c62a13605e914265caf0606cb99af68b1560c18306048a30605cc182e6099960c183060c1830606cbd96066a5560c183060489b0605cad7605e952605a9536058c306068b98e064a1460c183060449306058a97605c91860c183060c18306074cb02dc18182564b70295e9d52a64b7029c18152160df023c18306070c302cc18172460af0285c954a860cb028c18171ec183060c18306070c7060c18176060af0605a8d46060b7060c1814605cc3060c1830606cc3060c1816605cab06058893e05cb3060c181660c183060c18306070c1a30c1816e060ad7285a955e060ad82cc1814605cd55b2c1830606cb99afc1816605ca56a6588d4e05cc182ec181360c183060c1830606cbd960c1815e05ca566056854e05cad760c18136058b94e0c18306068b98e0c18156058a15e054813e058a9760c181260c183060c18306070c302b6ab552b60af0275eb706060af02762a13285cd7021c1830606cbb02a68b14aa5ca70265aaf0605cc302660996afc183060c1830606cbf06066a54605ca70605ac30605caf0605e9526058bb060c18306068bb06064a13e058a306056bb06058ab0605c915e0c183060c1830606cb992e66ad5605ca56265aaf0605ca572a5e9926058cd4b0c18306068b18ad64a9460589d5a456a706058b972c5c91860c183060c18306068b5860629d460589d56056bb06058a56605a8d16054b13e0c18306064b17e0609936054994e052b306054a16605889760c183060c183060
  | 6 => 0x74cf02dc1818a4c18306066bd322c183060c18306062d30295c914a672cb02dc181824c18306066bd32168bf02bc18162366a30255e9d52c70c3060c1817e0c183060629d260c183060c1830605edb06058893e06ec3060c181760c183060629d26064bf060c18156062a70605a8d46070c5a30c181660c18306062b54e0c183060c1830605ec98ac58894e06ec1a30c181660c18306062b54e064b592ec18156062995285a956606cb9960c181560c1830605e953e0c183060c1830605ad17e054813e06ab9960c181560c1830605e953e060b5860c1814605e9d460568556070c702b6ab552bc18306050a7060c183060c1830605ecb02758ab0606ec302b6ab552bc1830604ea706064b702966a942a629b02360b70606cbb06066a5460c1830604ca3060c183060c1830605ad306054b30606abb06066a5460c1830604a9f06060b7060629d3605e9f0605ccb0606cbd92e66ad5e0c1830604c9f060c183060c1830605ac17aa54a30606ab992e66ad560c1830604a9f06060ad82c62a13605e914265caf06068b1860629d4e0c183060489b060c183060c18306056c96e050ab06066b1860629d460c18306046970605cad7605e952605a9536058c306070c702bc1817a264af0275c994aac183060c18306054d3022c1830606ec302bc18172262af0275c994a964b7029c18152160df023c1830606cbb060c1816e060a706058893e0c183060c18306050b3060c1830606abb060c1816605ea706058893e060b7060c1814605cc3060c1830606cbd92ec18156060a562858915e0c183060c18306050c952cc1830606ab992ec1815605ea5627589156060ad82cc1814605cd55b2c18306068b1860c1814605c9d56054814e0c183060c1830604ca9460c18306066b1860c1814605a9d56054814605cad760c18136058b94e0c1830606cbf02966ad42960a70255eb3060c183060c18306050cb020c1830606abb02966ad4295ea70255cb306060af02762a13285cd7021c18306068b3060629d3605c9f0605ac3060c183060c1830604cab060c18306066b3060629d3605a9f06058bf0605caf0605e9526058bb060c18306068b582c62a54e05c9d5265aab060c183060c1830604cc142ac18306066b182c62a54605a9d52558ab0605ca572a5e9926058cd4b0c18306064a97605e953e0589546056bb060c183060c18306048a1360c18306062a97605e95360569546054b706058a56605a8d16054b13e0c18306072cb02dc181824c18306066bd32168bf02bc18162366a30255e9d52c70c702dc1817a4c18306066bd32064d302ac181820c183060c1830606ec3060c181760c183060629d26064bf060c18156062a70605a8d4606cc3060c1816e0c183060629d26060bb060c181760c183060c1830606ec1a30c181660c18306062b54e064b592ec18156062995285a956606cbda30c181660c18306062b546060c9930c181460c183060c1830606ab9960c181560c1830605e953e060b5860c1814605e9d460568556068b9960c181560c1830605e953605cb1860c181360c183060c1830606ec302b6ab552bc1830604ea706064b702966a942a629b02360b70606cbf02b6ab552bc1830604ca706060cb02864a17b1c183060c1830606abb06066a5460c1830604a9f06060b7060629d3605e9f0605ccb06068bb06066a5460c183060489b0605cb306060996e0c183060c1830606ab992e66ad560c1830604a9f06060ad82c62a13605e914265caf06068b592e66ad4e0c183060489f0605cc182e6099960c183060c18306066b1860629d460c18306046970605cad7605e952605a9536058c306064b1860629d3e0c183060449306058a97605c91860c183060c1830606ec302bc18172262af0275c994a964b7029c18152160df023c1830606cbf02bc1816a260ab0275c954a860cb028c18171ec183060c1830606abb060c1816605ea706058893e060b7060c1814605cc3060c18306068bb060c1815e05ca706058893e05cb3060c181660c183060c1830606ab992ec1815605ea5627589156060ad82cc1814605cd55b2c18306068b592ec1815605ca1626588d4e05cc182ec181360c183060c18306066b1860c1814605a9d56054814605cad760c18136058b94e0c18306064b1860c181460589d56054813e058a9760c181260c183060c1830606abb02966ad4295ea70255cb306060af02762a13285cd7021c18306068b702966ad4295ca30255aaf0605cc302660996afc183060c18306066b3060629d3605a9f06058bf0605caf0605e9526058bb060c18306064b3060629d360589f06056bb06058ab0605c915e0c183060c18306066b182c62a54605a9d52558ab0605ca572a5e9926058cd4b0c18306064ad82c62a53e0589952456a706058b972c5c91860c183060c18306062a97605e95360569546054b706058a56605a8d16054b13e0c18306060a97605e952e0549546052b306054a16605889760c183060c183060
  | 7 => 0x64b7029c1815a1c18306060b12a0c183060c18306062d30285c913a664b7029c1815a1c18306060b12a062b7028c18152264a30255c9d3a960b7060c1814e0c1830605c9d1e0c183060c1830605edb06058892e060b7060c1814e0c1830605c9d1e05eb7060c18146060a7060588d2e060ad6aac181360c1830605ca93e0c183060c1830605ec972c58894e060ad6aac181360c1830605ca93e05ead6aac181360609952858955e05cad5e0c181260c18306058952e0c183060c1830605ad166054813e05cad5e0c181260c18306058952e05aad5e0c1812605c9d46054854e060af0275c9d328c1830604c9f060c183060c1830605ecb02652ab06060af0275c9d328c1830604c9f0605eaf0265c9d328609b02352af0605caf0605895260c183060489b060c183060c1830605ad30604eb30605caf0605895260c183060489b0605aaf06058952605c9f0604ebf0605ca55a85895360c1830604897060c183060c1830605ac162a4ea30605ca55a85895360c18306048970605aa55a858952e05c914264ea706058a54e0548d260c1830604493060c183060c18306056c95604aab06058a54e0548d260c183060449306056a54e0548d1e058953604ab706062b3028c18152060a30265c953a8c183060c18306054d3022c18306062b3028c18152060a30265c953a860b3027c1814a15cd3023c1830605eb3060c1814605ca706058892e0c183060c18306050b3060c1830605eb3060c1814605ca706058892e05cb3060c1813e058b3060c1830605ea96aac1813605c995a6588d4e0c183060c18306050c952cc1830605ea96aac1813605c995a6588d4e05ca96aac18136058c95aec1830605aa95e0c181260589d4e054813e0c183060c1830604ca9460c1830605aa95e0c181260589d4e054813e058a95e0c18126054a94e0c1830605eab0265c9d3285c9b02452af060c183060c18306050cb020c1830605eab0265c9d3285c9b02452af0605cab0255c9d32858cb021c1830605aab0605895260589f0604ebb060c183060c1830604cab060c1830605aab0605895260589f0604ebb06058ab060589126054ab060c1830605aa15a858952e058914a44ea7060c183060c1830604cc142ac1830605aa15a858952e058914a44ea706058a15a8589526054c14acc18306056a14e0548d1e054953e04ab3060c183060c18306048a1360c18306056a14e0548d1e054953e04ab306054a14e0548916050a13e0c18306064b7029c1815a1c18306060b12a062b7028c18152264a30255c9d3a964b7029c1815a1c18306060b12a060c7028c18169fc183060c18306060b7060c1814e0c1830605c9d1e05eb7060c18146060a7060588d2e060b7060c1814e0c1830605c9d1e05cb3060c1815e0c183060c18306060ad6aac181360c1830605ca93e05ead6aac181360609952858955e060ad6aac181360c1830605ca93e05cbd72ec181360c183060c1830605cad5e0c181260c18306058952e05aad5e0c1812605c9d46054854e05cad5e0c181260c18306058952e058a9660c181260c183060c18306060af0275c9d328c1830604c9f0605eaf0265c9d328609b02352af06060af0275c9d328c1830604c9f0605cbf0265c9d3a9c183060c1830605caf0605895260c183060489b0605aaf06058952605c9f0604ebf0605caf0605895260c183060489b06058ab06058952e0c183060c1830605ca55a85895360c18306048970605aa55a858952e05c914264ea70605ca55a85895360c183060489706058b562c58955e0c183060c18306058a54e0548d260c183060449306056a54e0548d1e058953604ab706058a54e0548d260c183060449306054a1560548d4e0c183060c18306062b3028c18152060a30265c953a860b3027c1814a15cd3023c18306062b3028c18152060a30265c953a85ec3027c18161ec183060c1830605eb3060c1814605ca706058892e05cb3060c1813e058b3060c1830605eb3060c1814605ca706058892e05aaf060c181560c183060c1830605ea96aac1813605c995a6588d4e05ca96aac18136058c95aec1830605ea96aac1813605c995a6588d4e05ab972dc181360c183060c1830605aa95e0c181260589d4e054813e058a95e0c18126054a94e0c1830605aa95e0c181260589d4e054813e056a5660c181260c183060c1830605eab0265c9d3285c9b02452af0605cab0255c9d32858cb021c1830605eab0265c9d3285c9b02452af0605abb0255c993a9c183060c1830605aab0605895260589f0604ebb06058ab060589126054ab060c1830605aab0605895260589f0604ebb06056a706058912e0c183060c1830605aa15a858952e058914a44ea706058a15a8589526054c14acc1830605aa15a858952e058914a44ea706056b162b58915e0c183060c18306056a14e0548d1e054953e04ab306054a14e0548916050a13e0c18306056a14e0548d1e054953e04ab3060529d56054894e0c183060c183060
  | 8 => 0x56a3024c181420c18306066bd2a2c183060c1830605ccb0295c954a756a3024c181420c18306066bd2a254a7024c181423629f0265c994a9529f060c181360c18306062a11e0c183060c18306058cb060588d3e0529f060c181360c18306062a11e050a7060c1813605ea3060588d3e052995aac181360c18306062b52e0c183060c18306058c182a588d4e052995aac181360c18306062b52e0509d5aac1813605e954a958914e04e954e0c181260c1830605e991e0c183060c18306054c176054853e04e954e0c181260c1830605e991e04c9d4e0c1812605a993e054853e0549f0235c993a9c1830604ca3060c183060c1830605ac702856ab060549f0235c993a9c1830604ca306052a30235c993a8609b02558af060509b060588d2e0c183060489f060c183060c18306056c706052b3060509b060588d2e0c183060489f0604ea3060588d2e05c9f06054bb060509552958912e0c183060489b060c183060c18306056bd7a952a3060509552958912e0c183060489b0604e9952958912e05c9142854a70604c9146054851e0c1830604497060c183060c18306052bd6e04eab0604c9146054851e0c18306044970604a9946054851e0589536050b306056a3024c1814205a9f0265c954a8c183060c18306050c7023c18306056a3024c1814205a9f0265c954a854a7024c18142354cb023c183060529f060c18136056a3060588d3e0c183060c1830604cab060c183060529f060c18136056a3060588d3e050a7060c18136050af060c18306052995aac18136056954a6588d4e0c183060c1830604cbd52bc18306052995aac18136056954a6588d4e0509d5aac18136050c152dc1830604e954e0c18126052993e054853e0c183060c18306048a1460c1830604e954e0c18126052993e054853e04c9d4e0c1812604ca5460c183060549f0235c993a9589b02556af060c183060c1830604ec3022c183060549f0235c993a9589b02556af06052a30235c993a852c7022c183060509b060588d2e0549f06052b7060c183060c1830604aa7060c183060509b060588d2e0549f06052b70604ea3060588d2e04eab060c183060509552958912e0549142552a7060c183060c1830604ab94aac183060509552958912e0549142552a70604e9952958912e04ebd4acc1830604c9146054851e050953604eaf060c183060c183060469d3e0c1830604c9146054851e050953604eaf0604a9946054851e04aa13e0c18306056a3024c181420c18306066bd2a254a7024c181423629f0265c994a956a3024c181420c18306066bd2a256b7024c1814a0c183060c183060529f060c181360c18306062a11e050a7060c1813605ea3060588d3e0529f060c181360c18306062a11e0529f060c1813e0c183060c18306052995aac181360c18306062b52e0509d5aac1813605e954a958914e052995aac181360c18306062b52e052ad5acc181360c183060c1830604e954e0c181260c1830605e991e04c9d4e0c1812605a993e054853e04e954e0c181260c1830605e991e04e954e0c181260c183060c183060549f0235c993a9c1830604ca306052a30235c993a8609b02558af060549f0235c993a9c1830604ca306054b30235c994aac183060c183060509b060588d2e0c183060489f0604ea3060588d2e05c9f06054bb060509b060588d2e0c183060489f060509b060588d3e0c183060c183060509552958912e0c183060489b0604e9952958912e05c9142854a7060509552958912e0c183060489b06050a952b5891560c183060c1830604c9146054851e0c18306044970604a9946054851e0589536050b30604c9146054851e0c18306044970604c914605485460c183060c18306056a3024c1814205a9f0265c954a854a7024c18142354cb023c18306056a3024c1814205a9f0265c954a856b7024c1814a0c183060c183060529f060c18136056a3060588d3e050a7060c18136050af060c183060529f060c18136056a3060588d3e0529f060c1813e0c183060c18306052995aac18136056954a6588d4e0509d5aac18136050c152dc18306052995aac18136056954a6588d4e052ad5acc181360c183060c1830604e954e0c18126052993e054853e04c9d4e0c1812604ca5460c1830604e954e0c18126052993e054853e04e954e0c181260c183060c183060549f0235c993a9589b02556af06052a30235c993a852c7022c183060549f0235c993a9589b02556af06054b30235c994aac183060c183060509b060588d2e0549f06052b70604ea3060588d2e04eab060c183060509b060588d2e0549f06052b7060509b060588d3e0c183060c183060509552958912e0549142552a70604e9952958912e04ebd4acc183060509552958912e0549142552a706050a952b5891560c183060c1830604c9146054851e050953604eaf0604a9946054851e04aa13e0c1830604c9146054851e050953604eaf0604c914605485460c183060c183060
  | 9 => 0x4c97022c1813a0c18306060b52a1c183060c18306052b7027568d4a34c97022c1813a0c18306060b52a14c97023c1813a65897026568d4a44893060c1812e0c1830605ca51e0c183060c1830604eab06052913e04893060c1812e0c1830605ca51e0489f060c1812e054a306052913e04a91425c181260c1830605eb1260c183060c18306050b16a554893604a91425c181260c1830605eb12604a914a5c18126056913a854892e0468d360c181160c1830605aa1160c183060c1830604ca55e0508d260468d360c181160c1830605aa116046993e0c181160529d2e0508d1e04c97022568d423c1830604c9f060c183060c18306052b70274e9b0604c97022568d423c1830604c9f0604c97023568d42358970264e9b06048930605291360c1830604897060c183060c1830604eab0604a9f06048930605291360c1830604897060489f060529136054a30604aa30604a914255489260c1830604a9b060c183060c18306050b16a54c970604a914255489260c1830604a9b0604a914a5548926056913a84c97060468d360508d160c1830604693060c183060c1830604ca55e0489b060468d360508d160c183060469306046993e0508d160529d2e0489f0604c97022c1813a05297026568d4a3c183060c1830604ca7023c1830604c97022c1813a05297026568d4a34c97023c1813a64ca7023c1830604893060c1812e04ea306052913e0c183060c183060489f060c1830604893060c1812e04ea306052913e0489f060c1812e0489f060c1830604a91425c18126050913a354892e0c183060c1830604aa14a5c1830604a91425c18126050913a354892e04a914a5c1812604aa14a6c183060468d360c1811604c9d2e0508d1e0c183060c18306046993e0c183060468d360c1811604c9d2e0508d1e046993e0c18116046993e0c1830604c97022568d42352970264e9b060c183060c1830604ca7023c1830604c97022568d42352970264e9b0604c97023568d4234ca7023c183060489306052913604ea30604a9f060c183060c183060489f060c183060489306052913604ea30604a9f060489f0605291360489f060c1830604a91425548926050913a34c97060c183060c1830604aa14a5c1830604a91425548926050913a34c970604a914a554892604aa14a6c183060468d360508d1604c9d2e0489b060c183060c18306046993e0c183060468d360508d1604c9d2e0489b06046993e0508d16046993e0c1830604c97022c1813a0c18306060b52a14c97023c1813a65897026568d4a44c97022c1813a0c18306060b52a14ca7022c1813a0c183060c1830604893060c1812e0c1830605ca51e0489f060c1812e054a306052913e04893060c1812e0c1830605ca51e04893060c1812e0c183060c1830604a91425c181260c1830605eb12604a914a5c18126056913a854892e04a91425c181260c1830605eb12604aa1426c181260c183060c183060468d360c181160c1830605aa116046993e0c181160529d2e0508d1e0468d360c181160c1830605aa1160468d360c181160c183060c1830604c97022568d423c1830604c9f0604c97023568d42358970264e9b0604c97022568d423c1830604c9f0604ca7022568d4a4c183060c18306048930605291360c1830604897060489f060529136054a30604aa306048930605291360c1830604897060489306052913e0c183060c1830604a914255489260c1830604a9b0604a914a5548926056913a84c970604a914255489260c1830604a9b0604aa142654892e0c183060c183060468d360508d160c183060469306046993e0508d160529d2e0489f060468d360508d160c1830604693060468d360508d1e0c183060c1830604c97022c1813a05297026568d4a34c97023c1813a64ca7023c1830604c97022c1813a05297026568d4a34ca7022c1813a0c183060c1830604893060c1812e04ea306052913e0489f060c1812e0489f060c1830604893060c1812e04ea306052913e04893060c1812e0c183060c1830604a91425c18126050913a354892e04a914a5c1812604aa14a6c1830604a91425c18126050913a354892e04aa1426c181260c183060c183060468d360c1811604c9d2e0508d1e046993e0c18116046993e0c183060468d360c1811604c9d2e0508d1e0468d360c181160c183060c1830604c97022568d42352970264e9b0604c97023568d4234ca7023c1830604c97022568d42352970264e9b0604ca7022568d4a4c183060c183060489306052913604ea30604a9f060489f0605291360489f060c183060489306052913604ea30604a9f060489306052913e0c183060c1830604a91425548926050913a34c970604a914a554892604aa14a6c1830604a91425548926050913a34c970604aa142654892e0c183060c183060468d360508d1604c9d2e0489b06046993e0508d16046993e0c183060468d360508d1604c9d2e0489b060468d360508d1e0c183060c183060
  | 10 => 0x468f01fc18121fc183060509511fc183060c1830604c9b0244a8921f468f01fc18121fc183060509511f468f01fc1812204c8f0204a8921f448b060c1811e0c1830604e8d0e0c183060c1830604a8f06048911e0448b060c1811e0c1830604e8d0e0448f060c1811e04a9b06048911e0468d2a0c1810e0c18306050951e0c183060c1830604c993204a891e0468d2a0c1810e0c18306050951e0468d2a0c1810e04c8d1a34a891e04489260c181060c1830604e8d160c183060c1830604a8d2e048911604489260c181060c1830604e8d160448d260c1810604a991604891160468f01f4a8921fc1830604a97060c183060c1830604c9b024488b060468f01f4a8921fc1830604a97060468f01f4a8921f4c8f020488b060448b06048891e0c183060488b060c183060c1830604a8f060468b060448b06048891e0c183060488b060448f060488d1e04a9b060468b060468d2a04a891e0c1830604a97060c183060c1830604c99320488b060468d2a04a891e0c1830604a97060468d2a04a891e04c8d1a3488b06044892604889160c183060488b060c183060c1830604a8d2e0468b06044892604889160c183060488b060448d260488d1604a99160468b060468f01fc18121f4c8f0204a8921fc183060c183060468f01fc183060468f01fc18121f4c8f0204a8921f468f01fc181220468f01fc183060448b060c1811e04a8f06048911e0c183060c183060448f060c183060448b060c1811e04a8f06048911e0448f060c1811e0448f060c183060468d2a0c1810e04c8d1a04a891e0c183060c183060468d2a0c183060468d2a0c1810e04c8d1a04a891e0468d2a0c1810e0468d2a0c1830604489260c1810604a8d1604891160c183060c183060448d260c1830604489260c1810604a8d1604891160448d260c181060448d260c183060468f01f4a8921f4c8f020488b060c183060c183060468f01fc183060468f01f4a8921f4c8f020488b060468f01f4a8921f468f01fc183060448b06048891e04a8f060468b060c183060c183060448f060c183060448b06048891e04a8f060468b060448f060488d1e0448f060c183060468d2a04a891e04c8d1a0488b060c183060c183060468d2a0c183060468d2a04a891e04c8d1a0488b060468d2a04a891e0468d2a0c183060448926048891604a8d160468b060c183060c183060448d260c183060448926048891604a8d160468b060448d260488d160448d260c183060468f01fc18121fc183060509511f468f01fc1812204c8f0204a8921f468f01fc18121fc183060509511f468f01fc18121fc183060c183060448b060c1811e0c1830604e8d0e0448f060c1811e04a9b06048911e0448b060c1811e0c1830604e8d0e0448b060c1811e0c183060c183060468d2a0c1810e0c18306050951e0468d2a0c1810e04c8d1a34a891e0468d2a0c1810e0c18306050951e0468d2a0c1810e0c183060c1830604489260c181060c1830604e8d160448d260c1810604a9916048911604489260c181060c1830604e8d1604489260c181060c183060c183060468f01f4a8921fc1830604a97060468f01f4a8921f4c8f020488b060468f01f4a8921fc1830604a97060468f01f4a8921fc183060c183060448b06048891e0c183060488b060448f060488d1e04a9b060468b060448b06048891e0c183060488b060448b06048891e0c183060c183060468d2a04a891e0c1830604a97060468d2a04a891e04c8d1a3488b060468d2a04a891e0c1830604a97060468d2a04a891e0c183060c18306044892604889160c183060488b060448d260488d1604a99160468b06044892604889160c183060488b06044892604889160c183060c183060468f01fc18121f4c8f0204a8921f468f01fc181220468f01fc183060468f01fc18121f4c8f0204a8921f468f01fc18121fc183060c183060448b060c1811e04a8f06048911e0448f060c1811e0448f060c183060448b060c1811e04a8f06048911e0448b060c1811e0c183060c183060468d2a0c1810e04c8d1a04a891e0468d2a0c1810e0468d2a0c183060468d2a0c1810e04c8d1a04a891e0468d2a0c1810e0c183060c1830604489260c1810604a8d1604891160448d260c181060448d260c1830604489260c1810604a8d16048911604489260c181060c183060c183060468f01f4a8921f4c8f020488b060468f01f4a8921f468f01fc183060468f01f4a8921f4c8f020488b060468f01f4a8921fc183060c183060448b06048891e04a8f060468b060448f060488d1e0448f060c183060448b06048891e04a8f060468b060448b06048891e0c183060c183060468d2a04a891e04c8d1a0488b060468d2a04a891e0468d2a0c183060468d2a04a891e04c8d1a0488b060468d2a04a891e0c183060c183060448926048891604a8d160468b060448d260488d160448d260c183060448926048891604a8d160468b06044892604889160c183060c183060
  | _ => 0

def rowId : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 5
  | 7 => 0
  | 8 => 6
  | 9 => 7
  | 10 => 8
  | 11 => 9
  | 12 => 10
  | 13 => 7
  | 14 => 8
  | 15 => 9
  | 16 => 10
  | 17 => 7
  | 18 => 8
  | 19 => 9
  | 20 => 10
  | 21 => 6
  | 22 => 7
  | 23 => 8
  | 24 => 9
  | 25 => 10
  | _ => 0

def potential (i x : ℕ) : ℕ := (packedR i >>> (7*(x%2048))) &&& 127

def R (i : ℕ) := potential (rowId i)

theorem cert_starts : ∀ i ∈ [12,16,20,25], ∀ b < 64, 34 ≤ R i b := by
  have checked : [12,16,20,25].all (fun i =>
      (List.range 64).all (fun b => decide (34 ≤ R i b))) = true := by decide +kernel
  intro i hi b hb
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked i hi) b
    (List.mem_range.mpr hb))

theorem cert_finish : ∀ a < 64, R 0 (a*64) ≤ 40 := by
  have checked : (List.range 64).all (fun a => decide (R 0 (a*64) ≤ 40)) = true := by
    decide +kernel
  intro a ha
  exact of_decide_eq_true (List.all_eq_true.mp checked a (List.mem_range.mpr ha))

end GridStrip

end

section

namespace GridStrip

def packedMeet : ℕ → ℕ
  | 0 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffd460ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8fffffffffffffffffffffffffffffffffffffffffffffffffff83fe0ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffd460fffffffffffffffffffffffffffffffffffffffffffea3fe0ff83fe0fffffffffffffffffffffffffffffffffffffffffffffffe0fffffe0ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffd460ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8fffffffffffffffffffffffffffffffffffffffffffffffffff83fe0fffffffffffffffffffffffffffffffffa8fffffe0fffffe0fffffe0fffffffffffffffffffffffffffffffd460ffff060ffff060ffff060fffffffffffffffffffffffffffffffffffff83fe0fffffffff83fe0ffffffffffffffffffffffffffffffffffffffffe0ffffffffffffe0ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffd460ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8fffffffffffffffffffffffffffffffffffffffffffffffffff83fe0ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffd460fffffffffffffffffffffffffffffffffffffffffffea3fe0ff83fe0fffffffffffffffffffffffffffffffffffffffffffffffe0fffffe0ffffffffffffa8ffffffffffffe0ffffffffffffe0ffffffffffffe0ffffffffffd460fffffffffff060fffffffffff060fffffffffff060ffffffffffffa8ffffffffffffe0ffffffffffffe0ffffffffffffe0fffffffff83fe0fffffffff83fe0fffffffff83fe0fffffffff83fe0fffffffffffffffffffe0fffffe0fffffffffffffffffffe0fffffe0ffffffffffffffffff060ffff060ffffffffffffffffff060ffff060fffffffffffffffffffffff83fe0fffffffffffffffffffffff83fe0ffffffffffffffffffffffffffe0ffffffffffffffffffffffffffe0ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffd460ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8fffffffffffffffffffffffffffffffffffffffffffffffffff83fe0ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffd460fffffffffffffffffffffffffffffffffffffffffffea3fe0ff83fe0fffffffffffffffffffffffffffffffffffffffffffffffe0fffffe0ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffd460ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8fffffffffffffffffffffffffffffffffffffffffffffffffff83fe0fffffffffffffffffffffffffffffffffa8fffffe0fffffe0fffffe0fffffffffffffffffffffffffffffffd460ffff060ffff060ffff060fffffffffffffffffffffffffffffffffffff83fe0fffffffff83fe0ffffffffffffffffffffffffffffffffffffffffe0ffffffffffffe0ffffffffffffffffffffffffffa8ffffffffffffffffffffffffffe0ffffffffffffffffffffffffd460fffffffffffffffffffffffff060ffffffffffffffffffffffffffa8ffffffffffffffffffffffffffe0fffffffffffffffffffffff83fe0fffffffffffffffffffffff83fe0ffffffffffffffffffffffffffa8ffffffffffffffffffffffffffe0ffffffffffffffffffffffffd460fffffffffffffffffffffffff060fffffffffffffffea3fe0ff83fe0ffffffffffffffff83fe0ff83fe0fffffffffffffffffffe0fffffe0fffffffffffffffffffe0fffffe0ffffffffffffffffffffffffffffffffffffffffe0ffffffffffffe0fffffffffffffffffffffffffffffffffffffff060fffffffffff060ffffffffffffffffffffffffffffffffffffffffe0ffffffffffffe0fffffffffffffffffffffffffffffffffffff83fe0fffffffff83fe0fffffffffffffffffffffffffffffffffffffffffffffffe0fffffe0ffffffffffffffffffffffffffffffffffffffffffffff060ffff060fffffffffffffffffffffffffffffffffffffffffffffffffff83fe0ffffffffffffffffffffffffffffffffffffffffffffffffffffffe0
  | 1 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffffefa6ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9ffa9ffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffffefaaffffffffffffffffffffffffffffffffffffffffffff83fa6feabfa7fffffffffffffffffffffffffffffffffffffffffffffffa9fffffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffefabffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9ffaafffffffffffffffffffffffffffffffffdffffffa8fffffa7fffffa8fffffffffffffffffffffffffffffffefe0ffff02bfffefaaffff02bffffffffffffffffffffffffffffffffffffeabfa7ffffffffeabfa7ffffffffffffffffffffffffffffffffffffffffaaffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffefa6ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9ffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffffefaaffffffffffffffffffffffffffffffffffffffffffff83fa6feabfa7fffffffffffffffffffffffffffffffffffffffffffffffa9fffffaaffffffffffffddffffffffffffa8ffffffffffffa8ffffffffffffa8fffffffffff060fffffffffff026ffffffffffefabfffffffffff026ffffffffffffddffffffffffffaaffffffffffffaaffffffffffffaafffffffff7ffe0ffffffffe9ffaaffffffffe9ffaaffffffffe9ffaafffffffffffffffffffa7fffffa8fffffffffffffffffffa7fffffa8fffffffffffffffffefaaffff02bfffffffffffffffffefaaffff02bffffffffffffffffffffffeabfa7ffffffffffffffffffffffeabfa7ffffffffffffffffffffffffffaaffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffffefa6ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9ffa9ffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffffefaaffffffffffffffffffffffffffffffffffffffffffff83fa6feabfa7fffffffffffffffffffffffffffffffffffffffffffffffa9fffffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffefabffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9ffaafffffffffffffffffffffffffffffffffdffffffa8fffffa7fffffa8fffffffffffffffffffffffffffffffefe0ffff02bfffefaaffff02bffffffffffffffffffffffffffffffffffffeabfa7ffffffffeabfa7ffffffffffffffffffffffffffffffffffffffffaaffffffffffffaaffffffffffffffffffffffffffa8ffffffffffffffffffffffffffa7ffffffffffffffffffffffffefa6ffffffffffffffffffffffffefa6ffffffffffffffffffffffffffaaffffffffffffffffffffffffffaaffffffffffffffffffffffe9ffaaffffffffffffffffffffffe9ffa9ffffffffffffffffffffffffffa7ffffffffffffffffffffffffffa7ffffffffffffffffffffffffefaaffffffffffffffffffffffffefaaffffffffffffffff83fa6feabfa7ffffffffffffffff83fa6feabfa7fffffffffffffffffffa9fffffaafffffffffffffffffffa9fffffaaffffffffffffffffffffffffffffffffffffffffa8ffffffffffffa8ffffffffffffffffffffffffffffffffffffffefabfffffffffff026ffffffffffffffffffffffffffffffffffffffffaaffffffffffffaaffffffffffffffffffffffffffffffffffffe9ffaaffffffffe9ffaafffffffffffffffffffffffffffffffffffffffffffffffa7fffffa8fffffffffffffffffffffffffffffffffffffffffffffefaaffff02bffffffffffffffffffffffffffffffffffffffffffffffffffeabfa7ffffffffffffffffffffffffffffffffffffffffffffffffffffffaa
  | 2 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffffd528ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffe93fa8ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffd5a8fffffffffffffffffffffffffffffffffffffffffffea7facfea3faefffffffffffffffffffffffffffffffffffffffffffffffa8fffffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffffd528ffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffe97fa8fffffffffffffffffffffffffffffffffb0fffffa6fffffa8fffffa6fffffffffffffffffffffffffffffffd62cfffd4aefffd5a8fffd4adffffffffffffffffffffffffffffffffffffea7fafffffffffea3faeffffffffffffffffffffffffffffffffffffffffabffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffffd528ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffe93fa8ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffd5a8fffffffffffffffffffffffffffffffffffffffffffea7facfea3faefffffffffffffffffffffffffffffffffffffffffffffffa8fffffaaffffffffffffa7ffffffffffffa7ffffffffffffa7ffffffffffffa7ffffffffffd52fffffffffffd52effffffffffd5a8ffffffffffd52effffffffffffaaffffffffffffa8ffffffffffffa9ffffffffffffa8ffffffffeabfacffffffffe93fabffffffffe97fa8ffffffffe93fabfffffffffffffffffffa8fffffa6fffffffffffffffffffa8fffffa6fffffffffffffffffd5a8fffd4adfffffffffffffffffd5a8fffd4adffffffffffffffffffffffea3faeffffffffffffffffffffffea3faeffffffffffffffffffffffffffaaffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffffd528ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffe93fa8ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffd5a8fffffffffffffffffffffffffffffffffffffffffffea7facfea3faefffffffffffffffffffffffffffffffffffffffffffffffa8fffffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffffd528ffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffe97fa8fffffffffffffffffffffffffffffffffb0fffffa6fffffa8fffffa6fffffffffffffffffffffffffffffffd62cfffd4aefffd5a8fffd4adffffffffffffffffffffffffffffffffffffea7fafffffffffea3faeffffffffffffffffffffffffffffffffffffffffabffffffffffffaaffffffffffffffffffffffffffa7ffffffffffffffffffffffffffa7ffffffffffffffffffffffffd528ffffffffffffffffffffffffd528ffffffffffffffffffffffffffa8ffffffffffffffffffffffffffa8ffffffffffffffffffffffe93fa8ffffffffffffffffffffffe93fabffffffffffffffffffffffffffa8ffffffffffffffffffffffffffa8ffffffffffffffffffffffffd5a8ffffffffffffffffffffffffd5a8fffffffffffffffea7facfea3faefffffffffffffffea7facfea3faefffffffffffffffffffa8fffffaafffffffffffffffffffa8fffffaaffffffffffffffffffffffffffffffffffffffffa7ffffffffffffa7ffffffffffffffffffffffffffffffffffffffd5a8ffffffffffd52effffffffffffffffffffffffffffffffffffffffa9ffffffffffffa8ffffffffffffffffffffffffffffffffffffe97fa8ffffffffe93fabfffffffffffffffffffffffffffffffffffffffffffffffa8fffffa6fffffffffffffffffffffffffffffffffffffffffffffd5a8fffd4adffffffffffffffffffffffffffffffffffffffffffffffffffea3faeffffffffffffffffffffffffffffffffffffffffffffffffffffffaa
  | 3 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffa6ffffffffffffffffffffffffffffffffffffffffffffffffffffd4a7ffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffeaffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffffd528fffffffffffffffffffffffffffffffffffffffffffecbfa6fe9bfaafffffffffffffffffffffffffffffffffffffffffffffffa8fffffacffffffffffffffffffffffffffffffffffffffffffffffffffffffa5ffffffffffffffffffffffffffffffffffffffffffffffffffffd4a7ffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffeabfaafffffffffffffffffffffffffffffffffaafffffa2fffffa8fffffa3fffffffffffffffffffffffffffffffd72cfffd630fffd4a7fffd6b1ffffffffffffffffffffffffffffffffffffe9bfaaffffffffe9ffabffffffffffffffffffffffffffffffffffffffffacffffffffffffadffffffffffffffffffffffffffffffffffffffffffffffffffffffa6ffffffffffffffffffffffffffffffffffffffffffffffffffffd4a7ffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffeaffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffffd528fffffffffffffffffffffffffffffffffffffffffffecbfa6fe9bfabfffffffffffffffffffffffffffffffffffffffffffffffa8fffffacffffffffffffa5ffffffffffffa6ffffffffffffa6ffffffffffffa6ffffffffffdab3ffffffffffd828ffffffffffd4a7ffffffffffd828ffffffffffffacffffffffffffaaffffffffffffa9ffffffffffffaaffffffffeabfafffffffffeaffb0ffffffffeaffaaffffffffeaffb0fffffffffffffffffffa8fffffa3fffffffffffffffffffa8fffffa3fffffffffffffffffd4a7fffd6b1fffffffffffffffffd4a7fffd6b1ffffffffffffffffffffffe9ffabffffffffffffffffffffffe9ffabffffffffffffffffffffffffffadffffffffffffffffffffffffffadffffffffffffffffffffffffffffffffffffffffffffffffffffffa6ffffffffffffffffffffffffffffffffffffffffffffffffffffd4a7ffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffeaffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffffd528fffffffffffffffffffffffffffffffffffffffffffecbfa6fe9bfaafffffffffffffffffffffffffffffffffffffffffffffffa8fffffacffffffffffffffffffffffffffffffffffffffffffffffffffffffa5ffffffffffffffffffffffffffffffffffffffffffffffffffffd4a7ffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffeabfaafffffffffffffffffffffffffffffffffaafffffa2fffffa8fffffa3fffffffffffffffffffffffffffffffd72cfffd630fffd4a7fffd6b1ffffffffffffffffffffffffffffffffffffe9bfaaffffffffe9ffabffffffffffffffffffffffffffffffffffffffffacffffffffffffadffffffffffffffffffffffffffa6ffffffffffffffffffffffffffa7ffffffffffffffffffffffffd4a7ffffffffffffffffffffffffd6a8ffffffffffffffffffffffffffa9ffffffffffffffffffffffffffabffffffffffffffffffffffeaffaaffffffffffffffffffffffeb3fb1ffffffffffffffffffffffffffa9ffffffffffffffffffffffffffa9ffffffffffffffffffffffffd528ffffffffffffffffffffffffd528fffffffffffffffecbfa6fe9bfabfffffffffffffffecbfa6fea3facfffffffffffffffffffa8fffffacfffffffffffffffffffa8fffffaeffffffffffffffffffffffffffffffffffffffffa6ffffffffffffa6ffffffffffffffffffffffffffffffffffffffd4a7ffffffffffd828ffffffffffffffffffffffffffffffffffffffffa9ffffffffffffaaffffffffffffffffffffffffffffffffffffeaffaaffffffffeaffb0fffffffffffffffffffffffffffffffffffffffffffffffa8fffffa3fffffffffffffffffffffffffffffffffffffffffffffd4a7fffd6b1ffffffffffffffffffffffffffffffffffffffffffffffffffe9ffabffffffffffffffffffffffffffffffffffffffffffffffffffffffad
  | 4 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffffd3a5ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9ffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffabffffffffffffffffffffffffffffffffffffffffffffffffffffd5a7fffffffffffffffffffffffffffffffffffffffffffec3fa9fe9bfa9fffffffffffffffffffffffffffffffffffffffffffffffa5fffffabffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffffd426ffffffffffffffffffffffffffffffffffffffffffffffffffffffabffffffffffffffffffffffffffffffffffffffffffffffffffeabfabfffffffffffffffffffffffffffffffffaefffffa7fffffa8fffffaafffffffffffffffffffffffffffffffd92afffd630fffd424fffd733ffffffffffffffffffffffffffffffffffffe9ffaaffffffffea7facffffffffffffffffffffffffffffffffffffffffacffffffffffffafffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffffd3a5ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9ffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffabffffffffffffffffffffffffffffffffffffffffffffffffffffd5a7fffffffffffffffffffffffffffffffffffffffffffec3fa9fe9bfa9fffffffffffffffffffffffffffffffffffffffffffffffa5fffffacffffffffffffabffffffffffffa4ffffffffffffa9ffffffffffffa5ffffffffffd834ffffffffffd930ffffffffffd3a5ffffffffffd9b1ffffffffffffb0ffffffffffffa8ffffffffffffaaffffffffffffa9ffffffffeb3fb0ffffffffe93fb3ffffffffea7faaffffffffe97fb4fffffffffffffffffffa8fffffaafffffffffffffffffffa9fffffabfffffffffffffffffd424fffd733fffffffffffffffffd4a5fffd7b4ffffffffffffffffffffffea7facffffffffffffffffffffffeabfadffffffffffffffffffffffffffafffffffffffffffffffffffffffb0ffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffffd3a5ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9ffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffabffffffffffffffffffffffffffffffffffffffffffffffffffffd5a7fffffffffffffffffffffffffffffffffffffffffffec3fa9fe9bfa9fffffffffffffffffffffffffffffffffffffffffffffffa5fffffabffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffffd426ffffffffffffffffffffffffffffffffffffffffffffffffffffffabffffffffffffffffffffffffffffffffffffffffffffffffffeabfabfffffffffffffffffffffffffffffffffaefffffa7fffffa8fffffaafffffffffffffffffffffffffffffffd92afffd630fffd424fffd733ffffffffffffffffffffffffffffffffffffe9ffaaffffffffea7facffffffffffffffffffffffffffffffffffffffffacffffffffffffafffffffffffffffffffffffffffa7ffffffffffffffffffffffffffa8ffffffffffffffffffffffffd3a5ffffffffffffffffffffffffd624ffffffffffffffffffffffffffaaffffffffffffffffffffffffffacffffffffffffffffffffffe9ffaaffffffffffffffffffffffea3facffffffffffffffffffffffffffabffffffffffffffffffffffffffacffffffffffffffffffffffffd5a7ffffffffffffffffffffffffd628fffffffffffffffec3fa9fe9bfa9fffffffffffffffec3fa8feb7fb0fffffffffffffffffffa5fffffacfffffffffffffffffffa4fffffb3ffffffffffffffffffffffffffffffffffffffffa9ffffffffffffa5ffffffffffffffffffffffffffffffffffffffd3a5ffffffffffd9b1ffffffffffffffffffffffffffffffffffffffffaaffffffffffffa9ffffffffffffffffffffffffffffffffffffea7faaffffffffe97fb4fffffffffffffffffffffffffffffffffffffffffffffffa9fffffabfffffffffffffffffffffffffffffffffffffffffffffd4a5fffd7b4ffffffffffffffffffffffffffffffffffffffffffffffffffeabfadffffffffffffffffffffffffffffffffffffffffffffffffffffffb0
  | 5 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffa4ffffffffffffffffffffffffffffffffffffffffffffffffffffd227ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9ffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffacffffffffffffffffffffffffffffffffffffffffffffffffffffd5a8fffffffffffffffffffffffffffffffffffffffffffeabfa8fe9bfa4fffffffffffffffffffffffffffffffffffffffffffffffa6fffffabffffffffffffffffffffffffffffffffffffffffffffffffffffffa4ffffffffffffffffffffffffffffffffffffffffffffffffffffd3aaffffffffffffffffffffffffffffffffffffffffffffffffffffffacffffffffffffffffffffffffffffffffffffffffffffffffffeabfa8fffffffffffffffffffffffffffffffffb1fffffa0fffffa8fffffa7fffffffffffffffffffffffffffffffda31fffd628fffd3a4fffd6b0ffffffffffffffffffffffffffffffffffffea3fa8ffffffffeabfa9ffffffffffffffffffffffffffffffffffffffffa4ffffffffffffacffffffffffffffffffffffffffffffffffffffffffffffffffffffa2ffffffffffffffffffffffffffffffffffffffffffffffffffffd2a8ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffea3fabffffffffffffffffffffffffffffffffffffffffffffffffffffffacffffffffffffffffffffffffffffffffffffffffffffffffffffd528fffffffffffffffffffffffffffffffffffffffffffeabfa8fe9bfa4fffffffffffffffffffffffffffffffffffffffffffffffacfffffadffffffffffffa5ffffffffffff9effffffffffffa7ffffffffffffa4ffffffffffda32ffffffffffd828ffffffffffd227ffffffffffda2cffffffffffffafffffffffffffa8ffffffffffffa8ffffffffffffaeffffffffeaffaeffffffffe93faeffffffffe9ffaaffffffffeabfb6fffffffffffffffffffa8fffffa6fffffffffffffffffffaafffffaafffffffffffffffffd324fffd62efffffffffffffffffd527fffd836ffffffffffffffffffffffeabfa9ffffffffffffffffffffffeb7facffffffffffffffffffffffffffaaffffffffffffffffffffffffffb2ffffffffffffffffffffffffffffffffffffffffffffffffffffffa4ffffffffffffffffffffffffffffffffffffffffffffffffffffd227ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9ffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffacffffffffffffffffffffffffffffffffffffffffffffffffffffd5a8fffffffffffffffffffffffffffffffffffffffffffeabfa8fe9bfa4fffffffffffffffffffffffffffffffffffffffffffffffa6fffffabffffffffffffffffffffffffffffffffffffffffffffffffffffffa4ffffffffffffffffffffffffffffffffffffffffffffffffffffd3aaffffffffffffffffffffffffffffffffffffffffffffffffffffffacffffffffffffffffffffffffffffffffffffffffffffffffffeabfa8fffffffffffffffffffffffffffffffffb1fffffa0fffffa8fffffa7fffffffffffffffffffffffffffffffda31fffd628fffd3a4fffd6b0ffffffffffffffffffffffffffffffffffffea3fa8ffffffffeabfa9ffffffffffffffffffffffffffffffffffffffffa4ffffffffffffacffffffffffffffffffffffffffa2ffffffffffffffffffffffffffa0ffffffffffffffffffffffffd2a8ffffffffffffffffffffffffd525ffffffffffffffffffffffffffaaffffffffffffffffffffffffffaaffffffffffffffffffffffea3fabffffffffffffffffffffffe9bfb0ffffffffffffffffffffffffffacffffffffffffffffffffffffffaaffffffffffffffffffffffffd528ffffffffffffffffffffffffd426fffffffffffffffeabfa8fe9bfa4fffffffffffffffebbfa6fec7fb0fffffffffffffffffffacfffffadfffffffffffffffffffa2fffffb6ffffffffffffffffffffffffffffffffffffffffa7ffffffffffffa4ffffffffffffffffffffffffffffffffffffffd227ffffffffffda2cffffffffffffffffffffffffffffffffffffffffa8ffffffffffffaeffffffffffffffffffffffffffffffffffffe9ffaaffffffffeabfb6fffffffffffffffffffffffffffffffffffffffffffffffaafffffaafffffffffffffffffffffffffffffffffffffffffffffd527fffd836ffffffffffffffffffffffffffffffffffffffffffffffffffeb7facffffffffffffffffffffffffffffffffffffffffffffffffffffffb2
  | 6 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffffd3a4ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9ffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffabffffffffffffffffffffffffffffffffffffffffffffffffffffd5a7fffffffffffffffffffffffffffffffffffffffffffec3fa8fe9bfa9fffffffffffffffffffffffffffffffffffffffffffffffa4fffffabffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffffd3a5ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffea7faafffffffffffffffffffffffffffffffffadfffffa6fffffa8fffffaafffffffffffffffffffffffffffffffd8a9fffd5affffd424fffd733ffffffffffffffffffffffffffffffffffffe9bfa9ffffffffea7facffffffffffffffffffffffffffffffffffffffffabffffffffffffafffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffffd3a5ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9ffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffabffffffffffffffffffffffffffffffffffffffffffffffffffffd5a7fffffffffffffffffffffffffffffffffffffffffffec3fa9fe9bfa9fffffffffffffffffffffffffffffffffffffffffffffffa5fffffacffffffffffffabffffffffffffa4ffffffffffffa9ffffffffffffa5ffffffffffd834ffffffffffd930ffffffffffd3a5ffffffffffd9b1ffffffffffffb0ffffffffffffa8ffffffffffffaaffffffffffffa9ffffffffeb3fb0ffffffffe93fb3ffffffffea7faaffffffffe97fb4fffffffffffffffffffa8fffffaafffffffffffffffffffa9fffffabfffffffffffffffffd424fffd733fffffffffffffffffd4a5fffd7b4ffffffffffffffffffffffea7facffffffffffffffffffffffeabfadffffffffffffffffffffffffffafffffffffffffffffffffffffffb0ffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffffd3a4ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9ffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffabffffffffffffffffffffffffffffffffffffffffffffffffffffd5a7fffffffffffffffffffffffffffffffffffffffffffec3fa8fe9bfa9fffffffffffffffffffffffffffffffffffffffffffffffa4fffffabffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffffd3a5ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffea7faafffffffffffffffffffffffffffffffffadfffffa6fffffa8fffffaafffffffffffffffffffffffffffffffd8a9fffd5affffd424fffd733ffffffffffffffffffffffffffffffffffffe9bfa9ffffffffea7facffffffffffffffffffffffffffffffffffffffffabffffffffffffafffffffffffffffffffffffffffa7ffffffffffffffffffffffffffa8ffffffffffffffffffffffffd3a5ffffffffffffffffffffffffd624ffffffffffffffffffffffffffaaffffffffffffffffffffffffffacffffffffffffffffffffffe9ffaaffffffffffffffffffffffea3facffffffffffffffffffffffffffabffffffffffffffffffffffffffacffffffffffffffffffffffffd5a7ffffffffffffffffffffffffd628fffffffffffffffec3fa9fe9bfa9fffffffffffffffec3fa8feb7fb0fffffffffffffffffffa5fffffacfffffffffffffffffffa4fffffb3ffffffffffffffffffffffffffffffffffffffffa9ffffffffffffa5ffffffffffffffffffffffffffffffffffffffd3a5ffffffffffd9b1ffffffffffffffffffffffffffffffffffffffffaaffffffffffffa9ffffffffffffffffffffffffffffffffffffea7faaffffffffe97fb4fffffffffffffffffffffffffffffffffffffffffffffffa9fffffabfffffffffffffffffffffffffffffffffffffffffffffd4a5fffd7b4ffffffffffffffffffffffffffffffffffffffffffffffffffeabfadffffffffffffffffffffffffffffffffffffffffffffffffffffffb0
  | 7 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffa3ffffffffffffffffffffffffffffffffffffffffffffffffffffd227ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9ffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffacffffffffffffffffffffffffffffffffffffffffffffffffffffd5a8fffffffffffffffffffffffffffffffffffffffffffeabfa8fe9bfa4fffffffffffffffffffffffffffffffffffffffffffffffa5fffffabffffffffffffffffffffffffffffffffffffffffffffffffffffffa4ffffffffffffffffffffffffffffffffffffffffffffffffffffd329ffffffffffffffffffffffffffffffffffffffffffffffffffffffabffffffffffffffffffffffffffffffffffffffffffffffffffeabfa8fffffffffffffffffffffffffffffffffb0fffffa0fffffa8fffffa7fffffffffffffffffffffffffffffffd9b0fffd628fffd3a4fffd6b0ffffffffffffffffffffffffffffffffffffe9ffa8ffffffffeabfa9ffffffffffffffffffffffffffffffffffffffffa4ffffffffffffacffffffffffffffffffffffffffffffffffffffffffffffffffffffa2ffffffffffffffffffffffffffffffffffffffffffffffffffffd2a8ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffea3fabffffffffffffffffffffffffffffffffffffffffffffffffffffffacffffffffffffffffffffffffffffffffffffffffffffffffffffd528fffffffffffffffffffffffffffffffffffffffffffeabfa8fe9bfa4fffffffffffffffffffffffffffffffffffffffffffffffacfffffadffffffffffffa5ffffffffffff9effffffffffffa7ffffffffffffa4ffffffffffda32ffffffffffd828ffffffffffd227ffffffffffda2cffffffffffffafffffffffffffa8ffffffffffffa8ffffffffffffaeffffffffeaffaeffffffffe93faeffffffffe9ffaaffffffffeabfb6fffffffffffffffffffa8fffffa6fffffffffffffffffffaafffffaafffffffffffffffffd324fffd62efffffffffffffffffd527fffd836ffffffffffffffffffffffeabfa9ffffffffffffffffffffffeb7facffffffffffffffffffffffffffaaffffffffffffffffffffffffffb2ffffffffffffffffffffffffffffffffffffffffffffffffffffffa3ffffffffffffffffffffffffffffffffffffffffffffffffffffd227ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9ffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffacffffffffffffffffffffffffffffffffffffffffffffffffffffd5a8fffffffffffffffffffffffffffffffffffffffffffeabfa8fe9bfa4fffffffffffffffffffffffffffffffffffffffffffffffa5fffffabffffffffffffffffffffffffffffffffffffffffffffffffffffffa4ffffffffffffffffffffffffffffffffffffffffffffffffffffd329ffffffffffffffffffffffffffffffffffffffffffffffffffffffabffffffffffffffffffffffffffffffffffffffffffffffffffeabfa8fffffffffffffffffffffffffffffffffb0fffffa0fffffa8fffffa7fffffffffffffffffffffffffffffffd9b0fffd628fffd3a4fffd6b0ffffffffffffffffffffffffffffffffffffe9ffa8ffffffffeabfa9ffffffffffffffffffffffffffffffffffffffffa4ffffffffffffacffffffffffffffffffffffffffa2ffffffffffffffffffffffffffa0ffffffffffffffffffffffffd2a8ffffffffffffffffffffffffd525ffffffffffffffffffffffffffaaffffffffffffffffffffffffffaaffffffffffffffffffffffea3fabffffffffffffffffffffffe9bfb0ffffffffffffffffffffffffffacffffffffffffffffffffffffffaaffffffffffffffffffffffffd528ffffffffffffffffffffffffd426fffffffffffffffeabfa8fe9bfa4fffffffffffffffebbfa6fec7fb0fffffffffffffffffffacfffffadfffffffffffffffffffa2fffffb6ffffffffffffffffffffffffffffffffffffffffa7ffffffffffffa4ffffffffffffffffffffffffffffffffffffffd227ffffffffffda2cffffffffffffffffffffffffffffffffffffffffa8ffffffffffffaeffffffffffffffffffffffffffffffffffffe9ffaaffffffffeabfb6fffffffffffffffffffffffffffffffffffffffffffffffaafffffaafffffffffffffffffffffffffffffffffffffffffffffd527fffd836ffffffffffffffffffffffffffffffffffffffffffffffffffeb7facffffffffffffffffffffffffffffffffffffffffffffffffffffffb2
  | 8 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffa6ffffffffffffffffffffffffffffffffffffffffffffffffffffd4a7ffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffeaffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffd4a7fffffffffffffffffffffffffffffffffffffffffffec7fa6fe9bfaafffffffffffffffffffffffffffffffffffffffffffffffa8fffffacffffffffffffffffffffffffffffffffffffffffffffffffffffffa5ffffffffffffffffffffffffffffffffffffffffffffffffffffd4a7ffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffeabfaafffffffffffffffffffffffffffffffffaafffffa2fffffa8fffffa3fffffffffffffffffffffffffffffffd72cfffd630fffd4a7fffd6b1ffffffffffffffffffffffffffffffffffffe9bfaaffffffffe9ffabffffffffffffffffffffffffffffffffffffffffacffffffffffffadffffffffffffffffffffffffffffffffffffffffffffffffffffffa6ffffffffffffffffffffffffffffffffffffffffffffffffffffd4a7ffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffeaffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffd4a7fffffffffffffffffffffffffffffffffffffffffffec7fa6fe9bfabfffffffffffffffffffffffffffffffffffffffffffffffa8fffffacffffffffffffa5ffffffffffffa6ffffffffffffa6ffffffffffffa6ffffffffffdab3ffffffffffd828ffffffffffd4a7ffffffffffd828ffffffffffffacffffffffffffaaffffffffffffa9ffffffffffffaaffffffffeabfafffffffffeaffb0ffffffffeaffaaffffffffeaffb0fffffffffffffffffffa8fffffa3fffffffffffffffffffa8fffffa3fffffffffffffffffd4a7fffd6b1fffffffffffffffffd4a7fffd6b1ffffffffffffffffffffffe9ffabffffffffffffffffffffffe9ffabffffffffffffffffffffffffffadffffffffffffffffffffffffffadffffffffffffffffffffffffffffffffffffffffffffffffffffffa6ffffffffffffffffffffffffffffffffffffffffffffffffffffd4a7ffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffeaffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffd4a7fffffffffffffffffffffffffffffffffffffffffffec7fa6fe9bfaafffffffffffffffffffffffffffffffffffffffffffffffa8fffffacffffffffffffffffffffffffffffffffffffffffffffffffffffffa5ffffffffffffffffffffffffffffffffffffffffffffffffffffd4a7ffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffeabfaafffffffffffffffffffffffffffffffffaafffffa2fffffa8fffffa3fffffffffffffffffffffffffffffffd72cfffd630fffd4a7fffd6b1ffffffffffffffffffffffffffffffffffffe9bfaaffffffffe9ffabffffffffffffffffffffffffffffffffffffffffacffffffffffffadffffffffffffffffffffffffffa6ffffffffffffffffffffffffffa6ffffffffffffffffffffffffd4a7ffffffffffffffffffffffffd6a8ffffffffffffffffffffffffffa9ffffffffffffffffffffffffffaaffffffffffffffffffffffeaffaaffffffffffffffffffffffeaffb0ffffffffffffffffffffffffffa8ffffffffffffffffffffffffffa8ffffffffffffffffffffffffd4a7ffffffffffffffffffffffffd4a7fffffffffffffffec7fa6fe9bfabfffffffffffffffec7fa6fe9ffabfffffffffffffffffffa8fffffacfffffffffffffffffffa8fffffadffffffffffffffffffffffffffffffffffffffffa6ffffffffffffa6ffffffffffffffffffffffffffffffffffffffd4a7ffffffffffd828ffffffffffffffffffffffffffffffffffffffffa9ffffffffffffaaffffffffffffffffffffffffffffffffffffeaffaaffffffffeaffb0fffffffffffffffffffffffffffffffffffffffffffffffa8fffffa3fffffffffffffffffffffffffffffffffffffffffffffd4a7fffd6b1ffffffffffffffffffffffffffffffffffffffffffffffffffe9ffabffffffffffffffffffffffffffffffffffffffffffffffffffffffad
  | 9 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffa6ffffffffffffffffffffffffffffffffffffffffffffffffffffd3a4ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9bfaaffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffffd526fffffffffffffffffffffffffffffffffffffffffffebffa8fe9bfa9fffffffffffffffffffffffffffffffffffffffffffffffa4fffffabffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffffd3a5ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffea7faafffffffffffffffffffffffffffffffffadfffffa6fffffa8fffffaafffffffffffffffffffffffffffffffd8a9fffd5affffd424fffd733ffffffffffffffffffffffffffffffffffffe9bfa9ffffffffea7facffffffffffffffffffffffffffffffffffffffffabffffffffffffafffffffffffffffffffffffffffffffffffffffffffffffffffffffa6ffffffffffffffffffffffffffffffffffffffffffffffffffffd3a5ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9bfaaffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffffd526fffffffffffffffffffffffffffffffffffffffffffebffa8fe9bfa9fffffffffffffffffffffffffffffffffffffffffffffffa5fffffacffffffffffffabffffffffffffa4ffffffffffffa9ffffffffffffa5ffffffffffd834ffffffffffd930ffffffffffd3a5ffffffffffd9b1ffffffffffffb0ffffffffffffa8ffffffffffffaaffffffffffffa9ffffffffeb3fb0ffffffffe93fb3ffffffffea7faaffffffffe97fb4fffffffffffffffffffa8fffffaafffffffffffffffffffa9fffffabfffffffffffffffffd424fffd733fffffffffffffffffd4a5fffd7b4ffffffffffffffffffffffea7facffffffffffffffffffffffeabfadffffffffffffffffffffffffffafffffffffffffffffffffffffffb0ffffffffffffffffffffffffffffffffffffffffffffffffffffffa6ffffffffffffffffffffffffffffffffffffffffffffffffffffd3a4ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9bfaaffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffffd526fffffffffffffffffffffffffffffffffffffffffffebffa8fe9bfa9fffffffffffffffffffffffffffffffffffffffffffffffa4fffffabffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffffd3a5ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffea7faafffffffffffffffffffffffffffffffffadfffffa6fffffa8fffffaafffffffffffffffffffffffffffffffd8a9fffd5affffd424fffd733ffffffffffffffffffffffffffffffffffffe9bfa9ffffffffea7facffffffffffffffffffffffffffffffffffffffffabffffffffffffafffffffffffffffffffffffffffa6ffffffffffffffffffffffffffa7ffffffffffffffffffffffffd3a5ffffffffffffffffffffffffd624ffffffffffffffffffffffffffaaffffffffffffffffffffffffffabffffffffffffffffffffffe9bfaaffffffffffffffffffffffe9ffacffffffffffffffffffffffffffaaffffffffffffffffffffffffffabffffffffffffffffffffffffd526ffffffffffffffffffffffffd5a7fffffffffffffffebffa8fe9bfa9fffffffffffffffebffa8feb3faffffffffffffffffffffa5fffffacfffffffffffffffffffa4fffffb2ffffffffffffffffffffffffffffffffffffffffa9ffffffffffffa5ffffffffffffffffffffffffffffffffffffffd3a5ffffffffffd9b1ffffffffffffffffffffffffffffffffffffffffaaffffffffffffa9ffffffffffffffffffffffffffffffffffffea7faaffffffffe97fb4fffffffffffffffffffffffffffffffffffffffffffffffa9fffffabfffffffffffffffffffffffffffffffffffffffffffffd4a5fffd7b4ffffffffffffffffffffffffffffffffffffffffffffffffffeabfadffffffffffffffffffffffffffffffffffffffffffffffffffffffb0
  | 10 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffa1ffffffffffffffffffffffffffffffffffffffffffffffffffffd224ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9ffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffabffffffffffffffffffffffffffffffffffffffffffffffffffffd4a7fffffffffffffffffffffffffffffffffffffffffffea7fa7fe9bfa4fffffffffffffffffffffffffffffffffffffffffffffffa3fffffabffffffffffffffffffffffffffffffffffffffffffffffffffffffa4ffffffffffffffffffffffffffffffffffffffffffffffffffffd227ffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffea3fa8fffffffffffffffffffffffffffffffffaefffffa0fffffa8fffffa7fffffffffffffffffffffffffffffffd8aefffd4a8fffd3a4fffd6b0ffffffffffffffffffffffffffffffffffffe97fa7ffffffffeabfa9ffffffffffffffffffffffffffffffffffffffffa4ffffffffffffacffffffffffffffffffffffffffffffffffffffffffffffffffffffa1ffffffffffffffffffffffffffffffffffffffffffffffffffffd2a8ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9ffabffffffffffffffffffffffffffffffffffffffffffffffffffffffabffffffffffffffffffffffffffffffffffffffffffffffffffffd4a7fffffffffffffffffffffffffffffffffffffffffffea7fa7fe9bfa4fffffffffffffffffffffffffffffffffffffffffffffffacfffffadffffffffffffa5ffffffffffff9effffffffffffa7ffffffffffffa2ffffffffffda32ffffffffffd828ffffffffffd227ffffffffffd92bffffffffffffafffffffffffffa8ffffffffffffa8ffffffffffffacffffffffeaffaeffffffffe93faeffffffffe9ffaaffffffffea3fb4fffffffffffffffffffa8fffffa6fffffffffffffffffffa9fffffa9fffffffffffffffffd324fffd62efffffffffffffffffd4a6fffd734ffffffffffffffffffffffeabfa9ffffffffffffffffffffffeb3fabffffffffffffffffffffffffffaaffffffffffffffffffffffffffb0ffffffffffffffffffffffffffffffffffffffffffffffffffffffa1ffffffffffffffffffffffffffffffffffffffffffffffffffffd224ffffffffffffffffffffffffffffffffffffffffffffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffe9ffaaffffffffffffffffffffffffffffffffffffffffffffffffffffffabffffffffffffffffffffffffffffffffffffffffffffffffffffd4a7fffffffffffffffffffffffffffffffffffffffffffea7fa7fe9bfa4fffffffffffffffffffffffffffffffffffffffffffffffa3fffffabffffffffffffffffffffffffffffffffffffffffffffffffffffffa4ffffffffffffffffffffffffffffffffffffffffffffffffffffd227ffffffffffffffffffffffffffffffffffffffffffffffffffffffa9ffffffffffffffffffffffffffffffffffffffffffffffffffea3fa8fffffffffffffffffffffffffffffffffaefffffa0fffffa8fffffa7fffffffffffffffffffffffffffffffd8aefffd4a8fffd3a4fffd6b0ffffffffffffffffffffffffffffffffffffe97fa7ffffffffeabfa9ffffffffffffffffffffffffffffffffffffffffa4ffffffffffffacffffffffffffffffffffffffffa1ffffffffffffffffffffffffffa0ffffffffffffffffffffffffd2a8ffffffffffffffffffffffffd4a4ffffffffffffffffffffffffffaaffffffffffffffffffffffffffaaffffffffffffffffffffffe9ffabffffffffffffffffffffffe9bfafffffffffffffffffffffffffffabffffffffffffffffffffffffffaaffffffffffffffffffffffffd4a7ffffffffffffffffffffffffd426fffffffffffffffea7fa7fe9bfa4fffffffffffffffeb3fa6febffaefffffffffffffffffffacfffffadfffffffffffffffffffa2fffffb3ffffffffffffffffffffffffffffffffffffffffa7ffffffffffffa2ffffffffffffffffffffffffffffffffffffffd227ffffffffffd92bffffffffffffffffffffffffffffffffffffffffa8ffffffffffffacffffffffffffffffffffffffffffffffffffe9ffaaffffffffea3fb4fffffffffffffffffffffffffffffffffffffffffffffffa9fffffa9fffffffffffffffffffffffffffffffffffffffffffffd4a6fffd734ffffffffffffffffffffffffffffffffffffffffffffffffffeb3fabffffffffffffffffffffffffffffffffffffffffffffffffffffffb0
  | 11 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffa0ffffffffffffffffffffffffffffffffffffffffffffffffffffd223ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffe93faaffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffd3a4fffffffffffffffffffffffffffffffffffffffffffe9ffa5fe9bfa4fffffffffffffffffffffffffffffffffffffffffffffffa2fffffabffffffffffffffffffffffffffffffffffffffffffffffffffffffa3ffffffffffffffffffffffffffffffffffffffffffffffffffffd225ffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffe9ffa7fffffffffffffffffffffffffffffffffadfffffa0fffffa8fffffa5fffffffffffffffffffffffffffffffd829fffd4a8fffd324fffd62effffffffffffffffffffffffffffffffffffe93fa4ffffffffea3fa8ffffffffffffffffffffffffffffffffffffffffa4ffffffffffffaaffffffffffffffffffffffffffffffffffffffffffffffffffffff9fffffffffffffffffffffffffffffffffffffffffffffffffffffd2a5ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffe93faaffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffd3a4fffffffffffffffffffffffffffffffffffffffffffe9ffa5fe9bfa4fffffffffffffffffffffffffffffffffffffffffffffffa5fffffaaffffffffffffa4ffffffffffff9effffffffffffa7ffffffffffffa0ffffffffffd7afffffffffffd727ffffffffffd225ffffffffffd7a8ffffffffffffaeffffffffffffa8ffffffffffffa7ffffffffffffa8ffffffffeabfabffffffffe93facffffffffe9ffaaffffffffe93faefffffffffffffffffffa8fffffa5fffffffffffffffffffa8fffffa6fffffffffffffffffd324fffd5adfffffffffffffffffd3a4fffd62fffffffffffffffffffffffea3fa8ffffffffffffffffffffffea3fa8ffffffffffffffffffffffffffa9ffffffffffffffffffffffffffabffffffffffffffffffffffffffffffffffffffffffffffffffffffa0ffffffffffffffffffffffffffffffffffffffffffffffffffffd223ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffe93faaffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffffd3a4fffffffffffffffffffffffffffffffffffffffffffe9ffa5fe9bfa4fffffffffffffffffffffffffffffffffffffffffffffffa2fffffabffffffffffffffffffffffffffffffffffffffffffffffffffffffa3ffffffffffffffffffffffffffffffffffffffffffffffffffffd225ffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffe9ffa7fffffffffffffffffffffffffffffffffadfffffa0fffffa8fffffa5fffffffffffffffffffffffffffffffd829fffd4a8fffd324fffd62effffffffffffffffffffffffffffffffffffe93fa4ffffffffea3fa8ffffffffffffffffffffffffffffffffffffffffa4ffffffffffffaaffffffffffffffffffffffffff9fffffffffffffffffffffffffffa0ffffffffffffffffffffffffd2a5ffffffffffffffffffffffffd4a3ffffffffffffffffffffffffffa8ffffffffffffffffffffffffffa8ffffffffffffffffffffffe93faaffffffffffffffffffffffe93facffffffffffffffffffffffffffa8ffffffffffffffffffffffffffa8ffffffffffffffffffffffffd3a4ffffffffffffffffffffffffd3a4fffffffffffffffe9ffa5fe9bfa4fffffffffffffffea3fa5fea3fa9fffffffffffffffffffa5fffffaafffffffffffffffffffa2fffffacffffffffffffffffffffffffffffffffffffffffa7ffffffffffffa0ffffffffffffffffffffffffffffffffffffffd225ffffffffffd7a8ffffffffffffffffffffffffffffffffffffffffa7ffffffffffffa8ffffffffffffffffffffffffffffffffffffe9ffaaffffffffe93faefffffffffffffffffffffffffffffffffffffffffffffffa8fffffa6fffffffffffffffffffffffffffffffffffffffffffffd3a4fffd62fffffffffffffffffffffffffffffffffffffffffffffffffffea3fa8ffffffffffffffffffffffffffffffffffffffffffffffffffffffab
  | 12 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffa0ffffffffffffffffffffffffffffffffffffffffffffffffffffd223ffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffe8ffa6ffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffffd225fffffffffffffffffffffffffffffffffffffffffffe9ffa4fea3fa4fffffffffffffffffffffffffffffffffffffffffffffffa2fffffa5ffffffffffffffffffffffffffffffffffffffffffffffffffffffa3ffffffffffffffffffffffffffffffffffffffffffffffffffffd227ffffffffffffffffffffffffffffffffffffffffffffffffffffffa6ffffffffffffffffffffffffffffffffffffffffffffffffffe9ffa4fffffffffffffffffffffffffffffffffacfffffa2fffffa7fffffa3fffffffffffffffffffffffffffffffd72afffd426fffd225fffd3a8ffffffffffffffffffffffffffffffffffffe97fa4ffffffffea7fa5ffffffffffffffffffffffffffffffffffffffffa3ffffffffffffa5ffffffffffffffffffffffffffffffffffffffffffffffffffffffa0ffffffffffffffffffffffffffffffffffffffffffffffffffffd226ffffffffffffffffffffffffffffffffffffffffffffffffffffffa8ffffffffffffffffffffffffffffffffffffffffffffffffffe93fa6ffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffffd225fffffffffffffffffffffffffffffffffffffffffffe9ffa4fea3fa4fffffffffffffffffffffffffffffffffffffffffffffffa8fffffa5ffffffffffffa3ffffffffffffa0ffffffffffffa6ffffffffffffa0ffffffffffd629ffffffffffd426ffffffffffd227ffffffffffd426ffffffffffffacffffffffffffa8ffffffffffffa6ffffffffffffa8ffffffffea3fa6ffffffffe93fa6ffffffffe9ffa9ffffffffe93fa7fffffffffffffffffffa7fffffa3fffffffffffffffffffa7fffffa3fffffffffffffffffd225fffd3a8fffffffffffffffffd225fffd3a9ffffffffffffffffffffffea7fa6ffffffffffffffffffffffea7fa5ffffffffffffffffffffffffffa5ffffffffffffffffffffffffffa6ffffffffffffffffffffffffffffffffffffffffffffffffffffffa0ffffffffffffffffffffffffffffffffffffffffffffffffffffd223ffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffe8ffa6ffffffffffffffffffffffffffffffffffffffffffffffffffffffa7ffffffffffffffffffffffffffffffffffffffffffffffffffffd225fffffffffffffffffffffffffffffffffffffffffffe9ffa4fea3fa4fffffffffffffffffffffffffffffffffffffffffffffffa2fffffa5ffffffffffffffffffffffffffffffffffffffffffffffffffffffa3ffffffffffffffffffffffffffffffffffffffffffffffffffffd227ffffffffffffffffffffffffffffffffffffffffffffffffffffffa6ffffffffffffffffffffffffffffffffffffffffffffffffffe9ffa4fffffffffffffffffffffffffffffffffacfffffa2fffffa7fffffa3fffffffffffffffffffffffffffffffd72afffd426fffd225fffd3a8ffffffffffffffffffffffffffffffffffffe97fa4ffffffffea7fa5ffffffffffffffffffffffffffffffffffffffffa3ffffffffffffa5ffffffffffffffffffffffffffa0ffffffffffffffffffffffffffa0ffffffffffffffffffffffffd226ffffffffffffffffffffffffd423ffffffffffffffffffffffffffa8ffffffffffffffffffffffffffa7ffffffffffffffffffffffe93fa6ffffffffffffffffffffffe8ffa7ffffffffffffffffffffffffffa7ffffffffffffffffffffffffffa7ffffffffffffffffffffffffd225ffffffffffffffffffffffffd225fffffffffffffffe9ffa4fea3fa4fffffffffffffffe9ffa4fea7fa5fffffffffffffffffffa8fffffa5fffffffffffffffffffa2fffffa6ffffffffffffffffffffffffffffffffffffffffa6ffffffffffffa0ffffffffffffffffffffffffffffffffffffffd227ffffffffffd426ffffffffffffffffffffffffffffffffffffffffa6ffffffffffffa8ffffffffffffffffffffffffffffffffffffe9ffa9ffffffffe93fa7fffffffffffffffffffffffffffffffffffffffffffffffa7fffffa3fffffffffffffffffffffffffffffffffffffffffffffd225fffd3a9ffffffffffffffffffffffffffffffffffffffffffffffffffea7fa5ffffffffffffffffffffffffffffffffffffffffffffffffffffffa6
  | 13 => 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffa0ffffffffffffffffffffffffffffffffffffffffffffffffffffd223ffffffffffffffffffffffffffffffffffffffffffffffffffffffa5ffffffffffffffffffffffffffffffffffffffffffffffffffe8bfa3ffffffffffffffffffffffffffffffffffffffffffffffffffffffa3ffffffffffffffffffffffffffffffffffffffffffffffffffffd224fffffffffffffffffffffffffffffffffffffffffffe97fa2fe97fa4fffffffffffffffffffffffffffffffffffffffffffffffa3fffffa3ffffffffffffffffffffffffffffffffffffffffffffffffffffffa3ffffffffffffffffffffffffffffffffffffffffffffffffffffd224ffffffffffffffffffffffffffffffffffffffffffffffffffffffa3ffffffffffffffffffffffffffffffffffffffffffffffffffe8ffa3fffffffffffffffffffffffffffffffffa6fffffa3fffffa3fffffa2fffffffffffffffffffffffffffffffd3a5fffd3a4fffd226fffd224ffffffffffffffffffffffffffffffffffffe8ffa4ffffffffe97fa4ffffffffffffffffffffffffffffffffffffffffa3ffffffffffffa3ffffffffffffffffffffffffffffffffffffffffffffffffffffffa0ffffffffffffffffffffffffffffffffffffffffffffffffffffd224ffffffffffffffffffffffffffffffffffffffffffffffffffffffa5ffffffffffffffffffffffffffffffffffffffffffffffffffe8bfa3ffffffffffffffffffffffffffffffffffffffffffffffffffffffa3ffffffffffffffffffffffffffffffffffffffffffffffffffffd225fffffffffffffffffffffffffffffffffffffffffffe97fa2fe97fa4fffffffffffffffffffffffffffffffffffffffffffffffa4fffffa3ffffffffffffa3ffffffffffffa0ffffffffffffa3ffffffffffffa0ffffffffffd3a4ffffffffffd224ffffffffffd227ffffffffffd224ffffffffffffa6ffffffffffffa5ffffffffffffa3ffffffffffffa5ffffffffe9ffa3ffffffffe8bfa3ffffffffe8ffa6ffffffffe8bfa3fffffffffffffffffffa3fffffa2fffffffffffffffffffa3fffffa2fffffffffffffffffd226fffd224fffffffffffffffffd226fffd224ffffffffffffffffffffffe97fa4ffffffffffffffffffffffe97fa4ffffffffffffffffffffffffffa3ffffffffffffffffffffffffffa3ffffffffffffffffffffffffffffffffffffffffffffffffffffffa0ffffffffffffffffffffffffffffffffffffffffffffffffffffd223ffffffffffffffffffffffffffffffffffffffffffffffffffffffa5ffffffffffffffffffffffffffffffffffffffffffffffffffe8bfa3ffffffffffffffffffffffffffffffffffffffffffffffffffffffa3ffffffffffffffffffffffffffffffffffffffffffffffffffffd224fffffffffffffffffffffffffffffffffffffffffffe97fa2fe97fa4fffffffffffffffffffffffffffffffffffffffffffffffa3fffffa3ffffffffffffffffffffffffffffffffffffffffffffffffffffffa3ffffffffffffffffffffffffffffffffffffffffffffffffffffd224ffffffffffffffffffffffffffffffffffffffffffffffffffffffa3ffffffffffffffffffffffffffffffffffffffffffffffffffe8ffa3fffffffffffffffffffffffffffffffffa6fffffa3fffffa3fffffa2fffffffffffffffffffffffffffffffd3a5fffd3a4fffd226fffd224ffffffffffffffffffffffffffffffffffffe8ffa4ffffffffe97fa4ffffffffffffffffffffffffffffffffffffffffa3ffffffffffffa3ffffffffffffffffffffffffffa0ffffffffffffffffffffffffffa0ffffffffffffffffffffffffd224ffffffffffffffffffffffffd223ffffffffffffffffffffffffffa5ffffffffffffffffffffffffffa5ffffffffffffffffffffffe8bfa3ffffffffffffffffffffffe8bfa3ffffffffffffffffffffffffffa3ffffffffffffffffffffffffffa3ffffffffffffffffffffffffd225ffffffffffffffffffffffffd224fffffffffffffffe97fa2fe97fa4fffffffffffffffe97fa2fe97fa4fffffffffffffffffffa4fffffa3fffffffffffffffffffa3fffffa3ffffffffffffffffffffffffffffffffffffffffa3ffffffffffffa0ffffffffffffffffffffffffffffffffffffffd227ffffffffffd224ffffffffffffffffffffffffffffffffffffffffa3ffffffffffffa5ffffffffffffffffffffffffffffffffffffe8ffa6ffffffffe8bfa3fffffffffffffffffffffffffffffffffffffffffffffffa3fffffa2fffffffffffffffffffffffffffffffffffffffffffffd226fffd224ffffffffffffffffffffffffffffffffffffffffffffffffffe97fa4ffffffffffffffffffffffffffffffffffffffffffffffffffffffa3
  | _ => 0

def meet (i b k : ℕ) : ℕ := (packedMeet i >>> (7*(b*32+k))) &&& 127
end GridStrip

end

section

namespace GridStrip

/-- Unroll the five terms so the kernel can evaluate the certificate functions directly. -/
def sum5 (f : ℕ → ℕ) : ℕ := f 0 + f 1 + f 2 + f 3 + f 4

private theorem sum5_eq (f : ℕ → ℕ) : sum5 f = ∑ y ∈ Finset.range 5, f y := by
  simp [sum5, Finset.sum_range_succ]

/-- A neighbor mask on either side of the current column can be completed if each
unpainted cell has either one or two painted neighbors already accounted for. -/
def admissibleHalf (b z : ℕ) : Bool :=
  (List.range 5).all fun y =>
    decide (bit b y = 1 ∨ (1 ≤ vertical b y + bit z y ∧ vertical b y + bit z y ≤ 2))

def keyPrev (b z : ℕ) : ℕ := sum5 fun y =>
  if bit b y = 0 ∧ vertical b y = 1 then 2^y * bit z y else 0

def keyNext (b z : ℕ) : ℕ := sum5 fun y =>
  if bit b y = 0 ∧ vertical b y = 1 then 2^y * (1-bit z y) else 0

def base (d : ℕ) (o : Bool) (b : ℕ) : ℕ :=
  (sum5 fun y => w d y o * bit b y *
    ((if y=0 then 1 else 0) + (if d=0 then 1 else 0) + vertical b y)) + deposit d b

def burden (d : ℕ) (o : Bool) (b z : ℕ) : ℕ :=
  sum5 fun y => w d y o * bit b y * bit z y

private theorem legal_at {a b c : ℕ} (good : legal a b c=true) {y : ℕ} (hy : y < 5) :
    bit b y=1 ∨ bit a y + bit c y + vertical b y = 2 :=
  of_decide_eq_true (List.all_eq_true.mp good y (List.mem_range.mpr hy))

theorem pair_constraints {a b c : ℕ} (good : legal a b c = true) :
    admissibleHalf b a = true ∧ admissibleHalf b c = true ∧ keyPrev b a = keyNext b c := by
  have atCell (y : ℕ) (hy : y < 5) := @legal_at a b c good y hy
  have bitLe (z y : ℕ) : bit z y ≤ 1 := Nat.and_le_right
  constructor
  · apply List.all_eq_true.mpr
    intro y hy
    apply decide_eq_true
    have valid := atCell y (List.mem_range.mp hy)
    have := bitLe c y
    omega
  constructor
  · apply List.all_eq_true.mpr
    intro y hy
    apply decide_eq_true
    have valid := atCell y (List.mem_range.mp hy)
    have := bitLe a y
    omega
  · simp only [keyPrev, keyNext, sum5_eq]
    apply Finset.sum_congr rfl
    intro y hy
    split_ifs with unary
    · have valid := atCell y (Finset.mem_range.mp hy)
      congr 1
      obtain ⟨white, single⟩ := unary
      omega
    · rfl

theorem split_charge (d : ℕ) (o : Bool) (a b c : ℕ) :
    charge d o a b c = base d o b + burden d o b a + burden d o b c := by
  simp only [charge, rawCost, base, burden, sum5_eq]
  rw [show (∑ y ∈ Finset.range 5, w d y o * bit b y *
        ((if y=0 then 1 else 0)+(if d=0 then 1 else 0)+bit a y+bit c y+vertical b y))
    = (∑ y ∈ Finset.range 5, w d y o * bit b y *
        ((if y=0 then 1 else 0)+(if d=0 then 1 else 0)+vertical b y)) +
      (∑ y ∈ Finset.range 5, w d y o * bit b y * bit a y) +
      (∑ y ∈ Finset.range 5, w d y o * bit b y * bit c y) by
        simp only [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro y _
        ring]
  omega

theorem stageGood_of_pairs (before after : ℕ → ℕ) (mid : ℕ → ℕ → ℕ) (d : ℕ) (o : Bool)
    (prev : ∀ a < 64, ∀ b < 64, admissibleHalf b a = true →
      4+before (a*64+b) ≤ base d o b + burden d o b a + mid b (keyPrev b a))
    (next : ∀ b < 64, ∀ c < 64, admissibleHalf b c = true →
      mid b (keyNext b c) ≤ burden d o b c + after (b*64+c)) :
    stageGood before after d o := by
  intro a ha b hb c hc good
  obtain ⟨left,right,same⟩ := pair_constraints good
  have p := prev a ha b hb left
  have q := next b hb c hc right
  rw [same] at p
  rw [split_charge]
  omega

end GridStrip

end

section

namespace GridStrip
def checkPair (i src dst d : ℕ) (o : Bool) (b z : ℕ) : Bool :=
  if admissibleHalf b z then
    decide (4 + potential src (z*64+b) ≤ base d o b + burden d o b z + meet i b (keyPrev b z) ∧
      meet i b (keyNext b z) ≤ burden d o b z + potential dst (b*64+z))
  else true

def checkAt (i src dst d : ℕ) (o : Bool) (b : ℕ) :=
  (List.range 64).all (fun z => checkPair i src dst d o b z)

theorem stage_of_rows (i src dst d : ℕ) (o : Bool)
    (rows : (List.range 64).all (checkAt i src dst d o) = true) :
    stageGood (potential src) (potential dst) d o := by
  have get {b z : ℕ} (hb : b < 64) (hz : z < 64) (h : admissibleHalf b z = true) := by
    have all := List.all_eq_true.mp rows b (List.mem_range.mpr hb)
    have one := List.all_eq_true.mp all z (List.mem_range.mpr hz)
    simpa [checkPair,h] using one
  apply stageGood_of_pairs _ _ (meet i) _ _
  · intro a ha b hb h
    exact (get hb ha h).1
  · intro b hb c hc h
    exact (get hb hc h).2

end GridStrip

end

section

namespace GridStrip

private theorem stage0 : stageGood (potential 1) (potential 0) 0 false :=
  stage_of_rows 0 1 0 0 false (by decide +kernel)

private theorem stage1 : stageGood (potential 2) (potential 1) 1 false :=
  stage_of_rows 1 2 1 1 false (by decide +kernel)

private theorem stage2 : stageGood (potential 3) (potential 2) 2 false :=
  stage_of_rows 2 3 2 2 false (by decide +kernel)

private theorem stage3 : stageGood (potential 4) (potential 3) 3 false :=
  stage_of_rows 3 4 3 3 false (by decide +kernel)

private theorem stage4 : stageGood (potential 5) (potential 4) 4 false :=
  stage_of_rows 4 5 4 4 false (by decide +kernel)

private theorem stage5 : stageGood (potential 5) (potential 5) 5 false :=
  stage_of_rows 5 5 5 5 false (by decide +kernel)

private theorem stage6 : stageGood (potential 6) (potential 4) 4 true :=
  stage_of_rows 6 6 4 4 true (by decide +kernel)

private theorem stage7 : stageGood (potential 6) (potential 5) 4 false :=
  stage_of_rows 7 6 5 4 false (by decide +kernel)

private theorem stage8 : stageGood (potential 7) (potential 3) 3 true :=
  stage_of_rows 8 7 3 3 true (by decide +kernel)

private theorem stage9 : stageGood (potential 7) (potential 4) 3 false :=
  stage_of_rows 9 7 4 3 false (by decide +kernel)

private theorem stage10 : stageGood (potential 7) (potential 6) 3 false :=
  stage_of_rows 10 7 6 3 false (by decide +kernel)

private theorem stage11 : stageGood (potential 8) (potential 7) 2 false :=
  stage_of_rows 11 8 7 2 false (by decide +kernel)

private theorem stage12 : stageGood (potential 9) (potential 8) 1 false :=
  stage_of_rows 12 9 8 1 false (by decide +kernel)

private theorem stage13 : stageGood (potential 10) (potential 9) 0 false :=
  stage_of_rows 13 10 9 0 false (by decide +kernel)

theorem cert_steps : ∀ a b d o, (a,b,d,o) ∈ stationaryArcs → stageGood (R a) (R b) d o := by
  have h : ∀ t ∈ stationaryArcs, stageGood (R t.1) (R t.2.1) t.2.2.1 t.2.2.2 := by
    simp only [stationaryArcs, List.forall_mem_cons, List.not_mem_nil, false_implies,
      implies_true, and_true]
    exact ⟨stage0, stage1, stage2, stage3, stage4, stage4, stage5, stage7, stage10, stage11, stage12, stage13, stage8, stage11, stage12, stage13, stage9, stage11, stage12, stage13, stage6, stage10, stage11, stage12, stage13⟩
  intro a b d o hmem
  exact h (a,b,d,o) hmem

end GridStrip

end

section

namespace GridStrip

/-- Row of the stationary potential before a step at position x. -/
def route (n x : ℕ) : ℕ := match n with
  | 7 => [16, 15, 14, 13, 3, 2, 1, 0][x]?.getD 0
  | 8 => [20, 19, 18, 17, 4, 3, 2, 1, 0][x]?.getD 0
  | 9 => [25, 24, 23, 22, 21, 4, 3, 2, 1, 0][x]?.getD 0
  | _ => if x < 5 then 12-x else if x+5≤n then 6 else n-x

private theorem short7 : ∀ x : Fin 7,
    (route 7 x,route 7 (x.val+1),depth 7 x,omitCenter 7 x) ∈ stationaryArcs := by decide +kernel
private theorem short8 : ∀ x : Fin 8,
    (route 8 x,route 8 (x.val+1),depth 8 x,omitCenter 8 x) ∈ stationaryArcs := by decide +kernel
private theorem short9 : ∀ x : Fin 9,
    (route 9 x,route 9 (x.val+1),depth 9 x,omitCenter 9 x) ∈ stationaryArcs := by decide +kernel

private theorem longRoute {n x : ℕ} (hn : 10≤n) :
    route n x = if x < 5 then 12-x else if x+5≤n then 6 else n-x := by
  unfold route
  split <;> first | rfl | omega

/-- The stationary row repeats throughout the middle of every long word.
The two tapers and the short words use explicitly listed certificate arcs. -/
theorem route_arc {n x : ℕ} (hn : 7≤n) (hx : x < n) :
    (route n x,route n (x+1),depth n x,omitCenter n x) ∈ stationaryArcs := by
  by_cases short : n < 10
  · have eq : n=7 ∨ n=8 ∨ n=9 := by omega
    rcases eq with rfl | rfl | rfl
    · exact short7 ⟨x,hx⟩
    · exact short8 ⟨x,hx⟩
    · exact short9 ⟨x,hx⟩
  have big : 10≤n := by omega
  have noSkip : omitCenter n x = false := by simp [omitCenter]; omega
  rw [longRoute big,longRoute big,noSkip]
  by_cases small : x < 5
  · have dep : depth n x = x := by unfold depth; omega
    rw [dep]
    interval_cases x <;> simp [stationaryArcs]
    all_goals omega
  · by_cases mid : x+5 < n
    · have dep : depth n x=5 := by unfold depth; omega
      have sx : ¬x+1 < 5 := by omega
      have l1 : x+5≤n := by omega
      have l2 : x+1+5≤n := by omega
      simp [small,sx,l1,l2,dep,stationaryArcs]
    · by_cases seam : x+5=n
      · have dep : depth n x=4 := by unfold depth; omega
        have sx : ¬x+1 < 5 := by omega
        have l1 : x+5≤n := by omega
        have l2 : ¬x+1+5≤n := by omega
        have e : n-(x+1)=4 := by omega
        simp [small,sx,l1,l2,e,dep,stationaryArcs]
      · have sx : ¬x+1 < 5 := by omega
        have l1 : ¬x+5≤n := by omega
        have l2 : ¬x+1+5≤n := by omega
        simp only [small,sx,l1,l2,if_false]
        have dep : depth n x = n-(x+1) := by unfold depth; omega
        rw [dep]
        have a : n-x=n-(x+1)+1 := by omega
        rw [a]
        have k : n-(x+1) < 4 := by omega
        generalize n-(x+1)=r at *
        interval_cases r <;> decide

private theorem route_start {n : ℕ} (hn : 7≤n) : route n 0 ∈ [12,16,20,25] := by
  by_cases small : n < 10
  · interval_cases n <;> decide
  · have b : 10≤n := by omega
    simp [longRoute b]

private theorem route_finish {n : ℕ} (hn : 7≤n) : route n n=0 := by
  by_cases small : n < 10
  · interval_cases n <;> decide
  · have b : 10≤n := by omega
    have h : ¬n < 5 := by omega
    simp [longRoute b,h]

/-- A 26-row finite certificate for the boundary automaton suffices for *all*
side lengths. The terminal ghost is column zero and the initial ghost is row
zero, so the six-unit difference of their potentials is the entire boundary loss. -/
theorem word_bound_of_certificate (R : ℕ → ℕ → ℕ)
    (good : ∀ a b d o, (a,b,d,o) ∈ stationaryArcs → stageGood (R a) (R b) d o)
    (starts : ∀ a ∈ [12,16,20,25], ∀ b < 64, 34≤R a b)
    (finish : ∀ a < 64, R 0 (a*64) ≤ 40)
    (n : ℕ) (hn : 7≤n) (m : ℕ → ℕ) (masks : ∀ x ≤ n+1, m x < 64)
    (ghostL : m 0 = 0) (ghostR : m (n+1)=0)
    (valid : ∀ x < n, legal (m x) (m (x+1)) (m (x+2)) = true) :
    4*n ≤ (∑ x ∈ Finset.range n, charge (depth n x) (omitCenter n x)
      (m x) (m (x+1)) (m (x+2))) + 6 := by
  have E := telescope m (fun x => R (route n x)) (depth n) (omitCenter n) masks valid
    (fun x hx => good _ _ _ _ (route_arc hn hx))
  have a := starts _ (route_start hn) (m 1) (masks _ (by omega))
  have b := finish (m n) (masks _ (by omega))
  simp only [ghostL,ghostR,route_finish hn, Nat.zero_mul,Nat.zero_add,Nat.add_zero] at E
  omega

end GridStrip

end

section

namespace GridStrip

/-- The corrected loss of any legal width-six side of a square is at least four
per column, with a total endpoint allowance of six. -/
theorem word_bound {n : ℕ} (hn : 7 ≤ n) (m : ℕ → ℕ) (ghost₀ : m 0 = 0)
    (ghost₁ : m (n+1) = 0) (masks : ∀ x ≤ n+1, m x < 64)
    (valid : ∀ x < n, legal (m x) (m (x+1)) (m (x+2)) = true) :
    4*n ≤ (∑ x ∈ Finset.range n, charge (depth n x) (omitCenter n x)
      (m x) (m (x+1)) (m (x+2)))+6 :=
  word_bound_of_certificate R cert_steps cert_starts cert_finish n hn m masks ghost₀ ghost₁ valid

end GridStrip

end

section

open OMA.S_oeis_a344719

theorem FairGrid.sharp_lower {n : ℕ} (hn : 7≤n) (P : Finset (Cell n)) (fair : Fair P) :
    n^2+4*n ≤ 3*P.card+14 :=
  FairGrid.lower_of_word_bound hn P fair (fun m masks left right ok =>
    GridStrip.word_bound hn m left right masks ok)

end

theorem OMA.solution : type_of% @OMA.S_oeis_a344719.main :=
  OMA.A344719Series.remaining.mpr (fun _ hn P fair => FairGrid.sharp_lower hn P fair)
