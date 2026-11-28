import OMAStatements.S_oeis_a179004
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Maximum density in stable binary rectangles

R. H. Hardin posed the limiting-density conjecture in OEIS A179004 in January 2011.
The registered statement is from lefttosolve2/open-math-agents PR 2232.

The three diagonal phases each use two of every three interior cells. Complementing
the nearest inner line along each edge makes the perimeter stable. Summing the
three scores counts the corner corrections exactly. For the upper bound, count
edges joining unlike colors from both endpoints. Only the four corners can have
a single opposite neighbor when their value is one. Both resulting finite bounds
are included below.
-/

section
namespace GridAnti.Hardin

/-- Project the outermost coordinate onto the adjacent interior coordinate. -/
def coreCoord (n i : ℕ) : ℕ := min (n-2) (max 1 i)

def rim (n i : ℕ) : Bool := decide (i=0 ∨ i+1=n)

/-- A phase of the diagonal stripe pattern, complemented across each outer edge. -/
def collar {n m : ℕ} (t : Fin 3) (v : GridAnti.Cell n m) : Bool :=
  (decide ((coreCoord n v.1.val + coreCoord m v.2.val + t.val)%3 ≠ 0) ^^
    rim n v.1.val) ^^ rim m v.2.val

end GridAnti.Hardin
end

section
namespace GridAnti.Hardin

/-- Restriction to one coordinate direction. The remaining coordinate contributes a phase and a constant complement. -/
def line (n s i : ℕ) : Bool := decide ((coreCoord n i+s)%3 ≠ 0) ^^ rim n i

theorem core_inside {n i : ℕ} (hl : 1 ≤ i) (hr : i+1 < n) : coreCoord n i=i := by
  unfold coreCoord
  omega

theorem rim_inside {n i : ℕ} (hl : 1 ≤ i) (hr : i+1 < n) : rim n i=false := by
  simp [rim, show i≠0 by omega, show i+1≠n by omega]

private theorem line_inside {n s i : ℕ} (hl : 1 ≤ i) (hr : i+1<n) :
    line n s i = decide ((i+s)%3 ≠ 0) := by
  simp [line,core_inside hl hr,rim_inside hl hr]

private theorem endpoint_pairs {n : ℕ} (hn : 5≤n) (s : ℕ) :
    line n s 0 ≠ line n s 1 ∧ line n s (n-1) ≠ line n s (n-2) := by
  have a0 : coreCoord n 0 = coreCoord n 1 := by unfold coreCoord; omega
  have aN : coreCoord n (n-1) = coreCoord n (n-2) := by unfold coreCoord; omega
  have b0 : rim n 0 = true := by simp [rim]
  have b1 := @rim_inside n 1 (by omega) (by omega)
  have bN : rim n (n-1) = true := by simp [rim, show n-1+1=n by omega]
  have bM := @rim_inside n (n-2) (by omega) (by omega)
  have flip (z : Bool) : (z ^^ true) ≠ (z ^^ false) := by cases z <;> decide
  constructor
  · unfold line
    rw [a0,b0,b1]
    exact flip _
  · unfold line
    rw [aN,bN,bM]
    exact flip _

theorem line_neighbor {n : ℕ} (hn : 5≤n) (s : ℕ) (i : Fin n) :
    ∃ j : Fin n, (j.val+1=i.val ∨ i.val+1=j.val) ∧ line n s j.val ≠ line n s i.val := by
  have hi:=i.isLt
  obtain ⟨L,R⟩ := endpoint_pairs hn s
  by_cases h0 : i.val=0
  · exact ⟨⟨1,by omega⟩,Or.inr (by change i.val+1=1; omega),h0 ▸ Ne.symm L⟩
  by_cases h1 : i.val=1
  · exact ⟨⟨0,by omega⟩,Or.inl (by change 0+1=i.val; omega),h1 ▸ L⟩
  by_cases hN : i.val=n-1
  · exact ⟨⟨n-2,by omega⟩,Or.inl (by change n-2+1=i.val; omega),hN ▸ Ne.symm R⟩
  by_cases hM : i.val=n-2
  · exact ⟨⟨n-1,by omega⟩,Or.inr (by change i.val+1=n-1; omega),hM ▸ R⟩
  have I := @line_inside n s i.val (by omega) (by omega)
  by_cases hc : (i.val+s)%3=1
  · refine ⟨⟨i.val-1,by omega⟩,Or.inl (by change i.val-1+1=i.val; omega),?_⟩
    change line n s (i.val-1) ≠ line n s i.val
    rw [I,line_inside (by omega) (by omega)]
    have hz : (i.val-1+s)%3=0 := by omega
    simp [hc,hz]
  · refine ⟨⟨i.val+1,by omega⟩,Or.inr rfl,?_⟩
    change line n s (i.val+1) ≠ line n s i.val
    rw [I,line_inside (by omega) (by omega)]
    by_cases hz : (i.val+s)%3=0
    · have ht : (i.val+1+s)%3≠0 := by omega
      simp [hz,ht]
    · have ht : (i.val+1+s)%3=0 := by omega
      simp [hz,ht]

end GridAnti.Hardin
end

section
namespace GridAnti.Hardin

private theorem xor_swap (a b c : Bool) : ((a ^^ b) ^^ c) = ((a ^^ c) ^^ b) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem along_first {n m : ℕ} (t : Fin 3) (i : Fin n) (j : Fin m) :
    collar t (i,j) = (line n (coreCoord m j.val+t.val) i.val ^^ rim m j.val) := by
  simp [collar,line,Nat.add_assoc]

private theorem along_second {n m : ℕ} (t : Fin 3) (i : Fin n) (j : Fin m) :
    collar t (i,j) = (line m (coreCoord n i.val+t.val) j.val ^^ rim n i.val) := by
  unfold collar line
  change ((decide ((coreCoord n i.val + coreCoord m j.val + t.val)%3 ≠ 0) ^^
    rim n i.val) ^^ rim m j.val) = _
  rw [xor_swap]
  simp [Nat.add_assoc,Nat.add_comm]

theorem collar_two {n m : ℕ} (hn : 5≤n) (hm : 5≤m) (t : Fin 3) (v : Cell n m) :
    2 ≤ opp (collar t) v := by
  obtain ⟨i,j⟩:=v
  obtain ⟨k,hk,ck⟩ := line_neighbor hn (coreCoord m j.val+t.val) i
  obtain ⟨l,hl,cl⟩ := line_neighbor hm (coreCoord n i.val+t.val) j
  have hk' : collar t (k,j) ≠ collar t (i,j) := by
    intro eq
    rw [along_first,along_first] at eq
    exact ck (Bool.xor_left_inj.mp eq)
  have hl' : collar t (i,l) ≠ collar t (i,j) := by
    intro eq
    rw [along_second,along_second] at eq
    exact cl (Bool.xor_left_inj.mp eq)
  have sk : (k,j) ∈ neighbors (i,j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr ⟨rfl,hk.symm⟩⟩
  have sl : (i,l) ∈ neighbors (i,j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl ⟨rfl,hl.symm⟩⟩
  apply Finset.one_lt_card.mpr
  refine ⟨(k,j),Finset.mem_filter.mpr ⟨sk,hk'⟩,(i,l),Finset.mem_filter.mpr ⟨sl,hl'⟩,?_⟩
  intro same
  have eq : k.val=i.val := congrArg Fin.val (congrArg Prod.fst same)
  omega

theorem collar_happy_of_degree {n m : ℕ} (hn : 5≤n) (hm : 5≤m) (t : Fin 3)
    (degree : ∀ v : Cell n m, (neighbors v).card ≤ 4) :
    Happy (collar (n:=n) (m:=m) t) := by
  intro v
  have := collar_two hn hm t v
  have := degree v
  omega

end GridAnti.Hardin
end

section
namespace GridAnti.Hardin

/-- Each neighbor maps injectively to one of the four coordinate candidates. -/
theorem degree_le_four {n m : ℕ} (v : Cell n m) : (neighbors v).card ≤ 4 := by
  let point : Cell n m → ℕ × ℕ := fun q => (q.1.val,q.2.val)
  have inj : Function.Injective point := fun a b h =>
    Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
  let cross : Finset (ℕ × ℕ) :=
    {(v.1.val,v.2.val+1),(v.1.val,v.2.val-1),(v.1.val+1,v.2.val),(v.1.val-1,v.2.val)}
  have sub : (neighbors v).image point ⊆ cross := by
    intro z hz
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
    have step := (Finset.mem_filter.mp hq).2
    change Adj v q at step
    simp only [Adj,Fin.ext_iff] at step
    simp only [cross,point,Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq]
    rcases step with ⟨a,b|b⟩ | ⟨a,b|b⟩
    · exact Or.inl ⟨a.symm,b.symm⟩
    · exact Or.inr (Or.inl ⟨a.symm,by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨b.symm,a.symm⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by omega,a.symm⟩))
  exact (Finset.card_image_of_injective _ inj).symm.le.trans
    ((Finset.card_le_card sub).trans Finset.card_le_four)

theorem collar_happy {n m : ℕ} (hn : 5≤n) (hm : 5≤m) (t : Fin 3) :
    Happy (collar (n:=n) (m:=m) t) :=
  collar_happy_of_degree hn hm t degree_le_four

end GridAnti.Hardin
end

section
namespace GridAnti.Hardin

theorem neighbors_le_four {n m : ℕ} (v : Cell n m) : (neighbors v).card ≤ 4 :=
  degree_le_four v

private def step {n : ℕ} (i j : Fin n) : Prop :=
  i.val+1=j.val ∨ j.val+1=i.val

private theorem step_ne {n : ℕ} {i j : Fin n} (h : step i j) : j ≠ i := by
  intro eq
  subst j
  unfold step at h
  omega

private theorem has_step {n : ℕ} (hn : 2≤n) (i : Fin n) : ∃ j, step i j := by
  by_cases hi : i.val=0
  · exact ⟨⟨1,by omega⟩,Or.inl (by change i.val+1=1; omega)⟩
  · have := i.isLt
    exact ⟨⟨i.val-1,by omega⟩,Or.inr (by change i.val-1+1=i.val; omega)⟩

private theorem has_two_steps {n : ℕ} (i : Fin n) (inside : ¬(i.val=0 ∨ i.val+1=n)) :
    ∃ j k, step i j ∧ step i k ∧ j≠k := by
  have := i.isLt
  refine ⟨⟨i.val-1,by omega⟩,⟨i.val+1,by omega⟩,?_,Or.inl rfl,?_⟩
  · exact Or.inr (by change i.val-1+1=i.val; omega)
  · intro h
    have hv := congrArg Fin.val h
    change i.val-1=i.val+1 at hv
    omega

private theorem step_row {n m : ℕ} {i k : Fin n} (j : Fin m) (h : step i k) :
    (k,j) ∈ neighbors (i,j) :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr ⟨rfl,h⟩⟩

private theorem step_col {n m : ℕ} (i : Fin n) {j l : Fin m} (h : step j l) :
    (i,l) ∈ neighbors (i,j) :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl ⟨rfl,h⟩⟩

private theorem three_mem {α : Type*} [DecidableEq α] {s : Finset α} {a b c : α}
    (ha : a∈s) (hb : b∈s) (hc : c∈s) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    3≤s.card := by
  have sub : {a,b,c} ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl <;> assumption
  have h := Finset.card_le_card sub
  simpa [hab,hac,hbc] using h

theorem neighbor_lower {n m : ℕ} (hn : 2≤n) (hm : 2≤m) (v : Cell n m) :
    if ((v.1.val=0 ∨ v.1.val+1=n) ∧ (v.2.val=0 ∨ v.2.val+1=m))
    then 2 ≤ (neighbors v).card else 3 ≤ (neighbors v).card := by
  obtain ⟨i,j⟩ := v
  change if ((i.val=0 ∨ i.val+1=n) ∧ (j.val=0 ∨ j.val+1=m))
    then 2 ≤ (neighbors (i,j)).card else 3 ≤ (neighbors (i,j)).card
  obtain ⟨k,hk⟩ := has_step hn i
  obtain ⟨l,hl⟩ := has_step hm j
  split_ifs with corner
  · apply Finset.one_lt_card.mpr
    exact ⟨(k,j),step_row j hk,(i,l),step_col i hl,fun eq => step_ne hk (congrArg Prod.fst eq)⟩
  · by_cases ei : i.val=0 ∨ i.val+1=n
    · have ej : ¬ (j.val=0 ∨ j.val+1=m) := fun h => corner ⟨ei,h⟩
      obtain ⟨z,w,hz,hw,hzw⟩ := has_two_steps j ej
      apply three_mem (step_row j hk) (step_col i hz) (step_col i hw)
      · exact fun eq => step_ne hk (congrArg Prod.fst eq)
      · exact fun eq => step_ne hk (congrArg Prod.fst eq)
      · exact fun eq => hzw (congrArg Prod.snd eq)
    · obtain ⟨z,w,hz,hw,hzw⟩ := has_two_steps i ei
      apply three_mem (step_row j hz) (step_row j hw) (step_col i hl)
      · exact fun eq => hzw (congrArg Prod.fst eq)
      · exact fun eq => step_ne hz (congrArg Prod.fst eq)
      · exact fun eq => step_ne hw (congrArg Prod.fst eq)

end GridAnti.Hardin
end

section
namespace GridAnti.Hardin
open Finset

def atCorner {n m : ℕ} (v : Cell n m) : Prop :=
  (v.1.val=0 ∨ v.1.val+1=n) ∧ (v.2.val=0 ∨ v.2.val+1=m)

instance {n m : ℕ} (v : Cell n m) : Decidable (atCorner v) := by
  unfold atCorner
  infer_instance

private theorem corner_cap {n m : ℕ} (T : Finset (Cell n m)) :
    (T.filter atCorner).card ≤ 4 := by
  let p : Cell n m → ℕ × ℕ := fun q => (q.1.val,q.2.val)
  have inj : Function.Injective p := fun a b h =>
    Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
  let C : Finset (ℕ × ℕ) := {(0,0),(0,m-1),(n-1,0),(n-1,m-1)}
  have sub : (T.filter atCorner).image p ⊆ C := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
    obtain ⟨_,h⟩ := mem_filter.mp hv
    obtain ⟨a,b⟩ := h
    simp only [C, p, mem_insert, mem_singleton, Prod.mk.injEq]
    omega
  exact (card_image_of_injective _ inj).symm.le.trans ((card_le_card sub).trans card_le_four)

private theorem adj_comm {n m : ℕ} (v z : Cell n m) : Adj v z ↔ Adj z v := by
  unfold Adj
  grind

private theorem between {n m : ℕ} (T F : Finset (Cell n m)) :
    (∑ v ∈ T, (F.filter (Adj v)).card) = ∑ w ∈ F, (T.filter (Adj w)).card := by
  calc
    _ = ∑ v ∈ T, ∑ w ∈ F, (if Adj v w then 1 else 0 : ℕ) := by simp
    _ = ∑ w ∈ F, ∑ v ∈ T, (if Adj v w then 1 else 0 : ℕ) := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro w hw
      simp_rw [adj_comm _ w]
      simp

/-- Every happy colouring has at least two incidences at each one, with a possible
one-incidence exception at each of the rectangle's four corners. -/
theorem upper_from_degree {n m : ℕ} (c : Cell n m → Bool) (happy : Happy c)
    (localDeg : ∀ v : Cell n m, if atCorner v then 2≤(neighbors v).card
       else 3≤(neighbors v).card) : 3*ones c ≤ 2*n*m+2 := by
  classical
  let T := univ.filter (fun v => c v = true)
  let F := univ.filter (fun v => c v ≠ true)
  have part : T.card + F.card = n*m := by
    simpa [T,F] using (card_filter_add_card_filter_not (fun v => c v=true) (s:=univ))
  have lower (v : Cell n m) : 2 ≤ opp c v + (if atCorner v then 1 else 0 : ℕ) := by
    have hd := localDeg v
    have hh := happy v
    by_cases h : atCorner v <;> simp [h] at hd ⊢ <;> omega
  have lo := sum_le_sum (s:=T) (f:=fun _ => 2) (g:=fun v => opp c v + (if atCorner v then 1 else 0))
    (fun v _ => lower v)
  simp only [sum_const,nsmul_eq_mul,sum_add_distrib,sum_boole] at lo
  have bnd := corner_cap T
  have exactly : (∑ v ∈ T, opp c v) = ∑ w ∈ F, (T.filter (Adj w)).card := by
    rw [← between T F]
    apply sum_congr rfl
    intro v hv
    have hv' := (mem_filter.mp hv).2
    apply congrArg Finset.card
    ext w
    simp [neighbors,F,hv',and_comm]
  have hi := sum_le_sum (s:=F) (f:=fun w => (T.filter (Adj w)).card) (g:=fun _ => 4)
    (fun w _ => (card_le_card (show T.filter (Adj w) ⊆ neighbors w from
      fun _ h => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩)).trans (degree_le_four w))
  simp only [sum_const,nsmul_eq_mul] at hi
  simp only [Nat.cast_id] at lo hi
  change T.card*2 ≤ (∑ v ∈ T,opp c v) + (T.filter atCorner).card at lo
  change 3*T.card ≤ 2*n*m+2
  rw [Nat.mul_assoc 2 n m]
  omega

theorem best_upper_from_degree {n m : ℕ}
    (h : ∀ v : Cell n m, if atCorner v then 2≤(neighbors v).card else 3≤(neighbors v).card) :
    3*best n m ≤ 2*n*m+2 := by
  classical
  have bound : best n m ≤ (2*n*m+2)/3 := by
    apply Finset.sup_le
    intro c hc
    have w := upper_from_degree c (mem_filter.mp hc).2 h
    omega
  omega

/-- An additive rectangle bound from opposite-colour incidences. -/
theorem best_upper {n m : ℕ} (hn : 2≤n) (hm : 2≤m) :
    3*best n m ≤ 2*n*m+2 :=
  best_upper_from_degree (fun v => neighbor_lower hn hm v)

end GridAnti.Hardin
end

section
namespace GridAnti.Hardin
open Finset

def ballot {n m : ℕ} (t : Fin 3) (v : GridAnti.Cell n m) : ℕ :=
  if collar t v then 1 else 0

theorem ballot_total {n m : ℕ} (t : Fin 3) :
    ∑ v : GridAnti.Cell n m, ballot t v = ones (collar (n:=n) (m:=m) t) := by
  classical
  simp [ballot, ones]

end GridAnti.Hardin
end

section
namespace GridAnti.Hardin
open Finset

private theorem rim_total {n : ℕ} (hn : 2 ≤ n) :
    (∑ x : Fin n, (rim n x.val).toNat) = 2 := by
  let first : Fin n := ⟨0, by omega⟩
  let last : Fin n := ⟨n-1, by omega⟩
  have eq (x : Fin n) : (rim n x.val).toNat =
      (if x=first then 1 else 0) + (if x=last then 1 else 0) := by
    simp only [first,last,Fin.ext_iff,rim]
    by_cases hx : x.val=0
    · simp [hx,show 0 ≠ n-1 by omega]
    · by_cases hy : x.val+1=n
      · simp [show x.val=n-1 by omega,show n-1 ≠ 0 by omega,show n-1+1=n by omega]
      · simp [hx,hy,show x.val ≠ n-1 by omega]
  simp_rw [eq]
  simp [sum_add_distrib]

private theorem ballot_rims {n m : ℕ} (v : Cell n m) :
    ballot 0 v + ballot 1 v + ballot 2 v + (rim n v.1.val).toNat + (rim m v.2.val).toNat =
      2 + 2*(rim n v.1.val).toNat*(rim m v.2.val).toNat := by
  cases hr : rim n v.1.val <;> cases hc : rim m v.2.val <;>
    simp only [ballot,collar,hr,hc,Bool.xor_false,Bool.xor_true] <;>
    norm_num <;> split_ifs <;> omega

/-- Exact sum over the three collar phases, including every edge and corner. -/
theorem collar_ballots {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    ones (collar (n:=n) (m:=m) 0) + ones (collar (n:=n) (m:=m) 1) +
      ones (collar (n:=n) (m:=m) 2) + 2*n + 2*m = 2*n*m + 8 := by
  have H := Finset.sum_congr (s₁ := (univ : Finset (Cell n m))) rfl (fun v _ => ballot_rims v)
  have row : (∑ v : Cell n m, (rim n v.1.val).toNat) = m*2 := by
    rw [Fintype.sum_prod_type]
    simp [← Finset.mul_sum, rim_total hn]
  have col : (∑ v : Cell n m, (rim m v.2.val).toNat) = n*2 := by
    rw [Fintype.sum_prod_type]
    simp [rim_total hm]
  have corner : (∑ v : Cell n m, 2*(rim n v.1.val).toNat*(rim m v.2.val).toNat) = 8 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, rim_total hm, ← Finset.sum_mul, rim_total hn]
    rfl
  simp only [sum_add_distrib,ballot_total,row,col,corner,sum_const, card_univ, Cell, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at H
  simpa only [Nat.mul_comm, Nat.mul_left_comm,Nat.mul_assoc,Nat.add_comm,Nat.add_left_comm,
    Nat.add_assoc] using H

theorem sharp_phase_lower {n m : ℕ} (hn : 5 ≤ n) (hm : 5 ≤ m) :
    2*n*m+8 ≤ 3*best n m + 2*n+2*m := by
  classical
  have opt (t : Fin 3) : ones (collar (n:=n) (m:=m) t) ≤ best n m := by
    apply Finset.le_sup (f:=ones)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,collar_happy hn hm t⟩
  have H := collar_ballots (show 2 ≤ n by omega) (show 2 ≤ m by omega)
  have h0 := opt 0
  have h1 := opt 1
  have h2 := opt 2
  omega

end GridAnti.Hardin
end

section
namespace GridAnti.Hardin

/-- Boundary errors proportional to the perimeter vanish as both side lengths tend to infinity. -/
theorem density_of_finite_bounds
    (lower : ∀ n m : ℕ, 5 ≤ n → 5 ≤ m → 2*n*m+8 ≤ 3*best n m+2*n+2*m)
    (upper : ∀ n m : ℕ, 5 ≤ n → 5 ≤ m → 3*best n m ≤ 2*n*m+2) :
    type_of% @OMA.S_oeis_a179004.main := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (8 / ε)
  refine ⟨max 5 k, by omega, ?_⟩
  intro n m hn hm
  have hn5 : 5 ≤ n := (le_max_left 5 k).trans hn
  have hm5 : 5 ≤ m := (le_max_left 5 k).trans hm
  have hkn : k ≤ n := (le_max_right 5 k).trans hn
  have hkm : k ≤ m := (le_max_right 5 k).trans hm
  have en : (8 : ℝ) < (n : ℝ)*ε := (div_lt_iff₀ hε).mp (hk.trans_le (Nat.cast_le.mpr hkn))
  have em : (8 : ℝ) < (m : ℝ)*ε := (div_lt_iff₀ hε).mp (hk.trans_le (Nat.cast_le.mpr hkm))
  have nr : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have mr : 0 < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have budget : 4*((n:ℝ)+m) < ε*((n:ℝ)*m) := by
    nlinarith only [mul_lt_mul_of_pos_right en mr, mul_lt_mul_of_pos_right em nr]
  have ub : 3*(best n m : ℝ) ≤ 2*(n:ℝ)*m+2 := by exact_mod_cast upper n m hn5 hm5
  have lc : 2*(n:ℝ)*m+8 ≤ 3*(best n m : ℝ)+2*n+2*m := by
    exact_mod_cast lower n m hn5 hm5
  have n5r : (5:ℝ) ≤ n := by exact_mod_cast hn5
  have m5r : (5:ℝ) ≤ m := by exact_mod_cast hm5
  have area : 0 < (n:ℝ)*m := mul_pos nr mr
  apply abs_lt.mpr
  constructor
  · apply (lt_sub_iff_add_lt).mpr
    apply (lt_div_iff₀ area).mpr
    nlinarith only [lc, budget, mul_pos hε area,n5r,m5r]
  · apply (sub_lt_iff_lt_add).mpr
    apply (div_lt_iff₀ area).mpr
    nlinarith only [ub, budget, mul_pos hε area,n5r,m5r]

end GridAnti.Hardin
end

theorem OMA.solution : type_of% @OMA.S_oeis_a179004.main :=
  GridAnti.Hardin.density_of_finite_bounds
    (fun _ _ hn hm => GridAnti.Hardin.sharp_phase_lower hn hm)
    (fun _ _ hn hm => GridAnti.Hardin.best_upper (by omega) (by omega))
