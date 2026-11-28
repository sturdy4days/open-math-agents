import OMAStatements.S_oeis_a245954
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.List.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Nat.Factorial.Basic

/-! # Four-entry sliding windows at every word length

Over the alphabet 0,...,n, require a pair summing to n in every consecutive
four entries. At fixed word length k the count is a polynomial of degree at
most k in the number of complementary letter pairs, with coefficients depending
on whether a middle letter is present. At k=7 this is exactly OEIS A245954.
-/

namespace WindowFour

abbrev Letter := Option (ℕ × Bool)

def comp : Letter → Letter → Bool
  | none,none => true
  | some (i,b),some (j,c) => i==j && b != c
  | _,_ => false

def palette (m : ℕ) (mid : Bool) : Finset Letter :=
  ((Finset.range m ×ˢ (Finset.univ : Finset Bool)).image some) ∪
    (if mid then {none} else ∅)

@[simp] theorem mem_palette_none (m : ℕ) (mid : Bool) : none ∈ palette m mid ↔ mid = true := by
  cases mid <;> simp [palette]
@[simp] theorem mem_palette_some (m : ℕ) (mid : Bool) (i : ℕ) (b : Bool) :
    some (i,b) ∈ palette m mid ↔ i < m := by
  cases mid <;> simp [palette]

/-- The list stores positions from newest to oldest. -/
def allowed : List Letter → Bool
  | a::b::c::d::_ => comp a b || comp a c || comp a d || comp b c || comp b d || comp c d
  | _ => true

def assignments (m : ℕ) (mid : Bool) : ℕ → List Letter → ℕ
  | 0,_ => 1
  | f+1,w => ∑ x ∈ palette m mid, if allowed (x::w) then assignments m mid f (x::w) else 0

end WindowFour

namespace WindowFour

private def encode (n x : ℕ) : Letter :=
  if 2*x<n then some (x,false) else if n<2*x then some (n-x,true) else none

private theorem encode_mem (n : ℕ) (x : Fin (n+1)) :
    encode n x.val ∈ palette ((n+1)/2) (n%2==0) := by
  have hx := x.isLt
  unfold encode
  split
  · rw [mem_palette_some]
    omega
  · split
    · rw [mem_palette_some]
      omega
    · rw [mem_palette_none, beq_iff_eq]
      omega

private def decodeLetter (n : ℕ) : Letter → ℕ
  | none => n/2
  | some (i,false) => i
  | some (i,true) => n-i

private theorem decode_lt (n : ℕ) (v : Letter) (h : v ∈ palette ((n+1)/2) (n%2==0)) :
    decodeLetter n v < n+1 := by
  rcases v with _ | ⟨i,b⟩
  · dsimp [decodeLetter]; omega
  · rw [mem_palette_some] at h
    cases b <;> dsimp [decodeLetter] <;> omega

private theorem decode_encode (n : ℕ) (x : Fin (n+1)) :
    decodeLetter n (encode n x.val) = x.val := by
  have hx := x.isLt
  unfold encode
  split
  · rfl
  · split <;> dsimp [decodeLetter] <;> omega

private theorem encode_decode (n : ℕ) (v : Letter) (h : v ∈ palette ((n+1)/2) (n%2==0)) :
    encode n (decodeLetter n v) = v := by
  rcases v with _ | ⟨i,b⟩
  · rw [mem_palette_none, beq_iff_eq] at h
    simp [decodeLetter,encode,show ¬2*(n/2)<n by omega,show ¬n<2*(n/2) by omega]
  · rw [mem_palette_some] at h
    cases b
    · simp [decodeLetter,encode,show 2*i<n by omega]
    · simp [decodeLetter,encode,show ¬2*(n-i)<n by omega,show n<2*(n-i) by omega,
        show n-(n-i)=i by omega]

/-- Identify the low and high elements of each complementary pair, keeping a separate midpoint. -/
def colorChart (n : ℕ) :
    Fin (n+1) ≃ {v : Letter // v ∈ palette ((n+1)/2) (n%2==0)} where
  toFun x := ⟨encode n x.val,encode_mem n x⟩
  invFun v := ⟨decodeLetter n v.val,decode_lt n v.val v.property⟩
  left_inv x := Fin.ext (decode_encode n x)
  right_inv v := Subtype.ext (encode_decode n v.val v.property)

/-- The signed labels recognize exactly the same sums as the original natural-number alphabet. -/
theorem colorChart_sum (n : ℕ) (x y : Fin (n+1)) :
    (x.val+y.val=n) ↔ comp (colorChart n x).val (colorChart n y).val=true := by
  have hx := x.isLt
  have hy := y.isLt
  change _ ↔ comp (encode n x.val) (encode n y.val) = true
  unfold encode
  split <;> split <;> (try split) <;> (try split) <;> simp [comp] <;> omega

end WindowFour

namespace WindowFour
open Finset

def validWord (n : ℕ) : (k : ℕ) → List Letter → (Fin k → Fin (n+1)) → Bool
  | 0,_,_ => true
  | k+1,w,x =>
    let next := (colorChart n (x 0)).val :: w
    allowed next && validWord n k next (Fin.tail x)

/-- Evaluation over each word gives the same count as recursively extending the history. -/
theorem count_eval (n k : ℕ) (w : List Letter) :
    (∑ x : Fin k → Fin (n+1), if validWord n k w x then 1 else 0) =
      assignments ((n+1)/2) (n%2==0) k w := by
  classical
  induction k generalizing w with
  | zero => simp [validWord,assignments]
  | succ k ih =>
    let A := Fin (n+1)
    let m := (n+1)/2
    let mid := n%2==0
    let term (v : Letter) := if allowed (v::w) then assignments m mid k (v::w) else 0
    change _ = ∑ v ∈ palette m mid, term v
    let e := Fin.consEquiv (fun _ : Fin (k+1) => A)
    rw [← e.sum_comp, Fintype.sum_prod_type]
    calc
      _ = ∑ a : Fin (n+1), term (colorChart n a).val := by
        apply sum_congr rfl
        intro a _
        change (∑ t : Fin k → Fin (n+1), if validWord n (k+1) w (Fin.cons a t) then 1 else 0) = _
        simp only [validWord,Fin.cons_zero,Fin.tail_cons]
        by_cases h : allowed ((colorChart n a).val::w) = true
        · simpa [term,h,m,mid] using ih ((colorChart n a).val::w)
        · simp [term,h]
      _ = ∑ v : {v // v ∈ palette m mid}, term v.val :=
        (colorChart n).sum_comp (fun v => term v.val)
      _ = ∑ v ∈ palette m mid, term v := by
        exact Finset.sum_coe_sort .. 

end WindowFour

namespace WindowFour
open OMA.S_oeis_a245954 Finset

private theorem four_forall (P : ℕ → Prop) :
    (∀ i < 4, P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
  constructor
  · intro h
    exact ⟨h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide)⟩
  · rintro ⟨a,b,c,d⟩ i hi
    interval_cases i <;> assumption

private theorem four_exists (P : ℕ → Prop) :
    (∃ i < 4, P i) ↔ P 0 ∨ P 1 ∨ P 2 ∨ P 3 := by
  constructor
  · rintro ⟨i,hi,h⟩
    interval_cases i <;> tauto
  · rintro (h|h|h|h)
    · exact ⟨0,by decide,h⟩
    · exact ⟨1,by decide,h⟩
    · exact ⟨2,by decide,h⟩
    · exact ⟨3,by decide,h⟩

private def hit (n : ℕ) (a b c d : ℕ) : Prop :=
  a+b=n ∨ a+c=n ∨ a+d=n ∨ b+c=n ∨ b+d=n ∨ c+d=n

private theorem four_window (n : ℕ) (x : Fin 7 → Fin (n+1)) (t : ℕ) :
    (∃ i < 4, ∃ j < 4, i < j ∧ get x (t+i) + get x (t+j) = n) ↔
      hit n (get x t) (get x (t+1)) (get x (t+2)) (get x (t+3)) := by
  simp only [four_exists,hit]
  norm_num [or_assoc]

private theorem allowed_hit (n : ℕ) (a b c d : Fin (n+1)) (w : List Letter) :
    allowed ((colorChart n d).val::(colorChart n c).val::(colorChart n b).val::
      (colorChart n a).val::w)=true ↔ hit n a.val b.val c.val d.val := by
  simp only [allowed,Bool.or_eq_true,←colorChart_sum,hit]
  simp only [Nat.add_comm d.val, Nat.add_comm c.val a.val, Nat.add_comm c.val b.val,
    Nat.add_comm b.val a.val, or_comm, or_left_comm]

theorem original_eval (n : ℕ) (x : Fin 7 → Fin (n+1)) :
    good x = true ↔ validWord n 7 [] x = true := by
  simp only [good,decide_eq_true_eq,four_window,four_forall,validWord,Fin.tail,Bool.and_eq_true,
    allowed_hit]
  change (hit n (x 0) (x 1) (x 2) (x 3) ∧ hit n (x 1) (x 2) (x 3) (x 4) ∧
    hit n (x 2) (x 3) (x 4) (x 5) ∧ hit n (x 3) (x 4) (x 5) (x 6)) ↔ _
  simp [allowed]

theorem original_count (n : ℕ) :
    a n = (assignments ((n+1)/2) (n%2==0) 7 [] : ℤ) := by
  classical
  unfold a
  congr 1
  rw [card_filter,←count_eval]
  apply sum_congr rfl
  intro x _
  simp only [original_eval n x]

end WindowFour

namespace WindowFour

/-- Symbols already in use, including the optional midpoint, and the two
possible orientations of the first occurrence of the next pair. -/
def branches (mid : Bool) (u : ℕ) : List Letter :=
  (if mid then [none] else []) ++ (List.range (u+1)).flatMap (fun i =>
    [some (i,false), some (i,true)])

def advance (u : ℕ) : Letter → ℕ
  | none => u
  | some (i,_) => if i = u then u+1 else u

/-- Canonical words grow by reusing a label or introducing its successor.
The leaf weight is a function of the total number of labels used. -/
def tree (mid : Bool) (weight : ℕ → ℕ) : ℕ → ℕ → List Letter → ℕ
  | 0,u,_ => weight u
  | f+1,u,w => ((branches mid u).map fun x =>
      if allowed (x::w) then tree mid weight f (advance u x) (x::w) else 0).sum

end WindowFour

namespace WindowFour
open Finset

private theorem pairSum (u : ℕ) (g : Letter → ℕ) :
    (((List.range u).flatMap fun i => [some (i,false),some (i,true)]).map g).sum =
      ∑ i ∈ range u, (g (some (i,false)) + g (some (i,true))) := by
  induction u with
  | zero => simp
  | succ u ih => simp [List.range_succ,List.flatMap_append,ih,sum_range_succ]

theorem branchSum (mid : Bool) (u : ℕ) (g : Letter → ℕ) :
    ((branches mid u).map g).sum =
      (if mid then g none else 0) +
        (∑ i ∈ range u, (g (some (i,false)) + g (some (i,true)))) +
        (g (some (u,false)) + g (some (u,true))) := by
  cases mid <;> simp [branches,pairSum,sum_range_succ,add_assoc]

theorem paletteSum (mid : Bool) (m : ℕ) (g : Letter → ℕ) :
    (∑ x ∈ palette m mid, g x) =
      (if mid then g none else 0) +
        ∑ i ∈ range m, (g (some (i,false)) + g (some (i,true))) := by
  have pair : (∑ x ∈ ((range m ×ˢ (univ : Finset Bool)).image some), g x) =
      ∑ i ∈ range m, (g (some (i,false)) + g (some (i,true))) := by
    rw [sum_image (fun _ _ _ _ h => Option.some.inj h),sum_product]
    simp [add_comm]
  cases mid <;> simp only [palette,Bool.false_eq_true,if_false,if_true,union_empty,zero_add]
  · exact pair
  · rw [sum_union (by simp),pair,sum_singleton,add_comm]

def relabel (p : ℕ → ℕ) : Letter → Letter
  | none => none
  | some (i,b) => some (p i,b)

def bounded (u : ℕ) : Letter → Prop
  | none => True
  | some (i,_) => i < u

theorem allowed_relabel (u : ℕ) (p : ℕ → ℕ) (inj : Set.InjOn p (Set.Iio u))
    (w : List Letter) (bd : ∀ x ∈ w, bounded u x) :
    allowed (w.map (relabel p)) = allowed w := by
  have compat (x y) (hx : bounded u x) (hy : bounded u y) :
      comp (relabel p x) (relabel p y) = comp x y := by
    rcases x with _|⟨i,b⟩ <;> rcases y with _|⟨j,c⟩ <;> try rfl
    have h : p i = p j ↔ i=j := ⟨fun e => inj hx hy e,fun e => congrArg p e⟩
    have bh : (p i == p j) = (i == j) := by
      rw [Bool.eq_iff_iff]
      simpa using h
    simp only [relabel,comp,bh]
  rcases w with _|⟨a,_|⟨b,_|⟨c,_|⟨d,w⟩⟩⟩⟩ <;> try rfl
  simp only [List.map_cons,allowed]
  have ha := bd a (by simp)
  have hb := bd b (by simp)
  have hc := bd c (by simp)
  have hd := bd d (by simp)
  rw [compat a b ha hb,compat a c ha hc,compat a d ha hd,compat b c hb hc,
    compat b d hb hd,compat c d hc hd]

/-- A canonical first occurrence can use any of the unused actual labels. -/
def orbit (m : ℕ) (mid : Bool) : ℕ → ℕ → List Letter → ℕ
  | 0,_,_ => 1
  | k+1,u,w =>
    let step (x : Letter) (v : ℕ) := if allowed (x::w) then orbit m mid k v (x::w) else 0
    (if mid then step none u else 0) +
    (∑ i ∈ range u, (step (some (i,false)) u + step (some (i,true)) u)) +
    (m-u) * (step (some (u,false)) (u+1) + step (some (u,true)) (u+1))

theorem groupFresh (m u : ℕ) (p : ℕ → ℕ) (inj : Set.InjOn p (Set.Iio u))
    (fits : ∀ i < u, p i < m) (g : ℕ → ℕ) (fresh : ℕ)
    (constant : ∀ i < m, (∀ j < u, p j ≠ i) → g i = fresh) :
    (∑ i ∈ range m, g i) = (∑ j ∈ range u, g (p j)) + (m-u)*fresh := by
  let S := (range u).image p
  have subset : S ⊆ range m := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
    exact mem_range.mpr (fits j (mem_range.mp hj))
  have inj' : Set.InjOn p ((range u : Finset ℕ) : Set ℕ) := by simpa using inj
  have sz : S.card = u := by simp [S,card_image_of_injOn inj']
  have remain : (∑ i ∈ range m \ S, g i) = (m-u)*fresh := by
    rw [sum_congr rfl (g:=fun _ => fresh)]
    · simp [card_sdiff_of_subset subset,sz]
    · intro i hi
      obtain ⟨inside,out⟩ := mem_sdiff.mp hi
      apply constant _ (mem_range.mp inside)
      intro j hj eq
      exact out (mem_image.mpr ⟨j,mem_range.mpr hj,eq⟩)
  have split := sum_sdiff subset (f:=g)
  calc
    _ = (∑ i ∈ S, g i) + ∑ i ∈ range m \ S, g i := by omega
    _ = _ := by rw [remain]; congr 1; exact sum_image inj'

end WindowFour

namespace WindowFour
open Finset

/-- The multiplicity of a fresh label is the number of unused complementary pairs.
All extensions respect the comparison of letters in the four-position window. -/
theorem assignments_eq_orbit {m : ℕ} (mid : Bool) (k u : ℕ) (w : List Letter) (p : ℕ → ℕ)
    (inj : Set.InjOn p (Set.Iio u)) (fits : ∀ i < u, p i < m)
    (wd : ∀ x ∈ w, bounded u x) :
    assignments m mid k (w.map (relabel p)) = orbit m mid k u w := by
  induction k generalizing u w p with
  | zero => rfl
  | succ k ih =>
    let G (x : Letter) := if allowed (x :: w.map (relabel p)) then
      assignments m mid k (x :: w.map (relabel p)) else 0
    let O (v : ℕ) (x : Letter) := if allowed (x::w) then orbit m mid k v (x::w) else 0
    have applyStep (v : ℕ) (q : ℕ → ℕ) (x : Letter) (hx : bounded v x)
        (hq : Set.InjOn q (Set.Iio v)) (fitq : ∀ i<v, q i < m)
        (boundq : ∀ y∈w, bounded v y) (eqw : w.map (relabel q) = w.map (relabel p)) :
        G (relabel q x) = O v x := by
      have bd (y) (hy : y∈x::w) : bounded v y := by
        obtain rfl|inw := List.mem_cons.mp hy
        · exact hx
        · exact boundq _ inw
      have check := allowed_relabel v q hq (x::w) bd
      have result := ih v (x::w) q hq fitq bd
      simp only [List.map_cons,eqw] at check result
      simp only [G,O,check,result]
    have same (x : Letter) (hx : bounded u x) : G (relabel p x) = O u x :=
      applyStep u p x hx inj fits wd rfl
    have fresh (a : ℕ) (ha : a < m) (free : ∀ j < u, p j ≠ a) (bit : Bool) :
        G (some (a,bit)) = O (u+1) (some (u,bit)) := by
      let q := fun i => if i=u then a else p i
      have newInj : Set.InjOn q (Set.Iio (u+1)) := by
        intro x hx y hy eq
        change x < u+1 at hx
        change y < u+1 at hy
        by_cases ex : x=u <;> by_cases ey : y=u
        · omega
        · simp [q,ex,ey] at eq
          exact (free y (by omega) eq.symm).elim
        · simp [q,ex,ey] at eq
          exact (free x (by omega) eq).elim
        · simp [q,ex,ey] at eq
          exact inj (by change x < u; omega) (by change y < u; omega) eq
      have extend (x : ℕ) (hx : x < u+1) : q x < m := by
        by_cases eq : x=u
        · simpa [q,eq] using ha
        · simpa [q,eq] using fits x (by omega)
      have wb (y) (hy : y∈w) : bounded (u+1) y := by
        have h := wd y hy
        rcases y with _|⟨i,b⟩
        · trivial
        · exact Nat.lt_succ_of_lt h
      have eqw : w.map (relabel q) = w.map (relabel p) := by
        apply List.map_congr_left
        intro y hy
        have h := wd y hy
        rcases y with _|⟨i,b⟩
        · rfl
        · change i < u at h
          simp [relabel,q,h.ne]
      have h := applyStep (u+1) q (some (u,bit)) (Nat.lt_succ_self _) newInj extend wb eqw
      simpa only [relabel,q,if_true] using h
    let g := fun i => G (some (i,false)) + G (some (i,true))
    have sum := groupFresh m u p inj fits g (O (u+1) (some (u,false)) + O (u+1) (some (u,true)))
      (fun a ha free => by simp only [g,fresh a ha free])
    change (∑ x ∈ palette m mid, G x) = _
    rw [paletteSum,sum,← Nat.add_assoc]
    change (if mid then G none else 0) + (∑ i ∈ range u, g (p i)) + _ =
      (if mid then O u none else 0) + (∑ i ∈ range u, (O u (some (i,false)) + O u (some (i,true)))) + _
    have c0 : G none = O u none := same none trivial
    rw [c0]
    congr 2
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg₂ (·+·) (same (some (i,false)) (mem_range.mp hi)) (same (some (i,true)) (mem_range.mp hi))

theorem root_orbit (m : ℕ) (mid : Bool) (k : ℕ) :
    assignments m mid k [] = orbit m mid k 0 [] :=
  assignments_eq_orbit mid k 0 [] id (Set.injOn_id _) (by simp) (by simp)

end WindowFour

namespace WindowFour
open Finset

private def leaves (mid : Bool) : ℕ → ℕ → List Letter → List ℕ
  | 0,u,_ => [u]
  | k+1,u,w => (branches mid u).flatMap fun x =>
      if allowed (x::w) then leaves mid k (advance u x) (x::w) else []

private theorem advance_bounds (x : Letter) (u : ℕ) : u≤advance u x ∧ advance u x≤u+1 := by
  rcases x with _|⟨i,b⟩
  · simp [advance]
  · by_cases e : i=u <;> simp [advance,e]

private theorem leaf_bounds (mid : Bool) (k u : ℕ) (w : List Letter) :
    ∀ j ∈ leaves mid k u w, u ≤ j ∧ j ≤ u+k := by
  induction k generalizing u w with
  | zero => simp [leaves]
  | succ k ih =>
    intro j hj
    obtain ⟨x,_,hit⟩ := List.mem_flatMap.mp hj
    by_cases e : allowed (x::w)
    · simp only [e,if_true] at hit
      have := ih (advance u x) (x::w) j hit
      have := advance_bounds x u
      omega
    · simp [e] at hit

private theorem flat_sum {α β : Type} (xs : List α) (F : α → List β) (g : β → ℕ) :
    ((xs.flatMap F).map g).sum = (xs.map fun x => ((F x).map g).sum).sum := by
  induction xs <;> simp [*]

private theorem tree_leaves (mid : Bool) (g : ℕ → ℕ) (k u : ℕ) (w : List Letter) :
    tree mid g k u w = ((leaves mid k u w).map g).sum := by
  induction k generalizing u w with
  | zero => simp [tree,leaves]
  | succ k ih =>
    simp only [tree,leaves,flat_sum]
    congr 1
    apply List.map_congr_left
    intro x _
    by_cases e : allowed (x::w) <;> simp [e,ih]

private theorem mul_val (mid : Bool) (g : ℕ → ℕ) (a k u : ℕ) (w : List Letter) :
    a * tree mid g k u w = tree mid (fun j => a * g j) k u w := by
  simp only [tree_leaves]
  induction leaves mid k u w with
  | nil => simp
  | cons j l ih => simp [Nat.mul_add,ih]

private theorem congr_val (mid : Bool) (g h : ℕ → ℕ) (k u : ℕ) (w : List Letter)
    (eq : ∀ j ≥ u, g j = h j) : tree mid g k u w = tree mid h k u w := by
  rw [tree_leaves,tree_leaves]
  congr 1
  exact List.map_congr_left (fun j hj => eq j (leaf_bounds mid k u w j hj).1)

private theorem weight_fresh (m u k : ℕ) (mid : Bool) (w : List Letter) :
    (m-u) * tree mid (fun j => (m-(u+1)).descFactorial (j-(u+1))) k (u+1) w =
    tree mid (fun j => (m-u).descFactorial (j-u)) k (u+1) w := by
  rw [mul_val]
  apply congr_val
  intro j le
  rw [show j-u = (j-(u+1))+1 by omega]
  by_cases h : u < m
  · obtain ⟨a,ha⟩ := Nat.exists_eq_succ_of_ne_zero (show m-u≠0 by omega)
    rw [ha,show m-(u+1)=a by omega,Nat.succ_descFactorial_succ]
  · rw [show m-u=0 by omega,Nat.zero_descFactorial_succ]
    simp

private theorem orbit_tree (m : ℕ) (mid : Bool) (k u : ℕ) (w : List Letter) :
    orbit m mid k u w = tree mid (fun j => (m-u).descFactorial (j-u)) k u w := by
  induction k generalizing u w with
  | zero => simp [orbit,tree]
  | succ k ih =>
    rw [orbit,tree,branchSum]
    simp only [ih]
    have old (i : ℕ) (hi : i∈range u) (b : Bool) : advance u (some (i,b))=u := by
      simp [advance,(mem_range.mp hi).ne]
    simp only [advance,if_true]
    -- All occurrences of earlier labels have their original weight.
    congr 1
    · congr 1
      apply sum_congr rfl
      intro i hi
      simp [(mem_range.mp hi).ne]
    · rw [Nat.mul_add]
      congr 1 <;> split_ifs <;> simp_all only [Nat.mul_zero,weight_fresh]

private theorem sum_weight {ι : Type} (S : Finset ι) (g : ι → ℕ → ℕ) (xs : List ℕ) :
    (xs.map fun j => ∑ i ∈ S, g i j).sum = ∑ i ∈ S, (xs.map (g i)).sum := by
  induction xs with
  | nil => simp
  | cons j l ih => simp [ih,sum_add_distrib]

theorem histogram_all_lengths (k m : ℕ) (mid : Bool) :
    assignments m mid k [] =
      ∑ j : Fin (k+1), m.descFactorial j.val * tree mid (fun i => if i=j.val then 1 else 0) k 0 [] := by
  rw [root_orbit,orbit_tree]; simp only [Nat.sub_zero]
  trans tree mid (fun j => ∑ d : Fin (k+1), m.descFactorial d.val * (if j=d.val then 1 else 0)) k 0 []
  · rw [tree_leaves,tree_leaves]
    congr 1
    apply List.map_congr_left
    intro j mem
    have h := (leaf_bounds mid k 0 [] j mem).2
    let x : Fin (k+1) := ⟨j,by omega⟩
    have eq (d : Fin (k+1)) : j=d.val ↔ x=d := ⟨fun e => Fin.ext e,fun e => congrArg Fin.val e⟩
    simp only [eq,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true,x]
  · rw [tree_leaves,sum_weight]
    apply sum_congr rfl
    intro i _
    rw [mul_val,tree_leaves]

/-- A single polynomial for each midpoint choice counts all words of the given length. -/
noncomputable def windowPolynomial (k : ℕ) (mid : Bool) : Polynomial ℚ :=
  ∑ j : Fin (k+1), descPochhammer ℚ j.val *
    Polynomial.C ((tree mid (fun i => if i=j.val then 1 else 0) k 0 [] : ℕ) : ℚ)

theorem eval_windowPolynomial (k m : ℕ) (mid : Bool) :
    (windowPolynomial k mid).eval (m:ℚ) = (assignments m mid k []:ℚ) := by
  rw [histogram_all_lengths k m mid]
  simp [windowPolynomial,Polynomial.eval_finsetSum,descPochhammer_eval_eq_descFactorial]

/-- The polynomial degree is at most the word length. -/
theorem degree_bound (k : ℕ) (mid : Bool) : (windowPolynomial k mid).natDegree ≤ k := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  apply (Polynomial.natDegree_mul_le ..).trans
  simpa [descPochhammer_natDegree] using (show j.val≤k by omega)

/-- Count words of length k whose every length-four consecutive window has a complementary pair. -/
theorem sliding_four_all_lengths (n k : ℕ) :
    ((∑ x : Fin k → Fin (n+1), if validWord n k [] x then 1 else 0 : ℕ):ℚ) =
      (windowPolynomial k (n%2==0)).eval (((n+1)/2 : ℕ):ℚ) := by
  rw [count_eval,eval_windowPolynomial]

end WindowFour

namespace WindowFour
/-- Exact polynomial description for the registered length-seven sequence. -/
theorem original_polynomial (n : ℕ) :
    (OMA.S_oeis_a245954.a n : ℚ) =
      (windowPolynomial 7 (n%2==0)).eval (((n+1)/2 : ℕ):ℚ) := by
  rw [original_count, eval_windowPolynomial]
  norm_cast
end WindowFour
