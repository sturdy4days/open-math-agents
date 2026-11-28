import OMAStatements.S_oeis_a245954
import Mathlib.Tactic

/-!
# Complementary pairs in every four-position window

This proves Colin Barker's formulas for OEIS A245954, as formalized by
@clementtrecourt. Retain the most recent three letters while extending a word.
Label complementary pairs by order of first occurrence. A normalized pattern
using j distinct noncentral pairs has (m)_j realizations, where m is the
number of available pairs. A finite calculation on these patterns supplies
the parity polynomials; coefficient comparison gives the generating series.
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
        (hq : Set.InjOn q (Set.Iio v)) (fitq : ∀ i < v, q i < m)
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

theorem root_from_histogram (m : ℕ) (mid : Bool) :
    assignments m mid 7 [] =
      ∑ j : Fin 8, m.descFactorial j.val * tree mid (fun i => if i=j.val then 1 else 0) 7 0 [] := by
  rw [root_orbit,orbit_tree]; simp only [Nat.sub_zero]
  trans tree mid (fun j => ∑ d : Fin 8, m.descFactorial d.val * (if j=d.val then 1 else 0)) 7 0 []
  · rw [tree_leaves,tree_leaves]
    congr 1
    apply List.map_congr_left
    intro j mem
    have h := (leaf_bounds mid 7 0 [] j mem).2
    let x : Fin 8 := ⟨j,by omega⟩
    have eq (d : Fin 8) : j=d.val ↔ x=d := ⟨fun e => Fin.ext e,fun e => congrArg Fin.val e⟩
    simp only [eq,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true,x]
  · rw [tree_leaves,sum_weight]
    apply sum_congr rfl
    intro i _
    rw [mul_val,tree_leaves]

end WindowFour

namespace WindowFour
open Finset

/-- Reverse the orientation of one complementary pair, leaving all other letters fixed. -/
def flipAt (j : ℕ) : Letter → Letter
  | none => none
  | some (i,b) => some (i,if i=j then !b else b)

private theorem advance_flip (j u : ℕ) (x : Letter) : advance u (flipAt j x) = advance u x := by
  rcases x with _|⟨i,b⟩ <;> rfl

theorem allowed_flip (j : ℕ) (w : List Letter) : allowed (w.map (flipAt j)) = allowed w := by
  have compat (x y : Letter) : comp (flipAt j x) (flipAt j y) = comp x y := by
    rcases x with _|⟨i,b⟩ <;> rcases y with _|⟨k,c⟩ <;> try rfl
    by_cases h : i=k
    · subst k
      by_cases q : i=j <;> cases b <;> cases c <;> simp [flipAt,comp,q]
    · have ne : (i == k) = false := by simpa using h
      simp [flipAt,comp,ne]
  rcases w with _|⟨a,_|⟨b,_|⟨c,_|⟨d,w⟩⟩⟩⟩ <;> try rfl
  simp only [List.map_cons,allowed,compat]

/-- Every branch has a partner after flipping an orientation. The two branches
for the flipped pair exchange places and all other labels stay in place. -/
theorem tree_flip (j : ℕ) (mid : Bool) (weight : ℕ → ℕ) (f u : ℕ) (w : List Letter) :
    tree mid weight f u (w.map (flipAt j)) = tree mid weight f u w := by
  induction f generalizing u w with
  | zero => rfl
  | succ f ih =>
    let L (x : Letter) := if allowed (x::w) then tree mid weight f (advance u x) (x::w) else 0
    let R (x : Letter) := if allowed (x::w.map (flipAt j)) then
      tree mid weight f (advance u x) (x::w.map (flipAt j)) else 0
    have term (x : Letter) : R (flipAt j x) = L x := by
      change (if allowed ((x::w).map (flipAt j)) then
        tree mid weight f (advance u (flipAt j x)) ((x::w).map (flipAt j)) else 0) = _
      rw [allowed_flip,advance_flip,ih]
    have pair (i : ℕ) : R (some (i,false)) + R (some (i,true)) =
        L (some (i,false)) + L (some (i,true)) := by
      have hf := term (some (i,false))
      have ht := term (some (i,true))
      by_cases eq : i=j
      · subst i; simp [flipAt] at hf ht; omega
      · simp [flipAt,eq] at hf ht; omega
    change ((branches mid u).map R).sum = ((branches mid u).map L).sum
    rw [branchSum,branchSum,show R none = L none from term none]
    simp only [pair]

private theorem range_map_sum (g : ℕ → ℕ) (u : ℕ) :
    ((List.range u).map g).sum = ∑ i ∈ range u, g i := by
  induction u with
  | zero => simp
  | succ u ih => simp [List.range_succ,sum_range_succ,ih]

/-- Count only the false orientation when introducing a label, with multiplicity two. -/
def canonTree (mid : Bool) (weight : ℕ → ℕ) : ℕ → ℕ → List Letter → ℕ
  | 0,u,_ => weight u
  | f+1,u,w =>
    let next (x : Letter) := if allowed (x::w) then canonTree mid weight f (advance u x) (x::w) else 0
    (if mid then next none else 0) + ((List.range u).map fun i =>
      next (some (i,false)) + next (some (i,true))).sum + 2 * next (some (u,false))

private theorem flip_fresh (u : ℕ) (w : List Letter) (bd : ∀ x∈w, bounded u x) :
    w.map (flipAt u) = w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    have hx := bd x (by simp)
    have fix : flipAt u x = x := by
      rcases x with _|⟨i,b⟩
      · rfl
      · exact (by simp [flipAt, (show i<u from hx).ne])
    simp only [List.map_cons,fix,ih (fun y hy => bd y (by simp [hy]))]

theorem tree_eq_canonTree (mid : Bool) (weight : ℕ → ℕ) (f u : ℕ) (w : List Letter)
    (bd : ∀ x∈w, bounded u x) : tree mid weight f u w = canonTree mid weight f u w := by
  induction f generalizing u w with
  | zero => rfl
  | succ f ih =>
    let L (x : Letter) := if allowed (x::w) then tree mid weight f (advance u x) (x::w) else 0
    let R (x : Letter) := if allowed (x::w) then canonTree mid weight f (advance u x) (x::w) else 0
    have same (x : Letter) (hx : bounded (advance u x) x) (le : u ≤ advance u x) : L x = R x := by
      change (if _ then _ else _) = (if _ then _ else _)
      rw [ih (advance u x) (x::w) ?_]
      intro y hy
      obtain rfl|mem := List.mem_cons.mp hy
      · exact hx
      · have byu := bd y mem
        rcases y with _|⟨i,b⟩
        · trivial
        · exact (show i<u from byu).trans_le le
    have fresh : L (some (u,true)) = L (some (u,false)) := by
      have eq := flip_fresh u w bd
      have check := allowed_flip u (some (u,false)::w)
      have count := tree_flip u mid weight f (u+1) (some (u,false)::w)
      simp [eq,flipAt] at check count
      simp [L,advance,check,count]
    have old (i : ℕ) (h : i<u) (b : Bool) := same (some (i,b)) (by simp [bounded,advance,h.ne,h])
      (by simp [advance,h.ne])
    have new := same (some (u,false)) (by simp [bounded,advance]) (by simp [advance])
    have nil := same none (by trivial) (by rfl)
    change ((branches mid u).map L).sum = (if mid then R none else 0) +
      ((List.range u).map (fun i => R (some (i,false)) + R (some (i,true)))).sum + 2*R (some (u,false))
    rw [branchSum,range_map_sum, fresh,new, nil, two_mul]
    congr 2
    exact sum_congr rfl fun i hi => congrArg₂ (·+·) (old i (mem_range.mp hi) false) (old i (mem_range.mp hi) true)

theorem root_canonTree (mid : Bool) (weight : ℕ → ℕ) (f : ℕ) :
    tree mid weight f 0 [] = canonTree mid weight f 0 [] := tree_eq_canonTree _ _ _ _ _ (by simp)

end WindowFour

namespace WindowFour

private theorem advance_le (u : ℕ) (x : Letter) : advance u x ≤ u+1 := by
  cases x with
  | none => simp [advance]
  | some p => simp [advance]; split <;> omega

/-- Any weight can be recovered from the eight histograms, since every leaf
has at most seven introduced labels. -/
theorem tree_by_histogram (mid : Bool) (weight : ℕ → ℕ) (d u : ℕ) (w : List Letter)
    (bound : u+d ≤ 7) :
    tree mid weight d u w = ∑ j : Fin 8, tree mid (fun n => if n=j.val then 1 else 0) d u w * weight j.val := by
  induction d generalizing u w with
  | zero =>
    simp only [tree]
    let a : Fin 8 := ⟨u,by omega⟩
    rw [Finset.sum_eq_single a]
    · simp [a]
    · intro b _ ne
      have neq : u ≠ b.val := fun e => ne (Fin.ext e.symm)
      simp [neq]
    · simp
  | succ d ih =>
    simp only [tree]
    generalize branches mid u = l
    induction l with
    | nil => simp
    | cons x l h =>
      have b : advance u x + d ≤ 7 := by have := advance_le u x; omega
      by_cases yes : allowed (x::w) = true
      · simp only [List.map_cons,List.sum_cons,if_pos yes,add_mul,Finset.sum_add_distrib]
        rw [ih _ _ b,h]
      · simp [yes,h]

private theorem sum_map_bound {α : Type*} (l : List α) (s : α → ℕ) (b : ℕ)
    (h : ∀ x, s x ≤ b) : (l.map s).sum ≤ l.length*b := by
  induction l with
  | nil => simp
  | cons a l ih => simpa [Nat.succ_mul,add_comm] using Nat.add_le_add (h a) ih

theorem tree_count_bound (mid : Bool) (j d u : ℕ) (w : List Letter) (bound : u + d ≤ 7) :
    tree mid (fun n => if n=j then 1 else 0) d u w ≤ 17^d := by
  induction d generalizing u w with
  | zero => simp [tree]; split <;> omega
  | succ d ih =>
    have lim : u ≤ 6 := by omega
    have size : (branches mid u).length ≤ 17 := by
      interval_cases u <;> cases mid <;> decide
    simp only [tree]
    apply (sum_map_bound _ _ (17^d) ?_).trans
    · rw [pow_succ]; simpa only [mul_comm (17^d)] using Nat.mul_le_mul_right (17^d) size
    · intro x
      split
      · apply ih
        have := advance_le u x
        omega
      · exact Nat.zero_le _

theorem packed_histogram (mid : Bool) :
    tree mid (fun j => (2^32)^j) 7 0 [] =
    ∑ j : Fin 8, tree mid (fun n => if n=j.val then 1 else 0) 7 0 [] * (2^32)^j.val :=
  tree_by_histogram mid _ 7 0 [] (by decide)

private theorem digits_unique (base : ℕ) (pos : 0 < base) (l : ℕ) (f g : Fin l → ℕ)
    (bf : ∀ i, f i < base) (bg : ∀ i, g i < base)
    (same : ∑ i, f i * base^i.val = ∑ i, g i * base^i.val) : ∀ i, f i = g i := by
  induction l with
  | zero => intro i; exact Fin.elim0 i
  | succ l ih =>
    have splitSum (a : Fin (l+1) → ℕ) : (∑ i, a i * base^i.val) =
        a 0 + (∑ i : Fin l, a i.succ * base^i.val) * base := by
      rw [Fin.sum_univ_succ,Finset.sum_mul]; simp [pow_succ,mul_assoc]
    rw [splitSum, splitSum] at same
    have head := congrArg (fun x : ℕ => x % base) same
    simp only [Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt (bf 0),Nat.mod_eq_of_lt (bg 0)] at head
    have eq := Nat.add_left_cancel (head ▸ same)
    have tail := Nat.eq_of_mul_eq_mul_right pos eq
    exact Fin.cases head (ih _ _ (fun i => bf i.succ) (fun i => bg i.succ) tail)

theorem histogram_of_packed (mid : Bool) (g : Fin 8 → ℕ) (bound : ∀ i, g i < 2^32)
    (packed : tree mid (fun j => (2^32)^j) 7 0 [] = ∑ i : Fin 8, g i*(2^32)^i.val) :
    ∀ i : Fin 8, tree mid (fun n => if n=i.val then 1 else 0) 7 0 [] = g i := by
  rw [packed_histogram] at packed
  exact digits_unique (2^32) (by decide) 8 _ g (fun i =>
    (tree_count_bound mid i 7 0 [] (by decide)).trans_lt (by decide)) bound packed

end WindowFour

namespace WindowFour

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem orientOdd22 : canonTree false (fun j => (2^32)^j) 5 1 [some (0,false),some (0,false)] = 32667107264341086406682951208691428229120 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem orientOdd23 : canonTree false (fun j => (2^32)^j) 5 1 [some (0,true),some (0,false)] = 23384026295295768441182096124902896774185461219328 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem orientOdd24 : canonTree false (fun j => (2^32)^j) 5 2 [some (1,false),some (0,false)] = 163688183711815587625723366434640545295535259516928 := by
  decide +kernel

private theorem orientOdd2Join (q : ℕ → ℕ) (f v2 v3 v4 : ℕ)
    (h2 : canonTree false q f 1 [some (0,false),some (0,false)] = v2)
    (h3 : canonTree false q f 1 [some (0,true),some (0,false)] = v3)
    (h4 : canonTree false q f 2 [some (1,false),some (0,false)] = v4) : canonTree false q (f+1) 1 [some (0,false)] =
      0 + ((v2 + v3) + 0) + 2 * (v4) := by
  calc
    _ = 0 + ((canonTree false q f 1 [some (0,false),some (0,false)] + canonTree false q f 1 [some (0,true),some (0,false)]) + 0) + 2 * (canonTree false q f 2 [some (1,false),some (0,false)]) := by
      rw [canonTree]
      simp only [show List.range 1 = [0] from rfl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rfl
    _ = _ := by rw [h2, h3, h4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem orientOdd2 : canonTree false (fun j => (2^32)^j) 6 1 [some (0,false)] = 350760393751594050956969915400866938573947408482304 := by
  exact orientOdd2Join (fun j => (2^32)^j) 5 32667107264341086406682951208691428229120 23384026295295768441182096124902896774185461219328 163688183711815587625723366434640545295535259516928 orientOdd22 orientOdd23 orientOdd24

private theorem orientOddJoin (q : ℕ → ℕ) (f v2 : ℕ)
    (h2 : canonTree false q f 1 [some (0,false)] = v2) : canonTree false q (f+1) 0 [] =
      0 + 0 + 2 * (v2) := by
  calc
    _ = 0 + 0 + 2 * (canonTree false q f 1 [some (0,false)]) := by
      rw [canonTree]
      simp only [show List.range 0 = [] from rfl, List.map_nil, List.sum_nil]
      rfl
    _ = _ := by rw [h2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem orientOdd : canonTree false (fun j => (2^32)^j) 7 0 [] = 701520787503188101913939830801733877147894816964608 := by
  exact orientOddJoin (fun j => (2^32)^j) 6 350760393751594050956969915400866938573947408482304 orientOdd2

theorem packedOdd : tree false (fun j => (2^32)^j) 7 0 [] = 701520787503188101913939830801733877147894816964608 :=
  (root_canonTree _ _ _).trans orientOdd

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem orientEven11 : canonTree true (fun j => (2^32)^j) 5 0 [none,none] = 5444517891017425030797793374550861283329 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem orientEven12 : canonTree true (fun j => (2^32)^j) 5 1 [some (0,false),none] = 38111625159161463239678065801596193734656 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem orientEven21 : canonTree true (fun j => (2^32)^j) 5 1 [none,some (0,false)] = 38111625160112201190845362032733396664320 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem orientEven22 : canonTree true (fun j => (2^32)^j) 5 1 [some (0,false),some (0,false)] = 32667107275749941816890476703231005163520 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem orientEven23 : canonTree true (fun j => (2^32)^j) 5 1 [some (0,true),some (0,false)] = 23384026306184804214977217276308129209792747012096 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem orientEven24 : canonTree true (fun j => (2^32)^j) 5 2 [some (1,false),some (0,false)] = 163688183768983025339587918247338702563187439435776 := by
  decide +kernel

private theorem orientEven1Join (q : ℕ → ℕ) (f v1 v2 : ℕ)
    (h1 : canonTree true q f 0 [none,none] = v1)
    (h2 : canonTree true q f 1 [some (0,false),none] = v2) : canonTree true q (f+1) 0 [none] =
      v1 + 0 + 2 * (v2) := by
  calc
    _ = canonTree true q f 0 [none,none] + 0 + 2 * (canonTree true q f 1 [some (0,false),none]) := by
      rw [canonTree]
      simp only [show List.range 0 = [] from rfl, List.map_nil, List.sum_nil]
      rfl
    _ = _ := by rw [h1, h2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem orientEven1 : canonTree true (fun j => (2^32)^j) 6 0 [none] = 81667768209340351510153924977743248752641 := by
  exact orientEven1Join (fun j => (2^32)^j) 5 5444517891017425030797793374550861283329 38111625159161463239678065801596193734656 orientEven11 orientEven12

private theorem orientEven2Join (q : ℕ → ℕ) (f v1 v2 v3 v4 : ℕ)
    (h1 : canonTree true q f 1 [none,some (0,false)] = v1)
    (h2 : canonTree true q f 1 [some (0,false),some (0,false)] = v2)
    (h3 : canonTree true q f 1 [some (0,true),some (0,false)] = v3)
    (h4 : canonTree true q f 2 [some (1,false),some (0,false)] = v4) : canonTree true q (f+1) 1 [some (0,false)] =
      v1 + ((v2 + v3) + 0) + 2 * (v4) := by
  calc
    _ = canonTree true q f 1 [none,some (0,false)] + ((canonTree true q f 1 [some (0,false),some (0,false)] + canonTree true q f 1 [some (0,true),some (0,false)]) + 0) + 2 * (canonTree true q f 2 [some (1,false),some (0,false)]) := by
      rw [canonTree]
      simp only [show List.range 1 = [0] from rfl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rfl
    _ = _ := by rw [h1, h2, h3, h4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem orientEven2 : canonTree true (fun j => (2^32)^j) 6 1 [some (0,false)] = 350760393914929587330015196778721373072132027711488 := by
  exact orientEven2Join (fun j => (2^32)^j) 5 38111625160112201190845362032733396664320 32667107275749941816890476703231005163520 23384026306184804214977217276308129209792747012096 163688183768983025339587918247338702563187439435776 orientEven21 orientEven22 orientEven23 orientEven24

private theorem orientEvenJoin (q : ℕ → ℕ) (f v1 v2 : ℕ)
    (h1 : canonTree true q f 0 [none] = v1)
    (h2 : canonTree true q f 1 [some (0,false)] = v2) : canonTree true q (f+1) 0 [] =
      v1 + 0 + 2 * (v2) := by
  calc
    _ = canonTree true q f 0 [none] + 0 + 2 * (canonTree true q f 1 [some (0,false)]) := by
      rw [canonTree]
      simp only [show List.range 0 = [] from rfl, List.map_nil, List.sum_nil]
      rfl
    _ = _ := by rw [h1, h2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem orientEven : canonTree true (fun j => (2^32)^j) 7 0 [] = 701520787911526942869370745067596671122007304175617 := by
  exact orientEvenJoin (fun j => (2^32)^j) 6 81667768209340351510153924977743248752641 350760393914929587330015196778721373072132027711488 orientEven1 orientEven2

theorem packedEven : tree true (fun j => (2^32)^j) 7 0 [] = 701520787911526942869370745067596671122007304175617 :=
  (root_canonTree _ _ _).trans orientEven

end WindowFour

namespace WindowFour

theorem hist_odd (j : Fin 8) :
    tree false (fun i => if i = j.val then 1 else 0) 7 0 [] =
      [0,88,3784,10000,4656,480,0,0][j.val]! := by
  apply histogram_of_packed false (fun j => [0,88,3784,10000,4656,480,0,0][j.val]!) _ _ j
  · decide
  · rw [packedOdd]
    decide +kernel

theorem hist_even (j : Fin 8) :
    tree true (fun i => if i = j.val then 1 else 0) 7 0 [] =
      [1,1500,14232,18208,5856,480,0,0][j.val]! := by
  apply histogram_of_packed true (fun j => [1,1500,14232,18208,5856,480,0,0][j.val]!) _ _ j
  · decide
  · rw [packedEven]
    decide +kernel

end WindowFour

namespace WindowFour

theorem polynomial_even (m : ℕ) :
    (↑(∑ j : Fin 8, m.descFactorial j.val *
      ([1,1500,14232,18208,5856,480,0,0] : List ℕ)[j.val]!) : ℚ) =
       1 + 34*(2*(m:ℚ)) + 6*(2*(m:ℚ))^2 - 16*(2*(m:ℚ))^3 +
         66*(2*(m:ℚ))^4 + 15*(2*(m:ℚ))^5 := by
  rcases le_or_gt 5 m with h|h
  · simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Finset.sum_empty,
      Finset.univ_eq_empty, Nat.zero_add]
    norm_num [Nat.descFactorial_succ]
    push_cast [Nat.cast_sub (by omega : 1 ≤ m),Nat.cast_sub (by omega : 2 ≤ m),
        Nat.cast_sub (by omega : 3 ≤ m),Nat.cast_sub (by omega : 4 ≤ m)]
    ring
  · interval_cases m <;> norm_num [Fin.sum_univ_succ,Nat.descFactorial_succ]

theorem polynomial_odd (m : ℕ) :
    (↑(∑ j : Fin 8, (m+1).descFactorial j.val *
      ([0,88,3784,10000,4656,480,0,0] : List ℕ)[j.val]!) : ℚ) =
       58 + 57*(2*(m:ℚ)+1) - 80*(2*(m:ℚ)+1)^2 - 28*(2*(m:ℚ)+1)^3 +
         66*(2*(m:ℚ)+1)^4 + 15*(2*(m:ℚ)+1)^5 := by
  rcases le_or_gt 5 m with h|h
  · simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Finset.sum_empty,
      Finset.univ_eq_empty, Nat.zero_add]
    norm_num [Nat.descFactorial_succ]
    push_cast [Nat.cast_sub (by omega : 1 ≤ m),Nat.cast_sub (by omega : 2 ≤ m),
        Nat.cast_sub (by omega : 3 ≤ m),Nat.cast_sub (by omega : 4 ≤ m)]
    ring
  · interval_cases m <;> norm_num [Fin.sum_univ_succ,Nat.descFactorial_succ]

end WindowFour

namespace WindowFour

open PowerSeries

/-- The two parity formulas give the generating function, with zero constant term
as specified by the offset of the sequence. -/
theorem series (a : ℕ → ℤ)
    (even : ∀ n : ℕ, 1 ≤ n → Even n →
      (a n : ℚ) = 1 + 34 * (n : ℚ) + 6 * (n : ℚ)^2 - 16 * (n : ℚ)^3 +
        66 * (n : ℚ)^4 + 15 * (n : ℚ)^5)
    (odd : ∀ n : ℕ, 1 ≤ n → Odd n →
      (a n : ℚ) = 58 + 57 * (n : ℚ) - 80 * (n : ℚ)^2 - 28 * (n : ℚ)^3 +
        66 * (n : ℚ)^4 + 15 * (n : ℚ)^5) :
    mk (fun n => if n < 1 then 0 else (a n : ℚ)) *
        ((1 - X)^6 * (1 + X)^4 : PowerSeries ℚ) =
      X * (88 + 1325 * X + 4478 * X^2 + 12178 * X^3 + 8990 * X^4 +
        2708 * X^5 - 310 * X^6 - 658 * X^7 + 2 * X^8 - X^9) := by
  let b (n : ℕ) : ℚ := if n < 1 then 0 else (a n : ℚ)
  let f (x : ℚ) := 1 + 34*x + 6*x^2 - 16*x^3 + 66*x^4 + 15*x^5
  let g (x : ℚ) := 58 + 57*x - 80*x^2 - 28*x^3 + 66*x^4 + 15*x^5
  have value (n : ℕ) : b n = if n = 0 then 0 else if n%2 = 0 then f n else g n := by
    by_cases z : n = 0
    · simp [b,z]
    have pos : 1 ≤ n := by omega
    by_cases e : n%2 = 0
    · simpa [b,z,e,not_lt.mpr pos,f] using even n pos (Nat.even_iff.mpr e)
    · simpa [b,z,e,not_lt.mpr pos,g] using odd n pos (Nat.odd_iff.mpr (by omega))
  let B := mk b
  calc
    _ = B - (2:ℕ) • (X^1 * B) - (3:ℕ) • (X^2 * B) + (8:ℕ) • (X^3 * B) +
        (2:ℕ) • (X^4 * B) - (12:ℕ) • (X^5 * B) + (2:ℕ) • (X^6 * B) +
        (8:ℕ) • (X^7 * B) - (3:ℕ) • (X^8 * B) - (2:ℕ) • (X^9 * B) + X^10 * B := by
          dsimp [B,b]; simp only [nsmul_eq_mul]; ring
    _ = (88:ℕ) • X^1 + (1325:ℕ) • X^2 + (4478:ℕ) • X^3 + (12178:ℕ) • X^4 +
        (8990:ℕ) • X^5 + (2708:ℕ) • X^6 - (310:ℕ) • X^7 - (658:ℕ) • X^8 +
        (2:ℕ) • X^9 - X^10 := by
      apply PowerSeries.ext
      intro n
      simp only [B, map_sub, map_add, map_nsmul, coeff_X_pow_mul', coeff_X_pow, coeff_mk, value]
      simp only [nsmul_eq_mul]
      by_cases low : n ≤ 10
      · interval_cases n <;> norm_num [f,g]
      · obtain ⟨k,rfl⟩ : ∃ k, n = k+11 := ⟨n-11,by omega⟩
        have parity : k%2 = 0 ∨ k%2 = 1 := by omega
        rcases parity with e | e <;>
          simp +arith [Nat.add_mod, e, Nat.add_sub_assoc, f, g] <;> ring
    _ = _ := by simp only [nsmul_eq_mul]; ring

end WindowFour

namespace WindowFour
open OMA.S_oeis_a245954

theorem even_count (n : ℕ) (_ : 1 ≤ n) (par : Even n) :
    (a n : ℚ) = 1 + 34*(n:ℚ) + 6*(n:ℚ)^2 - 16*(n:ℚ)^3 + 66*(n:ℚ)^4 + 15*(n:ℚ)^5 := by
  obtain ⟨m,hm⟩ := par
  have en : n=2*m := by omega
  have idx : (n+1)/2 = m := by omega
  have mode : (n%2==0) = true := by simp [en]
  rw [original_count,idx,mode,root_from_histogram]
  simp only [hist_even,Int.cast_natCast]
  simpa only [en,Nat.cast_mul,Nat.cast_ofNat] using polynomial_even m

theorem odd_count (n : ℕ) (_ : 1 ≤ n) (par : Odd n) :
    (a n : ℚ) = 58 + 57*(n:ℚ) - 80*(n:ℚ)^2 - 28*(n:ℚ)^3 + 66*(n:ℚ)^4 + 15*(n:ℚ)^5 := by
  obtain ⟨m,hm⟩ := par
  have en : n=2*m+1 := by omega
  have idx : (n+1)/2=m+1 := by omega
  have mode : (n%2==0) = false := by simp [en,Nat.add_mod]
  rw [original_count,idx,mode,root_from_histogram]
  simp only [hist_odd,Int.cast_natCast]
  simpa only [en,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using polynomial_odd m

end WindowFour

theorem OMA.solution : type_of% @OMA.S_oeis_a245954.main :=
  ⟨WindowFour.series OMA.S_oeis_a245954.a WindowFour.even_count WindowFour.odd_count,
    WindowFour.even_count,WindowFour.odd_count⟩
