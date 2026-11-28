import OMAStatements.S_oeis_a340138
import Mathlib.Data.Nat.Log
import Mathlib.Combinatorics.Pigeonhole

/-!
# Explicit position and value bounds for the digital-root permutation

Michael De Vlieger proposed the permutation in OEIS A340138. An earlier
proof of bijectivity appears in blakestone-x/open-math-agents at 21379df6e861.
The registered statement uses the digital root of the immediately preceding
term, as in De Vlieger's program and its published values.

This proof gives two explicit finite bounds. The term at zero-based index n
is at most 10n+19. Every x occurs by index 900x+992. The proof of the latter
estimate counts requests up to a finite time, using short decimal witnesses
with a prescribed units digit and digital root.
-/

namespace OmaDigits
open OMA.S_oeis_a340138

/-- Every positive integer has a nonzero leading decimal digit. -/
theorem digit_witness (y : ℕ) (hy : 0<y) : ∃ d, 1≤d ∧ d≤9 ∧ hasDigit y d := by
  let j := Nat.log 10 y
  have ppos : 0 < 10^j := Nat.pow_pos (by decide)
  have low : 10^j ≤ y := Nat.pow_log_le_self 10 (by omega)
  have high : y < 10^j*10 := by
    simpa only [j, Nat.pow_succ] using Nat.lt_pow_succ_log_self (b:=10) (by decide) y
  have lb : 0 < y/10^j := Nat.div_pos low ppos
  have ub : y/10^j < 10 := (Nat.div_lt_iff_lt_mul ppos).mpr ((Nat.mul_comm _ _ ▸ high))
  refine ⟨y/10^j, lb, by omega, j, low, Nat.mod_eq_of_lt ub⟩

/-- There are arbitrarily large numbers ending in a prescribed digit and
having any prescribed positive digital root. -/
theorem root_witness (d r N : ℕ) (hd : d≤9) (hr : 1≤r) (hr' : r≤9) :
    ∃ y, N<y ∧ hasDigit y d ∧ root y=r := by
  let q := 9*(N+2)+9+r-d
  let y := 10*q+d
  have h : N<y := by dsimp [y,q]; omega
  refine ⟨y, h, ⟨0, by simp; omega, ?_⟩, ?_⟩
  · simp only [pow_zero, Nat.div_one]
    dsimp [y]
    omega
  · simp only [root, if_neg (show y≠0 by omega)]
    dsimp [y,q]
    omega

end OmaDigits

namespace OmaDigits
open OMA.S_oeis_a340138 Finset

def hit (t x : ℕ) : Prop := ∃ i<t, term i=x

noncomputable def requests (t d : ℕ) : Finset ℕ := (range t).filter fun i => root (term i)=d

private theorem from_history {n x : ℕ} (h : x∈history n) : hit (n+1) x := by
  induction n with
  | zero =>
    have hx : x=0 := by simpa [history] using h
    exact ⟨0, by decide, hx.symm⟩
  | succ n ih =>
    rcases List.mem_cons.mp h with e|old
    · exact ⟨n+1, by omega, e.symm⟩
    · obtain ⟨i, hi, eq⟩ := ih old
      exact ⟨i, by omega, eq⟩

private theorem hit_of_count (inj : Function.Injective term) {s d x : ℕ}
    (positive : 0<x) (digit : hasDigit x d) (cnt : x < (requests s d).card) :
    hit (s+1) x := by
  by_contra missing
  have limited : Set.MapsTo (fun i => term (i+1)) ↑(requests s d) ↑(range x) := by
    intro i hi
    have mem := Finset.mem_filter.mp hi
    have bound := Finset.mem_range.mp mem.1
    have absent : x ∉ history i := by
      intro hx
      obtain ⟨j,hj,eq⟩ := from_history hx
      exact missing ⟨j,by omega,eq⟩
    have least : term (i+1) ≤ x := Nat.sInf_le
      (s:={k : ℕ | k∉history i ∧ 0<k ∧ hasDigit k (root (term i))})
      ⟨absent,positive,mem.2.symm ▸ digit⟩
    have ne : term (i+1) ≠ x := fun e => missing ⟨i+1,by omega,e⟩
    exact mem_range.mpr (lt_of_le_of_ne least ne)
  have card := Finset.card_le_card_of_injOn _ limited
    (fun _ _ _ _ eq => Nat.add_right_cancel (inj eq))
  rw [Finset.card_range] at card
  omega

private def lastDigitNumber (d r k : ℕ) := 10*(9*k+((r+8-d)%9+1))+d

/-- The inverse permutation has an explicit linear upper bound. -/
theorem linear_hit (inj : Function.Injective term) (x : ℕ) : hit (900*x+993) x := by
  by_cases hx : x=0
  · exact ⟨0,by omega,hx.symm⟩
  obtain ⟨r,hr1,hr9,hdigit⟩ := digit_witness x (by omega)
  let l := 90*x+99
  let s := 10*l+1
  have rsmall (i : ℕ) : root (term i)<10 := by unfold root; split <;> omega
  obtain ⟨d,hd,count⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s:=range s) (t:=range 10) (f:=fun i => root (term i)) (n:=l)
    (fun i _ => mem_range.mpr (rsmall i)) (by simp [s])
  have d9 : d≤9 := by have := mem_range.mp hd; omega
  have numbered (k : ℕ) (hk : k≤x) : hit (s+1) (lastDigitNumber d r k) := by
    have positive : 0 < lastDigitNumber d r k := by unfold lastDigitNumber; omega
    have digs : hasDigit (lastDigitNumber d r k) d := by
      refine ⟨0,by simp; omega,?_⟩
      simp only [pow_zero,Nat.div_one]
      unfold lastDigitNumber
      omega
    apply hit_of_count inj positive digs
    change l < (requests s d).card at count
    apply lt_of_le_of_lt _ count
    dsimp [l,lastDigitNumber]
    omega
  choose index hi eq using fun (k : Fin (x+1)) => numbered k.val (by have := k.isLt; omega)
  have atRoot (k : ℕ) : root (lastDigitNumber d r k)=r := by
    unfold root lastDigitNumber
    split <;> omega
  have imem (k : Fin (x+1)) : index k ∈ requests (s+1) r := by
    apply mem_filter.mpr
    exact ⟨mem_range.mpr (hi k),by rw [eq,atRoot]⟩
  have emb : Function.Injective index := by
    intro a b e
    have same : lastDigitNumber d r a.val=lastDigitNumber d r b.val := (eq a).symm.trans ((congrArg term e).trans (eq b))
    apply Fin.ext
    unfold lastDigitNumber at same
    omega
  have many := Finset.card_le_card_of_injOn index (s:=univ) (t:=requests (s+1) r)
    (fun k _ => imem k) emb.injOn
  simp only [card_univ,Fintype.card_fin] at many
  have h := hit_of_count inj (by omega : 0<x) hdigit (by omega : x < (requests (s+1) r).card)
  rwa [show s+1+1 = 900*x+993 by dsimp [s,l]; omega] at h

end OmaDigits

namespace OmaDigits
open OMA.S_oeis_a340138 Finset

private theorem seen {i n : ℕ} (h : i≤n) : term i∈history n := by
  induction n with
  | zero =>
    obtain rfl : i=0 := by omega
    exact List.mem_cons_self
  | succ n ih =>
    by_cases hi : i=n+1
    · subst i; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih (by omega))

private theorem length_history (n : ℕ) : (history n).length=n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [history,ih]

private theorem digit_zero {d k : ℕ} (hd : d<10) (hk : 0<10*(k+1)+d) :
    hasDigit (10*(k+1)+d) d := by
  refine ⟨0,by rw [pow_zero]; exact hk,?_⟩
  simp only [pow_zero,Nat.div_one]
  omega

/-- A decimal digit appears in the units place of one of every ten consecutive integers. -/
private theorem choice_bound (n : ℕ) :
    term (n+1) ∉ history n ∧ term (n+1) ≤ 10*n+29 := by
  let d := root (term n)
  have hd : d<10 := by dsimp [d,root]; split <;> omega
  have candidate : ∃ k : Fin (n+2), 10*(k.val+1)+d ∉ history n := by
    classical
    by_contra! contra
    let f := fun k : Fin (n+2) => 10*(k.val+1)+d
    have inj : Function.Injective f := by
      intro i j e
      apply Fin.ext
      dsimp [f] at e
      omega
    have hc := Finset.card_le_card_of_injOn f (s:=univ) (t:=(history n).toFinset)
      (fun k _ => List.mem_toFinset.mpr (contra k)) inj.injOn
    have le := List.toFinset_card_le (l := history n)
    rw [length_history] at le
    simp only [card_univ,Fintype.card_fin] at hc
    omega
  obtain ⟨k,hk⟩ := candidate
  let A := {y : ℕ | y∉history n ∧ 0<y ∧ hasDigit y d}
  have pos : 0<10*(k.val+1)+d := by omega
  have inA : 10*(k.val+1)+d ∈ A := ⟨hk,pos,digit_zero hd pos⟩
  have membrane : sInf A ∈ A := Nat.sInf_mem ⟨_,inA⟩
  have hb := Nat.sInf_le inA
  change sInf A ∉ history n ∧ sInf A ≤ _
  exact ⟨membrane.1,by have := k.isLt; omega⟩

theorem bounds : Function.Bijective term ∧ (∀ n, term n ≤ 10*n+19) ∧
    ∀ x, ∃ j ≤ 900*x+992, term j=x := by
  have inj : Function.Injective term := by
    apply Function.Injective.of_lt_imp_ne
    intro i j hij
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
    exact fun e => (choice_bound k).1 (e ▸ seen (show i≤k by omega))
  have found (x : ℕ) : ∃ j≤900*x+992, term j=x := by
    obtain ⟨j,hj,eq⟩ := linear_hit inj x
    exact ⟨j,by omega,eq⟩
  refine ⟨⟨inj,fun x => (found x).imp (fun j hj => hj.2)⟩,?_,found⟩
  intro n
  cases n with
  | zero => decide +kernel
  | succ k => have := (choice_bound k).2; omega

end OmaDigits
