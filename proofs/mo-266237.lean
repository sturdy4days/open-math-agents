import OMAStatements.S_mo_266237
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Distance distribution of random balanced assignments

We prove the contingency-table formula in @LDJAI's formalization of Steve's
MathOverflow question 266237. Restricting each assignment to the reference
classes turns a table fiber into a product of independent row fibers. The
multinomial theorem counts labelings of each row with its prescribed counts.
-/

namespace Census266
open Finset

/-- The number of points with reference label i and assigned label j. -/
def table {N K : ℕ} (τ f : Fin N → Fin K) (i j : Fin K) : ℕ :=
  (univ.filter fun x => τ x=i ∧ f x=j).card

end Census266

namespace BalancedCensus
open Finset MvPolynomial OMA.S_mo_266237

/-- Expand one sum of label variables for each object. Grouping monomials by
their exponent vectors counts the assignments with any prescribed fiber sizes. -/
theorem multinomial_fiber {A : Type*} [Fintype A] [DecidableEq A] {K : ℕ} (t : Fin K → ℕ)
    (ht : ∑ j, t j = Fintype.card A) :
    ((univ : Finset (A → Fin K)).filter (fun f => counts f = t)).card = Nat.multinomial univ t := by
  classical
  let d : Fin K →₀ ℕ := Finsupp.equivFunOnFinite.symm t
  let w (f : A → Fin K) : Fin K →₀ ℕ := ∑ x, Finsupp.single (f x) 1
  have eval (f : A → Fin K) (j : Fin K) : w f j = counts f j := by
    simp only [w,Finsupp.finsetSum_apply,Finsupp.single_apply,counts,card_filter]
  have same (f : A → Fin K) : w f = d ↔ counts f = t := by
    constructor
    · intro h
      funext j
      rw [← eval, h]; rfl
    · intro h
      ext j
      change w f j = t j
      rw [eval, h]
  have mono (f : A → Fin K) : (∏ a, X (f a) : MvPolynomial (Fin K) ℕ) = monomial (w f) 1 :=
    (monomial_sum_one univ (fun a => Finsupp.single (f a) 1)).symm
  have total : d.sum (fun _ n => n) = Fintype.card A := by
    rw [Finsupp.sum_of_support_subset d (subset_univ _) _ (by simp)]
    exact ht
  calc
    _ = ∑ f : A → Fin K, coeff d (∏ a, (X (f a) : MvPolynomial (Fin K) ℕ)) := by
      rw [card_filter]
      refine sum_congr rfl fun f _ => ?_
      simp only [mono,coeff_monomial,same]
    _ = coeff d ((∑ j, (X j : MvPolynomial (Fin K) ℕ))^(Fintype.card A)) := by
      rw [← coeff_sum, ← Fintype.prod_sum (fun (_ : A) (j : Fin K) => (X j : MvPolynomial (Fin K) ℕ))]
      simp
    _ = _ := by
      rw [coeff_sum_X_pow_of_fintype,if_pos total,Finsupp.multinomial_eq_of_support_subset (subset_univ _)]
      rfl

end BalancedCensus

namespace Census266
open Finset OMA.S_mo_266237
variable {N K : ℕ}

private theorem restrict_counts (τ f : Fin N → Fin K) (i j : Fin K) :
    counts (fun x : {x // τ x=i} => f x.val) j = table τ f i j := by
  classical
  unfold counts table
  apply card_bij (fun (x : {x // τ x=i}) _ => x.val)
  · intro x hx
    exact mem_filter.mpr ⟨mem_univ _,x.property,(mem_filter.mp hx).2⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro x hx
    obtain ⟨hτ,hf⟩ := (mem_filter.mp hx).2
    exact ⟨⟨x,hτ⟩,mem_filter.mpr ⟨mem_univ _,hf⟩,rfl⟩

/-- Restricting an assignment to each reference class gives independent
row assignments with the specified color counts. -/
private def rowEquiv (τ : Fin N → Fin K) (t : Fin K → Fin K → ℕ) :
    {f : Fin N → Fin K // table τ f=t} ≃
      (∀ i : Fin K, {g : {x // τ x=i} → Fin K // counts g=t i}) where
  toFun f i := ⟨fun x => f.val x.val, funext fun j =>
    (restrict_counts τ f.val i j).trans (congrFun (congrFun f.property i) j)⟩
  invFun g := ⟨fun x => (g (τ x)).val ⟨x,rfl⟩, by
    funext i j
    rw [← restrict_counts]
    have eq : (fun x : {x // τ x=i} => (g (τ x.val)).val ⟨x.val,rfl⟩) = (g i).val := by
      funext ⟨x,h⟩
      subst i
      rfl
    rw [eq,(g i).property]⟩
  left_inv _ := rfl
  right_inv g := by
    funext i
    apply Subtype.ext
    funext ⟨x,h⟩
    subst i
    rfl

/-- The cardinality of a fixed table is the product of its row counts. -/
theorem row_fibers (τ : Fin N → Fin K) (t : Fin K → Fin K → ℕ) :
    ((univ : Finset (Fin N → Fin K)).filter fun f => table τ f=t).card =
      ∏ i, ((univ : Finset ({x // τ x=i} → Fin K)).filter fun g => counts g=t i).card := by
  classical
  simpa only [Fintype.card_pi,Fintype.card_subtype] using Fintype.card_congr (rowEquiv τ t)

end Census266

namespace Census266
open Finset OMA.S_mo_266237

private theorem sum_fibers {N K : ℕ} (s : Finset (Fin N)) (g : Fin N → Fin K) :
    (∑ i, (s.filter fun x => g x=i).card) = s.card :=
  (card_eq_sum_card_fiberwise (f:=g) (t:=univ) (fun _ _ => mem_univ _)).symm

theorem row_sum {N K : ℕ} (τ f : Fin N → Fin K) (i : Fin K) :
    (∑ j, table τ f i j) = counts τ i := by
  simpa only [filter_filter, table, counts] using sum_fibers (univ.filter fun x => τ x=i) f

theorem col_sum {N K : ℕ} (τ f : Fin N → Fin K) (j : Fin K) :
    (∑ i, table τ f i j) = counts f j := by
  simpa only [filter_filter, table, counts, and_comm] using sum_fibers (univ.filter fun x => f x=j) τ

/-- For each permutation, the off-diagonal cells partition its mismatch set. -/
theorem distance_eq {N K : ℕ} (τ f : Fin N → Fin K) :
    distance f τ = tableDistance (table τ f) := by
  classical
  apply congrArg (univ.inf' univ_nonempty)
  funext p
  let bad := univ.filter fun x => f x ≠ p (τ x)
  change bad.card = ∑ i, ∑ j, if j=p i then 0 else table τ f i j
  rw [← sum_fibers bad τ]
  apply sum_congr rfl
  intro i _
  rw [← sum_fibers _ f]
  apply sum_congr rfl
  intro j _
  have slice : ((bad.filter fun x => τ x=i).filter fun x => f x=j) =
      if j=p i then ∅ else univ.filter fun x => τ x=i ∧ f x=j := by
    ext x
    by_cases hi : τ x=i <;> by_cases hj : f x=j <;> by_cases h : j=p i <;> simp [bad,hi,hj,h]
  rw [slice]
  by_cases h : j=p i <;> simp [h,table]

theorem table_mem_iff {N K m : ℕ} (τ f : Fin N → Fin K) (hτ : τ∈balanced N K m) :
    table τ f ∈ tables K m ↔ f ∈ balanced N K m := by
  have rows : ∀ i, counts τ i=m := fun i => congrFun (mem_filter.mp hτ).2 i
  simp [tables, Fintype.mem_piFinset, mem_piAntidiag, row_sum, col_sum, rows, balanced, funext_iff]

end Census266

namespace Census266
open Finset OMA.S_mo_266237

/-- Every balanced table has a product of row multinomials as its fiber size. -/
theorem table_fiber {N K m : ℕ} (τ : Fin N → Fin K) (hτ : τ∈balanced N K m)
    (t : Fin K → Fin K → ℕ) (ht : t∈tables K m) :
    ((univ : Finset (Fin N→Fin K)).filter fun f => table τ f=t).card = weight t := by
  classical
  rw [row_fibers]
  apply prod_congr rfl
  intro i _
  apply BalancedCensus.multinomial_fiber
  have row : ∑ j, t i j = m := (mem_piAntidiag.mp (Fintype.mem_piFinset.mp (mem_filter.mp ht).1 i)).1
  have reference : counts τ i = m := congrFun (mem_filter.mp hτ).2 i
  simpa [Fintype.card_subtype,← reference,counts] using row

theorem numerator {N K m : ℕ} (τ : Fin N → Fin K) (hτ : τ∈balanced N K m) (d : ℕ) :
    ((balanced N K m).filter fun f => distance f τ=d).card =
      ∑ t ∈ (tables K m).filter (fun t => tableDistance t=d), weight t := by
  classical
  let F := (balanced N K m).filter fun f => distance f τ=d
  let T := (tables K m).filter fun t => tableDistance t=d
  change F.card = ∑ t ∈ T, weight t
  have maps (f) (hf : f∈F) : table τ f∈T := by
    obtain ⟨hb,hd⟩ := mem_filter.mp hf
    exact mem_filter.mpr ⟨(table_mem_iff τ f hτ).mpr hb, (distance_eq τ f).symm.trans hd⟩
  rw [card_eq_sum_card_fiberwise (f:=table τ) (t:=T) maps]
  apply sum_congr rfl
  intro t ht
  obtain ⟨htm,htd⟩ := mem_filter.mp ht
  rw [← table_fiber τ hτ t htm]
  congr 1
  ext f
  simp only [mem_filter,mem_univ,true_and]
  constructor
  · exact And.right
  · intro h
    refine ⟨mem_filter.mpr ⟨(table_mem_iff τ f hτ).mp (h ▸ htm),?_⟩,h⟩
    rw [distance_eq, h, htd]

end Census266

open Census266 OMA.S_mo_266237

theorem OMA.solution : type_of% @OMA.S_mo_266237.main := by
  intro N K m _ hN τ hτ d
  classical
  have total : (balanced N K m).card = Nat.multinomial Finset.univ (fun _ : Fin K => m) := by
    apply BalancedCensus.multinomial_fiber
    simpa using hN.symm
  rw [numerator τ hτ d,total]
