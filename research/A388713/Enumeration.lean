import OMAStatements.S_oeis_a388713
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Tactic

/-!
# Distinct representatives for the initial intervals of a partition

Gus Wiseman proposed the interpretation in OEIS A388713. This proof
formalizes Clément Garrot's prefix pigeonhole argument, recorded in A387112
on August 31, 2026. The registered statement is due to @esracummings31-blip.

Sources: https://oeis.org/A388713 and https://oeis.org/A387112.
-/

namespace NestedIntervals
open OMA.S_oeis_a388713

/-- For nested initial intervals, each prefix must fit into its largest interval.
When this holds, its one-based ranks supply distinct representatives. -/
theorem choosable_iff (y : List ℕ) (ordered : y.Pairwise (· ≤ ·)) :
    Choosable y ↔ Superdiagonal y := by
  constructor
  · rintro ⟨z,unique,hz⟩ i
    let index (j : Fin (i.val+1)) : Fin y.length := ⟨j.val,by have := j.isLt; omega⟩
    have below (j : Fin (i.val+1)) : y.get (index j) ≤ y.get i :=
      ordered.rel_get_of_le (by change j.val ≤ i.val; omega)
    let f (j : Fin (i.val+1)) : Fin (y.get i) :=
      ⟨z (index j)-1,by have h := hz (index j); have b := below j; omega⟩
    have inj : Function.Injective f := by
      intro u v eq
      have h := congrArg Fin.val eq
      change z (index u) - 1 = z (index v) - 1 at h
      have eu := (hz (index u)).1
      have ev := (hz (index v)).1
      have eqindex := unique (show z (index u) = z (index v) by omega)
      exact Fin.ext (congrArg (fun t : Fin y.length => t.val) eqindex)
    simpa using Fintype.card_le_of_injective f inj
  · intro h
    refine ⟨fun i => i.val+1, ?_, fun i => ⟨Nat.succ_pos _,h i⟩⟩
    exact fun i j eq => Fin.ext (Nat.succ.inj eq)

/-- Reversing the list only changes the indexing of a system of distinct representatives. -/
theorem choosable_reverse (y : List ℕ) : Choosable y.reverse ↔ Choosable y := by
  have flip (l : List ℕ) (h : Choosable l) : Choosable l.reverse := by
    obtain ⟨z,inj,valid⟩ := h
    let idx (i : Fin l.reverse.length) : Fin l.length := (i.cast l.length_reverse).rev
    refine ⟨fun i => z (idx i),inj.comp (Fin.rev_injective.comp (Fin.cast_injective _)),?_⟩
    intro i
    have eq : l.reverse.get i = l.get (idx i) := by
      simp [List.get_eq_getElem,idx,Fin.rev,Nat.sub_sub,Nat.add_comm]
    rw [eq]
    exact valid (idx i)
  exact ⟨fun h => by simpa using flip y.reverse h,flip y⟩

end NestedIntervals

theorem OMA.solution : type_of% @OMA.S_oeis_a388713.main := by
  intro n k
  unfold OMA.S_oeis_a388713.T
  apply congrArg Nat.card
  congr 1
  funext p
  apply propext
  have sorted : (OMA.S_oeis_a388713.parts n p).reverse.Pairwise (· ≤ ·) :=
    List.pairwise_reverse.mpr (Multiset.pairwise_sort _ _)
  rw [← NestedIntervals.choosable_iff _ sorted,NestedIntervals.choosable_reverse]

/-!
# Counting choices for superdiagonal partitions

The registered problem in OEIS A388713 asks when the positive initial intervals
of a partition admit distinct representatives. This file counts all such choices.
For any increasing family of finite sets, a partial matching using the first i
sets occupies exactly i elements of the next one. Multiplying the available
choices gives the Ferrers-board product. The ambient type may be infinite.

The sequence and the conjectured interpretation are due to Gus Wiseman.
Clément Garrot records the corresponding existence criterion in OEIS A387112.
Sources: https://oeis.org/A388713 and https://oeis.org/A387112.
-/

namespace NestedIntervals
open Finset
open scoped Classical

abbrev Systems {α : Type*} {k : ℕ} (S : Fin k → Finset α) :=
  {f : Fin k ↪ α // ∀ i, f i ∈ S i}

theorem count_systems {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (S : Fin k → Finset α) (ordered : Monotone S) :
    Fintype.card (Systems S) = ∏ i : Fin k, ((S i).card - i.val) := by
  classical
  induction k with
  | zero =>
    let _ : Unique (Systems S) := ⟨⟨⟨Function.Embedding.ofIsEmpty,fun i => Fin.elim0 i⟩⟩,
      fun f => Subtype.ext (Function.Embedding.ext (fun i => Fin.elim0 i))⟩
    simp
  | succ k ih =>
    let P := fun i : Fin k => S i.castSucc
    let restrict (x : Systems S) : Systems P :=
      ⟨Fin.Embedding.init x.val,fun i => x.property i.castSucc⟩
    have fiber (u : Systems P) :
        Fintype.card {x : Systems S // restrict x = u} = (S (Fin.last k)).card-k := by
      let taken := Finset.univ.map u.val
      let available := S (Fin.last k) \ taken
      have ht (v : α) : v ∈ taken ↔ v ∈ Set.range u.val := by simp [taken,Set.mem_range]
      have mono : taken ⊆ S (Fin.last k) := by
        intro v hv
        obtain ⟨i,rfl⟩ := (ht v).mp hv
        exact ordered (Fin.le_last i.castSucc) (u.property i)
      let extend (z : available) : Systems S :=
        ⟨Fin.Embedding.snoc u.val (a:=z.val) (fun hz => (mem_sdiff.mp z.property).2 ((ht _).mpr hz)),by
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa only [Fin.Embedding.snoc_last] using (mem_sdiff.mp z.property).1
          · simpa only [Fin.Embedding.snoc_castSucc] using u.property j⟩
      have re (z : available) : restrict (extend z) = u :=
        Subtype.ext (Fin.Embedding.init_snoc u.val (a:=z.val) (fun hz => (mem_sdiff.mp z.property).2 ((ht _).mpr hz)))
      have atLast (z : available) : (extend z).val (Fin.last k) = z.val := by
        simp only [extend,Fin.Embedding.snoc_last]
      have atOther (z : available) (j : Fin k) : (extend z).val j.castSucc = u.val j := by
        simp only [extend,Fin.Embedding.snoc_castSucc]
      let lastOf (x : {x : Systems S // restrict x = u}) : available :=
        ⟨x.val.val (Fin.last k),by
          apply mem_sdiff.mpr
          refine ⟨x.val.property _,?_⟩
          intro occurs
          obtain ⟨j,hj⟩ := (ht _).mp occurs
          have eq : x.val.val j.castSucc = u.val j :=
            congrArg (fun y : Systems P => y.val j) x.property
          have conflict := x.val.val.injective (eq.trans hj)
          exact (Fin.castSucc_lt_last j).ne conflict⟩
      let e : {x : Systems S // restrict x = u} ≃ available :=
        { toFun := lastOf
          invFun := fun z => ⟨extend z,re z⟩
          left_inv := by
            intro x
            apply Subtype.ext
            apply Subtype.ext
            apply Function.Embedding.ext
            intro i
            refine Fin.lastCases ?_ (fun j => ?_) i
            · exact atLast (lastOf x)
            · change (extend (lastOf x)).val j.castSucc = _
              rw [atOther]
              exact (congrArg (fun y : Systems P => y.val j) x.property).symm
          right_inv := fun z => Subtype.ext (atLast z) }
      rw [Fintype.card_congr e]
      change Fintype.card ↥(S (Fin.last k) \ taken) = _
      rw [Fintype.card_coe,card_sdiff_of_subset mono]
      simp [taken]
    have e := Fintype.card_congr (Equiv.sigmaFiberEquiv restrict).symm
    rw [Fintype.card_sigma] at e
    simp only [fiber,Finset.sum_const,Finset.card_univ,smul_eq_mul] at e
    rw [e,ih P (fun _ _ h => ordered (Fin.castSucc_le_castSucc_iff.mpr h)),Fin.prod_univ_castSucc]
    rfl

end NestedIntervals

namespace NestedIntervals
open Finset
open scoped Classical

/-- The ambient type may be infinite, since the representatives all lie in a finite union. -/
theorem count_finite_systems {α : Type*} [DecidableEq α] {k : ℕ}
    (S : Fin k → Finset α) (ordered : Monotone S) :
    Nat.card (Systems S) = ∏ i : Fin k, ((S i).card - i.val) := by
  classical
  let U := univ.biUnion S
  have incl (i : Fin k) {x : α} (hx : x ∈ S i) : x ∈ U := mem_biUnion.mpr ⟨i,mem_univ _,hx⟩
  let A := fun i => univ.filter (fun x : U => x.val ∈ S i)
  have mon : Monotone A := by
    intro i j ij x hx
    exact mem_filter.mpr ⟨mem_univ _,ordered ij (mem_filter.mp hx).2⟩
  have sizes (i : Fin k) : (A i).card = (S i).card := by
    exact card_bij' (s:=A i) (t:=S i)
      (fun x _ => x.val) (fun x hx => (⟨x,incl i hx⟩ : U))
      (fun x hx => (mem_filter.mp hx).2)
      (fun x hx => mem_filter.mpr ⟨mem_univ _,hx⟩)
      (fun _ _ => rfl) (fun _ _ => rfl)
  let e : Systems S ≃ Systems A :=
    { toFun := fun u => ⟨⟨fun i => ⟨u.val i,incl i (u.property i)⟩,
          fun _ _ h => u.val.injective (congrArg Subtype.val h)⟩,
        fun i => mem_filter.mpr ⟨mem_univ _,u.property i⟩⟩
      invFun := fun u => ⟨u.val.trans (Function.Embedding.subtype _),
          fun i => (mem_filter.mp (u.property i)).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,count_systems A mon]
  simp only [sizes]

/-- The number of actual positive integer choices for a weakly increasing list of row lengths. -/
theorem representatives_product (y : List ℕ) (ordered : y.Pairwise (· ≤ ·)) :
    Nat.card {f : Fin y.length ↪ ℕ // ∀ i, 1 ≤ f i ∧ f i ≤ y.get i} =
      ∏ i : Fin y.length, (y.get i - i.val) := by
  let S := fun i : Fin y.length => Icc 1 (y.get i)
  have mon : Monotone S := fun _ _ h _ hx =>
    mem_Icc.mpr ⟨(mem_Icc.mp hx).1,(mem_Icc.mp hx).2.trans (ordered.rel_get_of_le h)⟩
  have same : {f : Fin y.length ↪ ℕ // ∀ i, 1 ≤ f i ∧ f i ≤ y.get i} ≃ Systems S :=
    { toFun := fun f => ⟨f.val,fun i => mem_Icc.mpr (f.property i)⟩
      invFun := fun f => ⟨f.val,fun i => mem_Icc.mp (f.property i)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr same,count_finite_systems S mon]
  simp [S]

end NestedIntervals

namespace NestedIntervals
open OMA.S_oeis_a388713

/-- Count the one-based systems of distinct representatives for the actual partition,
whose parts the source lists in decreasing order. -/
theorem partition_representatives {n : ℕ} (p : Nat.Partition n) :
    let y := parts n p
    Nat.card {f : Fin y.length ↪ ℕ // ∀ i, 1 ≤ f i ∧ f i ≤ y.get i} =
      ∏ i : Fin y.reverse.length, (y.reverse.get i - i.val) := by
  dsimp only
  let y := parts n p
  let e : Fin y.reverse.length ≃ Fin y.length := (finCongr y.length_reverse).trans Fin.revPerm
  have h (i : Fin y.reverse.length) : y.reverse.get i = y.get (e i) := by
    simp [List.get_eq_getElem,e,Fin.rev,Nat.sub_sub,Nat.add_comm]
  let fwd (z : {f : Fin y.length ↪ ℕ // ∀ i, 1 ≤ f i ∧ f i ≤ y.get i}) :
      {f : Fin y.reverse.length ↪ ℕ // ∀ i, 1 ≤ f i ∧ f i ≤ y.reverse.get i} :=
    ⟨e.toEmbedding.trans z.val,fun i => by rw [h]; exact z.property (e i)⟩
  let back (z : {f : Fin y.reverse.length ↪ ℕ // ∀ i, 1 ≤ f i ∧ f i ≤ y.reverse.get i}) :
      {f : Fin y.length ↪ ℕ // ∀ i, 1 ≤ f i ∧ f i ≤ y.get i} :=
    ⟨e.symm.toEmbedding.trans z.val,fun i => by
      have v := z.property (e.symm i); rw [h,e.apply_symm_apply] at v; exact v⟩
  let bridge : _ ≃ _ := { toFun := fwd, invFun := back
                          left_inv := fun z => Subtype.ext (Function.Embedding.ext (fun i => congrArg z.val (e.apply_symm_apply i)))
                          right_inv := fun z => Subtype.ext (Function.Embedding.ext (fun i => congrArg z.val (e.symm_apply_apply i))) }
  exact (Nat.card_congr bridge).trans
    (representatives_product y.reverse (List.pairwise_reverse.mpr (Multiset.pairwise_sort _ _)))

end NestedIntervals

/-! The registered statement is due to @esracummings31-blip.
Gus Wiseman's OEIS A388713 links the number of zero entries in each row to A003059.
The construction below takes full parts of size k and an optional positive remainder. -/

namespace SuperdiagonalRows
open OMA.S_oeis_a388713

private theorem has_partition (n k : ℕ) :
    0 < T n k ↔ ∃ p : Nat.Partition n,
      p.parts ≠ 0 ∧ p.parts.sup = k ∧ Superdiagonal (parts n p).reverse := by
  rw [T,Nat.card_pos_iff]
  exact ⟨fun ⟨⟨⟨p,h⟩⟩,_⟩ => ⟨p,h⟩,fun ⟨p,h⟩ => ⟨⟨⟨p,h⟩⟩,inferInstance⟩⟩

private theorem bounds {n k : ℕ} (p : Nat.Partition n) (nonempty : p.parts ≠ 0)
    (maximum : p.parts.sup = k) (diag : Superdiagonal (parts n p).reverse) :
    0 < k ∧ k ≤ n ∧ n ≤ k*k := by
  have upper {x} (mem : x ∈ p.parts) : x ≤ k := maximum ▸ Multiset.le_sup mem
  obtain ⟨x,hx⟩ := Multiset.exists_mem_of_ne_zero nonempty
  have size : (parts n p).reverse.length = p.parts.card := by simp [parts]
  have len : p.parts.card ≤ k := by
    by_contra! h
    let i : Fin (parts n p).reverse.length := ⟨k, by omega⟩
    have low := diag i
    have mem : (parts n p).reverse.get i ∈ p.parts := by
      simpa [parts] using (List.get_mem (parts n p).reverse i)
    have high := upper mem
    change k+1 ≤ _ at low
    omega
  refine ⟨(p.parts_pos hx).trans_le (upper hx),?_,?_⟩
  · rw [←maximum]
    exact Multiset.sup_le.mpr (fun _ hi => p.le_of_mem_parts hi)
  · calc n = p.parts.sum := p.parts_sum.symm
         _ ≤ p.parts.card * k := by
           simpa using Multiset.sum_le_card_nsmul p.parts k fun a h => upper h
         _ ≤ k*k := Nat.mul_le_mul_right k len

private theorem of_list {n k : ℕ} (y : List ℕ) (sum : y.sum=n)
    (pos : ∀x∈y, 0<x) (largest : k ∈ y) (bound : ∀x∈y,x≤k)
    (ordered : y.Pairwise (· ≤ ·)) (diag : Superdiagonal y) : 0<T n k := by
  let p : Nat.Partition n :=
    ⟨(y.reverse : List ℕ), fun h => pos _ (by simpa using h),by simpa using sum⟩
  have hk : k∈p.parts := by simpa [p] using largest
  have rev : parts n p = y.reverse := by
    change (↑y.reverse : Multiset ℕ).sort (· ≥ ·) = y.reverse
    rw [Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simpa [List.pairwise_reverse] using ordered
  refine (has_partition n k).mpr ⟨p,fun eq => ?_,le_antisymm ?_ (Multiset.le_sup hk),?_⟩
  · simp [eq] at hk
  · exact Multiset.sup_le.mpr fun a ha => bound a (by simpa [p] using ha)
  · simpa [rev] using diag

private theorem construct {n k : ℕ} (hk : 0<k) (lo : k≤n) (hi : n≤k*k) : 0<T n k := by
  let q := n/k
  let r := n%k
  have qpos : 0<q := Nat.div_pos lo hk
  have rem_lt : r<k := Nat.mod_lt _ hk
  have total : r+q*k=n := Nat.mod_add_div' n k
  have lim : q ≤ k := by
    by_contra! large
    have := Nat.mul_lt_mul_of_pos_right large hk
    omega
  have diag_rep {q : ℕ} (bound : q≤k) : Superdiagonal (List.replicate q k) := by
    intro i
    have hlen : i.val < q := by simpa using i.isLt
    simp only [List.get_eq_getElem,List.getElem_replicate]
    omega
  by_cases h : r=0
  · apply of_list (List.replicate q k)
    · simpa [List.sum_replicate,smul_eq_mul,h] using total
    · simpa [List.mem_replicate,qpos.ne'] using hk
    · simp [List.mem_replicate,qpos.ne']
    · simp [List.mem_replicate]
    · simp
    · exact diag_rep lim
  · have fewer : q<k := by
      by_contra! le
      have eq : q=k := by omega
      rw [eq] at total
      omega
    apply of_list (r :: List.replicate q k)
    · simpa [List.sum_replicate,smul_eq_mul] using total
    · intro x hx
      simp only [List.mem_cons,List.mem_replicate] at hx
      rcases hx with rfl|⟨_,rfl⟩
      · omega
      · exact hk
    · simp [List.mem_replicate,qpos.ne']
    · intro x hx
      simp only [List.mem_cons,List.mem_replicate] at hx
      rcases hx with rfl|⟨_,rfl⟩
      · omega
      · omega
    · simp [List.pairwise_cons,List.mem_replicate,rem_lt.le]
    · intro i
      cases e : i.val with
      | zero =>
        simp [List.get_eq_getElem,e]
        omega
      | succ j =>
        have hj : j<q := by have := i.isLt; simp at this; omega
        simp [List.get_eq_getElem,e]
        omega

theorem support (n k : ℕ) : 0<T n k ↔ 0<k ∧ k≤n ∧ n≤k*k := by
  constructor
  · intro h
    obtain ⟨p,ne,max,diag⟩ := (has_partition n k).mp h
    exact bounds p ne max diag
  · rintro ⟨hk,lo,hi⟩
    exact construct hk lo hi

@[simp] theorem zero_column (n : ℕ) : T n 0 = 0 := by
  have := (support n 0).mp
  omega
end SuperdiagonalRows


namespace SuperdiagonalRows
open OMA.S_oeis_a388713

/-- For positive n the initial zero segment ends at floor(sqrt(n-1)).
For n=0 the only entry of the registered triangle is zero. -/
theorem zero_positions (n : ℕ) :
    (Finset.range (n+1)).filter (fun k => T n k = 0) = Finset.range ((n-1).sqrt+1) := by
  classical
  ext k
  by_cases hn : n=0
  · subst n
    by_cases hk : k=0 <;> simp [hk]
  have cap : (n-1).sqrt ≤ n := le_trans (Nat.sqrt_le_self _) (Nat.sub_le _ _)
  have square : k ≤ (n-1).sqrt ↔ k*k < n := by rw [Nat.le_sqrt]; omega
  have eq : T n k = 0 ↔ ¬ (0<k ∧ k≤n ∧ n≤k*k) := by rw [←support]; omega
  simp only [Finset.mem_filter,Finset.mem_range,eq]
  by_cases hk : k=0
  · subst k
    simp
  · omega

theorem num_zeros (n : ℕ) :
    ((Finset.range (n+1)).filter (fun k => T n k = 0)).card = (n-1).sqrt+1 := by
  rw [zero_positions,Finset.card_range]

/-- On every positive row this is the ceiling square root of n, characterized
by its order property without using a real-valued square root. -/
theorem zero_count_le_iff {n d : ℕ} (hn : 0 < n) :
    ((Finset.range (n+1)).filter (fun k => T n k = 0)).card ≤ d ↔ n ≤ d*d := by
  rw [num_zeros,Nat.succ_le_iff,Nat.sqrt_lt]
  omega

/-- Gus Wiseman's A003059 observation for the positive rows, as a real ceiling. -/
theorem num_zeros_ceil_sqrt {n : ℕ} (hn : 0<n) :
    ((Finset.range (n+1)).filter (fun k => T n k=0)).card = ⌈Real.sqrt (n : ℝ)⌉₊ := by
  have ceiling (d : ℕ) : ⌈Real.sqrt (n : ℝ)⌉₊ ≤ d ↔ n ≤ d*d := by
    rw [Nat.ceil_le,Real.sqrt_le_iff]
    simp only [Nat.cast_nonneg,true_and,pow_two]
    exact_mod_cast Iff.rfl
  exact le_antisymm ((zero_count_le_iff hn).mpr ((ceiling _).mp le_rfl))
    ((ceiling _).mpr ((zero_count_le_iff hn).mp le_rfl))

end SuperdiagonalRows

namespace A388Ballot

/-- Nondecreasing parts with ceiling k and the required staircase below them. -/
abbrev Bounded (k l : ℕ) := {y : Fin l → ℕ // Monotone y ∧ ∀ i, i.val+1 ≤ y i ∧ y i ≤ k}

instance (k l : ℕ) : Finite (Bounded k l) := by
  let f (y : Bounded k l) (i : Fin l) : Fin (k+1) := ⟨y.1 i, Nat.lt_succ_of_le (y.2.2 i).2⟩
  apply Finite.of_injective f
  intro x y h
  exact Subtype.ext (funext (fun i => congrArg Fin.val (congrFun h i)))

private def raise {k l} (y : Bounded k l) : Bounded (k+1) l :=
  ⟨y.1, y.2.1, fun i => ⟨(y.2.2 i).1, (y.2.2 i).2.trans (by omega)⟩⟩

private def lower {k l} (y : Bounded (k+1) (l+1)) (h : y.1 (Fin.last l) ≤ k) : Bounded k (l+1) :=
  ⟨y.1, y.2.1, fun i => ⟨(y.2.2 i).1, (y.2.1 (Fin.le_last i)).trans h⟩⟩

private def drop {k l} (y : Bounded k (l+1)) : Bounded k l :=
  ⟨fun i => y.1 i.castSucc, fun _ _ h => y.2.1 (by simpa), fun i => y.2.2 i.castSucc⟩

private def append {k l} (y : Bounded (k+1) l) (hl : l ≤ k) : Bounded (k+1) (l+1) := by
  refine ⟨Fin.snoc y.1 (k+1), ?_, ?_⟩
  · intro a b hab
    induction b using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last]
      induction a using Fin.lastCases with
      | last => simp
      | cast i => simpa using (y.2.2 i).2
    | cast j =>
      induction a using Fin.lastCases with
      | last => exact ((Fin.not_le.mpr j.castSucc_lt_last) hab).elim
      | cast i => simpa using y.2.1 (show i ≤ j from hab)
  · intro i
    induction i using Fin.lastCases with
    | last => simpa using hl
    | cast j => simpa using y.2.2 j

def split {k l} (hl : l ≤ k) :
    Bounded (k+1) (l+1) ≃ Bounded k (l+1) ⊕ Bounded (k+1) l where
  toFun y := if h : y.1 (Fin.last l) ≤ k then .inl (lower y h) else .inr (drop y)
  invFun := Sum.elim raise (fun y => append y hl)
  left_inv y := by
    dsimp only
    split_ifs with h
    · rfl
    · apply Subtype.ext
      funext j
      induction j using Fin.lastCases with
      | last =>
        have bound := (y.2.2 (Fin.last l)).2
        change Fin.snoc (α := fun _ => ℕ) _ (k+1) (Fin.last l) = _
        rw [Fin.snoc_last]
        omega
      | cast i =>
        change Fin.snoc (α := fun _ => ℕ) _ (k+1) i.castSucc = _
        rw [Fin.snoc_castSucc]
        rfl
  right_inv y := by
    cases y with
    | inl a =>
      dsimp only
      split_ifs with h
      · rfl
      · exact (h ((a.2.2 (Fin.last l)).2)).elim
    | inr a =>
      dsimp only
      split_ifs with h
      · change Fin.snoc (α:=fun _ => ℕ) a.1 (k+1) (Fin.last l) ≤ k at h
        rw [Fin.snoc_last] at h
        omega
      · apply congrArg Sum.inr
        apply Subtype.ext
        funext i
        change Fin.snoc (α:=fun _ => ℕ) a.1 (k+1) i.castSucc = a.1 i
        rw [Fin.snoc_castSucc]

theorem split_area_inl {k l : ℕ} (hl : l ≤ k) (a : Bounded k (l+1)) :
    (∑ i, ((split hl).symm (.inl a)).1 i) = ∑ i, a.1 i := rfl

theorem split_area_inr {k l : ℕ} (hl : l ≤ k) (a : Bounded (k+1) l) :
    (∑ i, ((split hl).symm (.inr a)).1 i) = (∑ i, a.1 i)+(k+1) := by
  change (∑ i, Fin.snoc (α:=fun _ => ℕ) a.1 (k+1) i) = _
  rw [Fin.sum_univ_castSucc]
  simp

noncomputable def T (k l : ℕ) := Nat.card (Bounded k l)

theorem recurrence {k l : ℕ} (hl : l ≤ k) : T (k+1) (l+1) = T k (l+1) + T (k+1) l :=
  (Nat.card_congr (split hl)).trans Nat.card_sum

theorem empty (k : ℕ) : T k 0 = 1 := by
  have : Unique (Bounded k 0) := { default := ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩,
                                   uniq := fun _ => Subtype.ext (funext fun i => i.elim0) }
  exact Nat.card_unique

theorem outside (k l : ℕ) (h : k < l) : T k l = 0 := by
  have : IsEmpty (Bounded k l) := ⟨fun y => by have := y.2.2 ⟨k,h⟩; dsimp at this; omega⟩
  exact Nat.card_of_isEmpty

end A388Ballot

namespace A388Ballot
open Finset

/-- The ballot number in additive form, including the first out-of-range diagonal. -/
theorem ballot_add (k l : ℕ) (hl : l ≤ k+1) :
    T k l + (k+l).choose (k+1) = (k+l).choose l := by
  induction k generalizing l with
  | zero =>
    interval_cases l <;> simp [empty, outside, Nat.choose]
  | succ k ih =>
    induction l with
    | zero => simp [empty]
    | succ l inner =>
      by_cases beyond : k+1 < l+1
      · have h : l = k+1 := by omega
        subst l
        rw [outside _ _ (by omega), zero_add]
      · have sub := ih (l+1) (by omega)
        have prior := inner (by omega)
        have top : k+1+(l+1)=(k+l+1)+1 := by omega
        rw [recurrence (by omega), top, Nat.choose_succ_succ (k+l+1) (k+1), Nat.choose_succ_succ (k+l+1) l]
        simp only [show k+(l+1)=k+l+1 by omega] at sub
        simp only [show k+1+l=k+l+1 by omega] at prior
        rw [add_add_add_comm, sub, prior, add_comm]

theorem ballot_formula {k l : ℕ} (hl : l ≤ k+1) :
    T k l = (k+l).choose l - (k+l).choose (k+1) := by have := ballot_add k l hl; omega

theorem diagonal (k : ℕ) : T k k = catalan k := by
  have b := ballot_add k k (by omega)
  have choose := Nat.choose_succ_right_eq (2*k) k
  have cent := succ_mul_catalan_eq_centralBinom k
  change (k+1)*catalan k = (2*k).choose k at cent
  rw [show k+k=2*k by omega] at b
  rw [show 2*k-k=k by omega] at choose
  nlinarith

/-- Summing over all allowed lengths gives the next Catalan number. -/
theorem across_lengths (k : ℕ) : (∑ l∈range (k+1), T k l) = catalan (k+1) := by
  have partial_sum (r : ℕ) (hr : r ≤ k+1) : (∑ l∈range (r+1), T k l) = T (k+1) r := by
    induction r with
    | zero => simp [empty]
    | succ r ih =>
      rw [sum_range_succ, ih (by omega), recurrence (by omega), add_comm]
  have h := partial_sum (k+1) (by omega)
  rw [sum_range_succ,outside k (k+1) (by omega), add_zero, diagonal] at h
  exact h

end A388Ballot

namespace A388Columns
open OMA.S_oeis_a388713

/-- Weakly increasing arrays with superdiagonal entries and attained maximum. -/
def MaxArray (k l : ℕ) :=
  {y : Fin l → ℕ // Monotone y ∧ (∀ i, i.val + 1 ≤ y i ∧ y i ≤ k) ∧ ∃ i, y i = k}

instance {k l : ℕ} : Finite (MaxArray k l) :=
  Finite.of_injective (fun y : MaxArray k l => fun i : Fin l =>
    (⟨y.1 i, Nat.lt_succ_of_le (y.2.2.1 i).2⟩ : Fin (k+1))) (by
      intro y z h
      exact Subtype.ext (funext fun i => congrArg Fin.val (congrFun h i)))

private abbrev PartFiber (n k : ℕ) :=
  {p : Nat.Partition n // p.parts ≠ 0 ∧ p.parts.sup = k ∧ Superdiagonal (parts n p).reverse}

private abbrev ColumnLists (k : ℕ) :=
  {L : List ℕ // L.Pairwise (· ≤ ·) ∧ Superdiagonal L ∧ (∀ a ∈ L, a ≤ k) ∧ k ∈ L}

private theorem sup_occurs (s : Multiset ℕ) (hne : s ≠ 0) : s.sup ∈ s := by
  induction s using Multiset.induction_on with
  | empty => contradiction
  | cons a s ih =>
    by_cases h : s = 0
    · subst s; simp
    · by_cases ha : a ≤ s.sup
      · rw [Multiset.sup_cons, sup_eq_right.mpr ha]
        exact Multiset.mem_cons_of_mem (ih h)
      · rw [Multiset.sup_cons, sup_eq_left.mpr (by omega)]
        exact Multiset.mem_cons_self _ _

private theorem size_bounds {k} (L : ColumnLists k) :
    L.1.length ≤ k ∧ L.1.sum ≤ k*k := by
  have hlen : L.1.length ≤ k := by
    by_contra! h
    let i : Fin L.1.length := ⟨k,h⟩
    have lo := L.2.2.1 i
    have hi := L.2.2.2.1 (L.1.get i) (List.get_mem _ _)
    change k+1 ≤ _ at lo
    omega
  refine ⟨hlen, le_trans ?_ (Nat.mul_le_mul_right k hlen)⟩
  have bound (s : List ℕ) (hs : ∀ a ∈ s, a ≤ k) : s.sum ≤ s.length*k := by
    induction s with
    | nil => simp
    | cons a s ih =>
      simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
      have h1 := hs a (by simp)
      have h2 := ih (fun x hx => hs x (by simp [hx]))
      omega
  exact bound _ L.2.2.2.1

private def fromPart {n k} (p : PartFiber n k) : ColumnLists k := by
  refine ⟨(parts n p.1).reverse, List.pairwise_reverse.mpr (Multiset.pairwise_sort _ _),
      p.2.2.2, ?_, ?_⟩
  · intro a ha
    have mem : a ∈ p.1.parts := by simpa [parts] using ha
    exact (Multiset.le_sup mem).trans_eq p.2.2.1
  · have mem := sup_occurs p.1.parts p.2.1
    simpa [parts, ← p.2.2.1] using mem

private theorem parts_recover {n k} (p : PartFiber n k) :
    ((fromPart p).1 : Multiset ℕ) = p.1.parts := by
  change ((parts n p.1).reverse : Multiset ℕ) = p.1.parts
  rw [Multiset.coe_reverse, parts, Multiset.sort_eq]

private noncomputable def partitionsEquiv (k : ℕ) :
    (Σ n : Fin (k*k+1), PartFiber n.val k) ≃ ColumnLists k :=
  Equiv.ofBijective (fun z => fromPart z.2) <| by
    constructor
    · rintro ⟨n,p⟩ ⟨m,q⟩ eq
      have same : p.1.parts = q.1.parts := (parts_recover p).symm.trans <|
        (congrArg (fun L : ColumnLists k => (L.1 : Multiset ℕ)) eq).trans (parts_recover q)
      have ix : n = m := Fin.ext (p.1.parts_sum.symm.trans ((congrArg Multiset.sum same).trans q.1.parts_sum))
      subst m
      have e : p=q := Subtype.ext (Nat.Partition.ext same)
      subst q
      rfl
    · intro L
      let n : Fin (k*k+1) := ⟨L.1.sum, Nat.lt_succ_of_le (size_bounds L).2⟩
      let p : Nat.Partition n.val := {
        parts := (L.1 : Multiset ℕ)
        parts_pos := by
          intro i hi
          obtain ⟨j, rfl⟩ := List.mem_iff_get.mp (Multiset.mem_coe.mp hi)
          exact (Nat.succ_pos _).trans_le (L.2.2.1 j)
        parts_sum := Multiset.sum_coe _ }
      have same : (parts n.val p).reverse = L.1 := by
        apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
        · exact List.pairwise_reverse.mpr <| Multiset.pairwise_sort _ _
        · exact L.2.1
        · apply Multiset.coe_eq_coe.mp
          rw [Multiset.coe_reverse, parts, Multiset.sort_eq]
      have kmem : k ∈ p.parts := Multiset.mem_coe.mpr L.2.2.2.2
      have su : p.parts.sup = k := le_antisymm
        (Multiset.sup_le.mpr fun x hx => L.2.2.2.1 x (Multiset.mem_coe.mp hx))
        (Multiset.le_sup kmem)
      have nz : p.parts ≠ 0 := by intro hz; simp [hz] at kmem
      exact ⟨⟨n, ⟨p,nz,su,same ▸ L.2.2.1⟩⟩, Subtype.ext same⟩

private def fromArray {k l} (a : MaxArray k l) : ColumnLists k := by
  refine ⟨List.ofFn a.1,List.pairwise_ofFn.mpr (fun _ _ h => a.2.1 h.le),?_,?_,?_⟩
  · intro j
    let j' : Fin l := ⟨j.val, by simpa using j.isLt⟩
    simpa [List.get_eq_getElem,j'] using (a.2.2.1 j').1
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact (a.2.2.1 i).2
  · exact List.mem_ofFn.mpr a.2.2.2

private noncomputable def arraysEquiv (k : ℕ) : (Σ l : Fin (k+1), MaxArray k l.val) ≃ ColumnLists k :=
  Equiv.ofBijective (fun z => fromArray z.2) <| by
    constructor
    · rintro ⟨l, a⟩ ⟨m, b⟩ eq
      have h : List.ofFn a.1 = List.ofFn b.1 := congrArg Subtype.val eq
      have ix : l=m := Fin.ext (by simpa using congrArg List.length h)
      subst m
      have e : a=b := Subtype.ext (List.ofFn_injective h)
      subst b
      rfl
    · intro L
      let l : Fin (k+1) := ⟨L.1.length, Nat.lt_succ_of_le (size_bounds L).1⟩
      let a : MaxArray k l.val :=
        ⟨L.1.get, (fun _ _ h => L.2.1.rel_get_of_le h),
          fun i => ⟨L.2.2.1 i,L.2.2.2.1 _ (List.get_mem _ _)⟩,
          List.mem_iff_get.mp L.2.2.2.2⟩
      exact ⟨⟨l,a⟩,Subtype.ext (List.ofFn_get L.1)⟩

/-- Reindex the actual partitions of bounded sum by their increasing arrays. -/
noncomputable def partition_array (k : ℕ) :
    (Σ n : Fin (k*k+1), {p : Nat.Partition n.val //
      p.parts ≠ 0 ∧ p.parts.sup = k ∧ Superdiagonal (parts n.val p).reverse}) ≃
      (Σ l : Fin (k+1), MaxArray k l.val) :=
  (partitionsEquiv k).trans (arraysEquiv k).symm

/-- The column equivalence keeps the entire multiset of parts. -/
theorem partition_array_parts (k : ℕ) (n : Fin (k*k+1)) (p : PartFiber n.val k) :
    ((List.ofFn ((partition_array k ⟨n,p⟩).2.1)) : Multiset ℕ) = p.1.parts := by
  let E := arraysEquiv k
  let x := fromPart p
  have h := E.apply_symm_apply x
  exact (congrArg (fun L : ColumnLists k => (L.1 : Multiset ℕ)) h).trans (parts_recover p)

/-- An actual entry above the square cutoff has no partitions. -/
theorem beyond_square {n k : ℕ} (h : k*k < n) : T n k = 0 := by
  have impossible (p : PartFiber n k) : False := by
    have hs := (size_bounds (fromPart p)).2
    have eq := (congrArg Multiset.sum (parts_recover p)).trans p.1.parts_sum
    simp only [Multiset.sum_coe] at eq
    omega
  let : IsEmpty (PartFiber n k) := ⟨impossible⟩
  exact Nat.card_of_isEmpty

/-- Count the same column by its integer sum or by its length. -/
theorem column_sum (k : ℕ) :
    (∑ n ∈ Finset.range (k*k+1), T n k) =
      ∑ l ∈ Finset.range (k+1), Nat.card (MaxArray k l) := by
  have h := Nat.card_congr ((partitionsEquiv k).trans (arraysEquiv k).symm)
  rw [← Fin.sum_univ_eq_sum_range (fun n => T n k),
    ← Fin.sum_univ_eq_sum_range (fun l => Nat.card (MaxArray k l))]
  simpa only [Nat.card_sigma, T, PartFiber] using h

end A388Columns

namespace A388Ballot
open Finset A388Columns

/-- Separate arrays according to whether their upper bound is attained. -/
private noncomputable def maxSplit (k l : ℕ) :
    Bounded (k+1) l ≃ MaxArray (k+1) l ⊕ Bounded k l := by
  classical
  let f : Bounded (k+1) l → MaxArray (k+1) l ⊕ Bounded k l := fun y =>
    if h : ∃ i, y.1 i=k+1 then Sum.inl ⟨y.1, y.2.1, y.2.2, h⟩
    else Sum.inr ⟨y.1,y.2.1,fun i => ⟨(y.2.2 i).1,
      Nat.le_of_lt_succ (lt_of_le_of_ne (y.2.2 i).2 (fun eq => h ⟨i,eq⟩))⟩⟩
  let g : MaxArray (k+1) l ⊕ Bounded k l → Bounded (k+1) l := Sum.elim
    (fun y => ⟨y.1,y.2.1,y.2.2.1⟩)
    (fun y => ⟨y.1,y.2.1,fun i => ⟨(y.2.2 i).1,(y.2.2 i).2.trans (by omega)⟩⟩)
  refine ⟨f,g,?_,?_⟩
  · intro y
    dsimp [f]
    split_ifs <;> rfl
  · rintro (y|y)
    · dsimp [f,g]
      split_ifs with h
      · rfl
      · exact (h y.2.2.2).elim
    · dsimp [f,g]
      split_ifs with h
      · obtain ⟨i,hi⟩ := h
        have le := (y.2.2 i).2
        omega
      · rfl

theorem max_card (k l : ℕ) :
    Nat.card (MaxArray (k+1) l)+T k l=T (k+1) l :=
  (Nat.card_congr (maxSplit k l) |>.trans Nat.card_sum).symm

theorem column_succ (k : ℕ) :
    (∑ n∈range ((k+1)*(k+1)+1), OMA.S_oeis_a388713.T n (k+1)) + catalan (k+1) = catalan (k+2) := by
  rw [column_sum]
  have shorter : (∑ l∈range (k+2), T k l)= catalan (k+1) := by
    rw [sum_range_succ,outside k (k+1) (by omega), add_zero, across_lengths]
  rw [← shorter, ← sum_add_distrib, ← across_lengths (k+1)]
  exact sum_congr rfl (fun i _ => max_card k i)

theorem column_total (k : ℕ) :
    (∑ n∈range (k*k+1), OMA.S_oeis_a388713.T n k) = catalan (k+1)-catalan k := by
  cases k with
  | zero =>
    rw [column_sum]
    have : IsEmpty (MaxArray 0 0) := ⟨fun y => by obtain ⟨i,_⟩ := y.2.2.2; exact i.elim0⟩
    simp [Nat.card_of_isEmpty]
  | succ k => exact Nat.eq_sub_of_add_eq (column_succ k)

end A388Ballot

namespace A388Columns
open Finset

private theorem staircase (r : ℕ) : (∑ i : Fin r, (i.val+1)) = (r+1).choose 2 := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,ih]
    calc
      _ = (r+1)+(r+1).choose 2 := Nat.add_comm _ _
      _ = _ := by simpa only [Nat.choose_one_right] using (Nat.choose_succ_succ (r+1) 1).symm

/-- Increase the rightmost part strictly below the maximum. This preserves all
constraints and raises the area by one until the entire rectangle is filled. -/
private theorem raise_area {k l : ℕ} (y : MaxArray k l) (lt : (∑ i, y.val i) < l*k) :
    ∃ z : MaxArray k l, (∑ i, z.val i) = (∑ i, y.val i)+1 := by
  classical
  let U := univ.filter (fun i : Fin l => y.val i < k)
  have ne : U.Nonempty := by
    by_contra! h
    have full (i : Fin l) : y.val i = k := by
      have miss : i ∉ U := by rw [h]; simp
      exact le_antisymm (y.property.2.1 i).2 (le_of_not_gt (fun hi => miss (mem_filter.mpr ⟨mem_univ _,hi⟩)))
    simp [full] at lt
  let j := U.max' ne
  have hj : y.val j < k := (mem_filter.mp (U.max'_mem ne)).2
  let g (i : Fin l) := y.val i + if i = j then 1 else 0
  have limits (i : Fin l) : i.val+1 ≤ g i ∧ g i ≤ k := by
    have lo := y.property.2.1 i
    by_cases eq : i=j
    · subst i
      simp [g]
      omega
    · simpa [g,eq] using lo
  have order : Monotone g := by
    intro a b ab
    by_cases e : a = j
    · subst a
      by_cases eb : b=j
      · simp [eb]
      have hb : k ≤ y.val b := le_of_not_gt (fun low => eb (le_antisymm
          (U.le_max' b (mem_filter.mpr ⟨mem_univ _,low⟩)) ab))
      simp [g,eb]
      omega
    · have h := y.property.1 ab
      simp only [g,if_neg e,add_zero]
      omega
  obtain ⟨i,hi⟩ := y.property.2.2
  have diff : i≠j := by rintro rfl; omega
  let z : MaxArray k l := ⟨g,order,limits,i,by simp [g,hi,diff]⟩
  refine ⟨z,?_⟩
  change (∑ i, (y.val i + if i=j then 1 else 0)) = _
  simp [sum_add_distrib]

/-- Exact attainable total for a fixed maximum and a fixed number of parts. -/
theorem fixed_area_iff (k l n : ℕ) :
    (∃ y : MaxArray k l, (∑ i, y.val i) = n) ↔
      0 < l ∧ l ≤ k ∧ k+l.choose 2 ≤ n ∧ n ≤ l*k := by
  classical
  cases l with
  | zero =>
    constructor
    · rintro ⟨y,_⟩
      obtain ⟨i,_⟩ := y.property.2.2
      exact Fin.elim0 i
    · simp
  | succ r =>
    constructor
    · rintro ⟨y,rfl⟩
      obtain ⟨a,ha⟩ := y.property.2.2
      have last : y.val (Fin.last r) = k := le_antisymm (y.property.2.1 _).2
        (ha.symm.trans_le (y.property.1 (Fin.le_last a)))
      have hlen := (y.property.2.1 (Fin.last r)).1
      change r+1 ≤ y.val (Fin.last r) at hlen
      refine ⟨by omega,by omega,?_,?_⟩
      · rw [Fin.sum_univ_castSucc,last,← staircase]
        have t := sum_le_sum (s:=univ) (fun (i : Fin r) _ => (y.property.2.1 i.castSucc).1)
        simpa [Nat.add_comm,Fin.val_castSucc] using Nat.add_le_add_right t k
      · calc
          _ ≤ ∑ _ : Fin (r+1), k := sum_le_sum fun i _ => (y.property.2.1 i).2
          _ = _ := by simp
    · rintro ⟨_,hlen,lo,hi⟩
      let b (i : Fin (r+1)) := if i=Fin.last r then k else i.val+1
      have limits (i : Fin (r+1)) : i.val+1 ≤ b i ∧ b i ≤ k := by
        by_cases e : i=Fin.last r
        · subst i; simpa [b] using hlen
        · have := i.isLt; simp [b,e]; omega
      have mon : Monotone b := by
        intro i j ij
        by_cases e : j=Fin.last r
        · subst j; simpa [b] using (limits i).2
        · have ne : i≠Fin.last r := fun hi => e (le_antisymm (Fin.le_last j) (hi ▸ ij))
          simp [b,e,ne]; exact ij
      let base : MaxArray k (r+1) := ⟨b,mon,limits,Fin.last r,by simp [b]⟩
      have sum0 : (∑ i, base.val i) = k+(r+1).choose 2 := by
        change (∑ i, b i) = _
        rw [Fin.sum_univ_castSucc]
        simp [b,Fin.castSucc_ne_last,staircase,Nat.add_comm]
      induction n,lo using Nat.le_induction with
      | base => exact ⟨base,sum0⟩
      | succ m hm ih =>
        obtain ⟨y,eq⟩ := ih (by omega)
        obtain ⟨z,hz⟩ := raise_area y (by omega)
        exact ⟨z,by omega⟩

end A388Columns

namespace A388Columns
open OMA.S_oeis_a388713

/-- Exact support, simultaneously by total, largest part, and number of parts,
for the partitions in the registered OEIS statement. -/
theorem partition_area_iff (k l n : ℕ) :
    (∃ p : Nat.Partition n, p.parts ≠ 0 ∧ p.parts.sup = k ∧ p.parts.card = l ∧
      Superdiagonal (parts n p).reverse) ↔
    0 < l ∧ l ≤ k ∧ k+l.choose 2 ≤ n ∧ n ≤ l*k := by
  rw [← fixed_area_iff]
  constructor
  · rintro ⟨p,nz,max,lc,diag⟩
    let L := (parts n p).reverse
    have size : L.length = l := by simpa [L,parts] using lc
    clear lc
    subst l
    have cmem (x : ℕ) : x ∈ L ↔ x ∈ p.parts := by simp [L,parts]
    have sorted : L.Pairwise (· ≤ ·) := List.pairwise_reverse.mpr (Multiset.pairwise_sort _ _)
    have bounds (i : Fin L.length) : i.val+1 ≤ L.get i ∧ L.get i ≤ k :=
      ⟨diag i,(Multiset.le_sup ((cmem _).mp (L.get_mem i))).trans_eq max⟩
    have ne : L ≠ [] := by
      intro e
      apply nz
      have zz : L.length = 0 := by simp [e]
      simpa [L,parts] using zz
    let j : Fin L.length := ⟨L.length-1,by have := List.length_pos_iff_ne_nil.mpr ne; omega⟩
    have full : L.get j = k := by
      refine le_antisymm (bounds j).2 (max ▸ Multiset.sup_le.mpr ?_)
      intro x hx
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ((cmem x).mpr hx)
      exact sorted.rel_get_of_le (by change i.val ≤ L.length-1; omega)
    let a : MaxArray k L.length := ⟨L.get,(fun _ _ h => sorted.rel_get_of_le h),bounds,j,full⟩
    refine ⟨a,?_⟩
    change ∑ i, L.get i = n
    rw [← List.sum_ofFn,List.ofFn_get]
    have same : (L : Multiset ℕ) = p.parts := by simp [L,parts]
    exact (congrArg Multiset.sum same).trans p.parts_sum
  · rintro ⟨a,area⟩
    let L := List.ofFn a.val
    have mono : L.Pairwise (· ≤ ·) := List.pairwise_ofFn.mpr (fun _ _ h => a.property.1 h.le)
    have total : L.sum = n := (List.sum_ofFn).trans area
    have bound (x : ℕ) (hx : x ∈ L) : 0 < x ∧ x ≤ k := by
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact ⟨(Nat.succ_pos _).trans_le (a.property.2.1 i).1,(a.property.2.1 i).2⟩
    let p : Nat.Partition n := ⟨(L.reverse : List ℕ),fun h => (bound _ (by simpa using h)).1,
          by simpa using total⟩
    have kmem : k ∈ p.parts := by
      simpa [p,L] using (List.mem_ofFn.mpr a.property.2.2 : k ∈ L)
    have sorted : parts n p = L.reverse := by
      change (↑L.reverse : Multiset ℕ).sort (· ≥ ·) = L.reverse
      rw [Multiset.coe_sort]
      apply List.mergeSort_of_pairwise
      simpa [List.pairwise_reverse] using mono
    refine ⟨p,fun z => by simp [z] at kmem,le_antisymm ?_ (Multiset.le_sup kmem),by simp [p,L],?_⟩
    · exact Multiset.sup_le.mpr (fun x h => (bound x (by simpa [p] using h)).2)
    · rw [sorted,List.reverse_reverse]
      intro i
      let j : Fin l := ⟨i.val,by simpa [L] using i.isLt⟩
      simpa [L,List.get_eq_getElem,j] using (a.property.2.1 j).1

end A388Columns

namespace A388Weights
open Finset A388Columns A388Ballot

def area {l : ℕ} (a : Fin l → ℕ) := ∑ i, a i

/-- The coefficient of weight n in the generating polynomial for bounded arrays. -/
noncomputable def B (k l n : ℕ) := Nat.card {y : Bounded k l // area y.1 = n}

/-- The same coefficient with the maximum required to occur. -/
noncomputable def M (k l n : ℕ) := Nat.card {y : MaxArray k l // area y.1 = n}

private def acrossLengths (k n : ℕ) :
    {z : (Σ l : Fin (k+1), MaxArray k l.val) // area z.2.1 = n} ≃
      (Σ l : Fin (k+1), {a : MaxArray k l.val // area a.1 = n}) where
  toFun z := ⟨z.1.1, z.1.2, z.2⟩
  invFun z := ⟨⟨z.1,z.2.1⟩,z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The coefficient-by-length sum recovers the registered entry, including n=0. -/
theorem original_coeff (n k : ℕ) :
    OMA.S_oeis_a388713.T n k = ∑ l ∈ range (k+1), M k l n := by
  classical
  by_cases small : n ≤ k*k
  · let t : Fin (k*k+1) := ⟨n,by omega⟩
    let e := partition_array k
    have conserve (z) : area (e z).2.1 = z.1.val := by
      have h := (congrArg Multiset.sum (partition_array_parts k z.1 z.2)).trans z.2.1.parts_sum
      simpa only [Multiset.sum_coe, List.sum_ofFn, area, e] using h
    let fiber := e.subtypeEquiv (p:=fun z => z.1=t) (q:=fun z => area z.2.1=n)
      (by intro z; rw [conserve]; exact Fin.ext_iff)
    let eq := (Equiv.sigmaSubtype t).symm.trans (fiber.trans (acrossLengths k n))
    have h := Nat.card_congr eq
    rw [←Fin.sum_univ_eq_sum_range (fun l => M k l n)]
    simpa only [Nat.card_sigma, M, OMA.S_oeis_a388713.T] using h
  · rw [beyond_square (by omega)]
    symm
    apply sum_eq_zero
    intro l hl
    have size : l ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hl)
    have empty : IsEmpty {a : MaxArray k l // area a.1 = n} := ⟨fun a => by
      have lim : area a.1.1 ≤ l*k := by
        calc
          area a.1.1 ≤ ∑ _ : Fin l, k := sum_le_sum fun i _ => (a.1.2.2.1 i).2
          _ = l*k := by simp
      have cap := (lim.trans (Nat.mul_le_mul_right k size))
      exact small (a.2 ▸ cap)⟩
    exact Nat.card_of_isEmpty

/-- Splitting at the last maximum raises the area by precisely k+1. -/
theorem recurrence_add {k l : ℕ} (hl : l ≤ k) (m : ℕ) :
    B (k+1) (l+1) (m+(k+1)) = B k (l+1) (m+(k+1)) + B (k+1) l m := by
  let n := m+(k+1)
  let pred : Bounded k (l+1) ⊕ Bounded (k+1) l → Prop :=
    Sum.elim (fun a => area a.1=n) (fun b => area b.1=m)
  let e := (A388Ballot.split hl).symm
  have aligned (z) : pred z ↔ area (e z).1 = n := by
    cases z with
    | inl a => exact (congrArg (· = n) (split_area_inl hl a)).symm.to_iff
    | inr b =>
      change area b.1=m ↔ (∑ i, ((A388Ballot.split hl).symm (.inr b)).1 i) = m+(k+1)
      rw [split_area_inr]
      exact Nat.add_left_inj.symm
  let eq := (e.subtypeEquiv (p:=pred) (q:=fun y => area y.1=n) aligned).symm.trans Equiv.subtypeSum
  exact (Nat.card_congr eq).trans Nat.card_sum

theorem recurrence_low {k l n : ℕ} (hl : l ≤ k) (low : n < k+1) :
    B (k+1) (l+1) n = B k (l+1) n := by
  let pred : Bounded k (l+1) ⊕ Bounded (k+1) l → Prop :=
    Sum.elim (fun a => area a.1=n) (fun _ => False)
  let e := (A388Ballot.split hl).symm
  have aligned (z) : pred z ↔ area (e z).1 = n := by
    cases z with
    | inl a => exact (congrArg (· = n) (split_area_inl hl a)).symm.to_iff
    | inr b =>
      change False ↔ (∑ i, ((A388Ballot.split hl).symm (.inr b)).1 i) = n
      rw [split_area_inr]
      constructor
      · rintro ⟨⟩
      · intro h
        exact (Nat.not_le_of_lt low) ((Nat.le_add_left _ _).trans_eq h)
  let eq := (e.subtypeEquiv (p:=pred) (q:=fun y => area y.1=n) aligned).symm.trans Equiv.subtypeSum
  have zero : Nat.card {b : Bounded (k+1) l // False} = 0 := by simp
  exact (Nat.card_congr eq).trans (Nat.card_sum.trans (by change _ + Nat.card {b : Bounded (k+1) l // False} = _; rw [zero,Nat.add_zero]; rfl))

theorem recurrence {k l : ℕ} (hl : l ≤ k) (n : ℕ) :
    B (k+1) (l+1) n = B k (l+1) n + if k+1 ≤ n then B (k+1) l (n-(k+1)) else 0 := by
  split_ifs with h
  · simpa only [Nat.sub_add_cancel h] using recurrence_add hl (n-(k+1))
  · simpa using recurrence_low hl (by omega : n < k+1)

private def exactMax {k l : ℕ} (hl : l ≤ k) :
    MaxArray (k+1) (l+1) ≃ Bounded (k+1) l where
  toFun a := ⟨fun i => a.1 i.castSucc, fun _ _ h => a.2.1 (by simpa), fun i => a.2.2.1 i.castSucc⟩
  invFun a :=
    let b := (A388Ballot.split hl).symm (Sum.inr a)
    ⟨b.1,b.2.1,b.2.2,Fin.last l, by
      change Fin.snoc (α:=fun _ => ℕ) a.1 (k+1) (Fin.last l) = k+1
      rw [Fin.snoc_last]⟩
  right_inv a := by
    apply Subtype.ext; funext i
    change Fin.snoc (α:=fun _ => ℕ) a.1 (k+1) i.castSucc = a.1 i
    rw [Fin.snoc_castSucc]
  left_inv a := by
    apply Subtype.ext; funext i
    induction i using Fin.lastCases with
    | cast i =>
      change Fin.snoc (α:=fun _ => ℕ) (fun j => a.1 j.castSucc) (k+1) i.castSucc = a.1 i.castSucc
      rw [Fin.snoc_castSucc]
    | last =>
      change Fin.snoc (α:=fun _ => ℕ) _ (k+1) (Fin.last l)=a.1 (Fin.last l)
      rw [Fin.snoc_last]
      obtain ⟨i,hi⟩ := a.2.2.2
      exact le_antisymm (hi.symm.trans_le (a.2.1 (Fin.le_last i))) (a.2.2.1 _).2

/-- Removing the last part from a nonempty exact-maximum array. -/
theorem maximum_add {k l : ℕ} (hl : l ≤ k) (m : ℕ) :
    M (k+1) (l+1) (m+(k+1)) = B (k+1) l m := by
  let e := (exactMax hl).symm
  have aligned (a) : area a.1=m ↔ area (e a).1=m+(k+1) := by
    change area a.1=m ↔ (∑ i, ((A388Ballot.split hl).symm (.inr a)).1 i)=m+(k+1)
    rw [split_area_inr]
    exact Nat.add_left_inj.symm
  exact (Nat.card_congr (e.subtypeEquiv (p:=fun a => area a.1=m)
    (q:=fun a => area a.1=m+(k+1)) aligned)).symm

theorem maximum_low {k l n : ℕ} (low : n<k+1) : M (k+1) (l+1) n=0 := by
  have empty : IsEmpty {a : MaxArray (k+1) (l+1) // area a.1=n} := ⟨fun a => by
    obtain ⟨i,hi⟩ := a.1.2.2.2
    have h : a.1.1 i ≤ area a.1.1 := Finset.single_le_sum (fun j _ => Nat.zero_le (a.1.1 j)) (Finset.mem_univ i)
    exact (Nat.not_le_of_lt low) ((hi ▸ h).trans_eq a.2)⟩
  exact Nat.card_of_isEmpty

theorem maximum {k l : ℕ} (hl : l ≤ k) (n : ℕ) :
    M (k+1) (l+1) n = if k+1 ≤ n then B (k+1) l (n-(k+1)) else 0 := by
  split_ifs with h
  · simpa only [Nat.sub_add_cancel h] using maximum_add hl (n-(k+1))
  · exact maximum_low (by omega)

theorem empty_length (k n : ℕ) : B k 0 n = if n=0 then 1 else 0 := by
  by_cases hn : n=0
  · subst n
    rw [if_pos rfl]
    let empty : Bounded k 0 := ⟨Fin.elim0,fun i => i.elim0,fun i => i.elim0⟩
    let : Unique {a : Bounded k 0 // area a.1=0} :=
      ⟨⟨⟨empty,by simp [area]⟩⟩,fun _ => Subtype.ext (Subtype.ext (funext fun i => i.elim0))⟩
    exact Nat.card_unique
  · rw [if_neg hn]
    let : IsEmpty {a : Bounded k 0 // area a.1=n} := ⟨fun a => hn (by simpa [area] using a.2.symm)⟩
    exact Nat.card_of_isEmpty

theorem outside (k l n : ℕ) (hl : k<l) : B k l n=0 := by
  let : IsEmpty {a : Bounded k l // area a.1=n} := ⟨fun a => by
    have h := a.1.2.2 ⟨k,hl⟩
    dsimp at h
    omega⟩
  exact Nat.card_of_isEmpty

theorem maximum_empty_length (k n : ℕ) : M k 0 n=0 := by
  let : IsEmpty {a : MaxArray k 0 // area a.1=n} := ⟨fun a => by
    obtain ⟨i,_⟩ := a.1.2.2.2
    exact i.elim0⟩
  exact Nat.card_of_isEmpty

/-- Every original column is the one-step area shift of the bounded-array counts. -/
theorem original_from_bounded (n k : ℕ) :
    OMA.S_oeis_a388713.T n (k+1) =
      if k+1 ≤ n then ∑ l ∈ range (k+1), B (k+1) l (n-(k+1)) else 0 := by
  rw [original_coeff, Finset.sum_range_succ', maximum_empty_length, Nat.add_zero]
  by_cases hn : k+1 ≤ n
  · rw [if_pos hn]
    exact sum_congr rfl (fun l hl => by rw [maximum (Nat.lt_succ_iff.mp (mem_range.mp hl)),if_pos hn])
  · rw [if_neg hn]
    exact sum_eq_zero fun _ _ => maximum_low (by omega)

end A388Weights

#print axioms NestedIntervals.count_systems
#print axioms NestedIntervals.count_finite_systems
#print axioms NestedIntervals.representatives_product
#print axioms NestedIntervals.partition_representatives
#print axioms SuperdiagonalRows.zero_positions
#print axioms SuperdiagonalRows.num_zeros
#print axioms SuperdiagonalRows.zero_count_le_iff
#print axioms SuperdiagonalRows.num_zeros_ceil_sqrt
#print axioms A388Ballot.recurrence
#print axioms A388Ballot.ballot_formula
#print axioms A388Ballot.across_lengths
#print axioms A388Columns.column_sum
#print axioms A388Ballot.column_total
#print axioms A388Columns.fixed_area_iff
#print axioms A388Columns.partition_area_iff
#print axioms A388Weights.original_coeff
#print axioms A388Weights.recurrence
#print axioms A388Weights.maximum
#print axioms A388Weights.original_from_bounded
#print axioms OMA.solution
