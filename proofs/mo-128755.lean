import OMAStatements.S_mo_128755
import Mathlib.Tactic

/-!
# Expected minimum Hamming distance between overlapping windows

This proves the signed even-subgraph formula from the statement formalized by
@LDJAI for MathOverflow question 128755. Expand the threshold indicator for
each window in Boolean characters. Averaging over the random words cancels
every edge set having a bit of odd degree. Summing the surviving terms over
thresholds gives the expected minimum.
-/

namespace Hamming
open Finset

def sign {α : Type*} [DecidableEq α] (x : Finset α) (i : α) : ℚ :=
  if i ∈ x then -1 else 1

def character {α : Type*} [DecidableEq α] (s x : Finset α) : ℚ :=
  ∏ i ∈ s, sign x i

theorem character_card {α : Type*} [DecidableEq α] (s x : Finset α) :
    character s x = (-1 : ℚ)^(s ∩ x).card := by
  simp [character, sign]

private theorem orthogonal {α : Type*} [Fintype α] [DecidableEq α] (x y : Finset α) :
    (∑ s : Finset α, character s x * character s y) =
      if x=y then (2:ℚ)^Fintype.card α else 0 := by
  classical
  simp only [character, ← prod_mul_distrib]
  have expn := prod_one_add (f := fun i => sign x i * sign y i) (univ : Finset α)
  rw [powerset_univ] at expn
  rw [← expn]
  by_cases h : x=y
  · subst y
    have term (i : α) : 1 + sign x i * sign x i = 2 := by
      by_cases hi : i ∈ x <;> simp [sign, hi] <;> norm_num
    simp [term]
  · rw [if_neg h]
    have hdiff : ∃ i, ¬ (i ∈ x ↔ i ∈ y) := by
      by_contra! hf
      exact h (Finset.ext hf)
    obtain ⟨i,hi⟩ := hdiff
    apply prod_eq_zero (mem_univ i)
    by_cases hx : i ∈ x <;> by_cases hy : i ∈ y <;> simp_all [sign]

theorem inversion {α : Type*} [Fintype α] [DecidableEq α] (F : Finset α → ℚ) (x : Finset α) :
    (∑ s : Finset α, character s x * ∑ y : Finset α, F y * character s y) =
      (2:ℚ)^Fintype.card α * F x := by
  classical
  simp_rw [mul_sum]
  rw [sum_comm]
  calc
    _ = ∑ y, F y * ∑ s, character s x * character s y := by
      simp_rw [mul_sum]
      exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    _ = _ := by simp [orthogonal, mul_comm]

theorem window_indicator (n r : ℕ)
    (tail : ∀ s : Finset (Fin n),
      (∑ y : Finset (Fin n), if r ≤ y.card then (-1:ℚ)^(s ∩ y).card else 0) =
        OMA.S_mo_128755.signedTail n r s.card) (x : Finset (Fin n)) :
    (∑ s : Finset (Fin n), character s x * OMA.S_mo_128755.signedTail n r s.card) =
      (2:ℚ)^n * (if r ≤ x.card then 1 else 0) := by
  classical
  simpa [character_card, ← tail, ite_mul] using
    inversion (fun y : Finset (Fin n) => if r ≤ y.card then 1 else 0) x
end Hamming

namespace HammingTail
open Finset OMA.S_mo_128755
variable {α : Type*} [DecidableEq α]

/-- Split the subsets of a disjoint union into independently chosen subsets. -/
private lemma disjoint_sum (a b : Finset α) (hd : Disjoint a b) (f : Finset α → ℚ) :
    ∑ u ∈ (a ∪ b).powerset, f u = ∑ x ∈ a.powerset, ∑ y ∈ b.powerset, f (x ∪ y) := by
  induction a using Finset.induction_on generalizing f with
  | empty => simp
  | @insert z a hz ih =>
    have ha : Disjoint a b := hd.mono_left (subset_insert _ _)
    have hb : z ∉ b := disjoint_left.mp hd (mem_insert_self _ _)
    rw [insert_union, sum_powerset_insert (by simp [hz,hb]), sum_powerset_insert hz,
      ih ha, ih ha]
    simp [insert_union]

omit [DecidableEq α] in
private lemma bins (s : Finset α) (J : Finset ℕ) (g : ℕ → ℚ) :
    (∑ u ∈ s.powerset, if u.card ∈ J then g u.card else 0) =
      ∑ j ∈ J, (s.card.choose j : ℚ) * g j := by
  calc
    _ = ∑ u ∈ s.powerset, ∑ j ∈ J, if u.card = j then g j else 0 := by simp
    _ = ∑ j ∈ J, ∑ u ∈ s.powerset, if u.card = j then g j else 0 := sum_comm
    _ = _ := by
      refine sum_congr rfl fun j _ => ?_
      rw [← sum_filter, ← powersetCard_eq_filter, sum_const, card_powersetCard, nsmul_eq_mul]

private lemma split_sizes [Fintype α] (s : Finset α) (g : ℕ → ℕ → ℚ) :
    (∑ y : Finset α, g (s∩y).card y.card) =
      ∑ u ∈ s.powerset, ∑ v ∈ (univ \ s).powerset, g u.card (u.card+v.card) := by
  let b : Finset α := univ \ s
  have hd : Disjoint s b := disjoint_sdiff_self_right
  have allU : s ∪ b = univ := by ext z; simp [b]
  calc
    _ = ∑ y ∈ (s ∪ b).powerset, g (s∩y).card y.card := by rw [allU]; simp
    _ = _ := by
      rw [disjoint_sum s b hd]
      refine sum_congr rfl fun u hu => sum_congr rfl fun v hv => ?_
      have us := mem_powerset.mp hu
      have vb : v ⊆ b := mem_powerset.mp hv
      have dv : Disjoint s v := hd.mono_right vb
      have du : Disjoint u v := dv.mono_left us
      have I : s ∩ (u∪v) = u := by
        rw [inter_union_distrib_left, inter_eq_right.mpr us, disjoint_iff_inter_eq_empty.mp dv, union_empty]
      rw [I, card_union_of_disjoint du]

/-- A selected element pairs subsets with opposite signs.  Exactly the subsets of
size one less than the threshold survive. -/
theorem signed_tail {n r : ℕ} (s : Finset (Fin n)) (hr : r ∈ Finset.Icc 1 n) :
    (∑ y : Finset (Fin n), if r ≤ y.card then (-1:ℚ)^(s∩y).card else 0) =
      signedTail n r s.card := by
  classical
  rcases r with _ | d
  · simp at hr
  let b : Finset (Fin n) := univ \ s
  have hb : b.card = n-s.card := by simp [b,card_sdiff_of_subset]
  rw [split_sizes s (fun j m => if d+1 ≤ m then (-1:ℚ)^j else 0)]
  change (∑ u ∈ s.powerset, ∑ v ∈ b.powerset,
    if d+1 ≤ u.card+v.card then (-1:ℚ)^u.card else 0) = _
  by_cases empty : s = ∅
  · subst s
    simp only [powerset_empty, sum_singleton, card_empty, zero_add, pow_zero,
      signedTail, tsub_zero] at *
    have base := bins b (Icc (d+1) n) (fun _ => 1)
    calc
      _ = ∑ v ∈ b.powerset, if v.card ∈ Icc (d+1) n then (1:ℚ) else 0 := by
        refine sum_congr rfl fun v hv => ?_
        simp [Finset.mem_Icc, (card_le_card (mem_powerset.mp hv)).trans_eq hb]
      _ = _ := by simpa [hb] using base
  · obtain ⟨z,hz⟩ := nonempty_iff_ne_empty.mpr empty
    let t := s.erase z
    have ht : z ∉ t := notMem_erase z s
    have ti : insert z t = s := insert_erase hz
    have tc : t.card = s.card-1 := card_erase_of_mem hz
    have pos : s.card ≠ 0 := card_ne_zero.mpr (nonempty_iff_ne_empty.mpr empty)
    rw [signedTail, if_neg pos]
    conv_lhs => rw [← ti, sum_powerset_insert ht, ← sum_add_distrib]
    calc
      _ = ∑ u ∈ t.powerset, ∑ v ∈ b.powerset,
          if u.card + v.card = d then -(-1:ℚ)^u.card else 0 := by
        refine sum_congr rfl fun u hu => ?_
        have zu : z ∉ u := fun hz => ht (mem_powerset.mp hu hz)
        rw [← sum_add_distrib, card_insert_of_notMem zu, pow_succ]
        refine sum_congr rfl fun v _ => ?_
        split_ifs <;> first | omega | ring
      _ = ∑ u ∈ t.powerset, if u.card ∈ range (d+1) then
          -(-1:ℚ)^u.card * (b.card.choose (d-u.card) : ℚ) else 0 := by
        refine sum_congr rfl fun u _ => ?_
        by_cases le : u.card ≤ d
        · have eqsum (v : Finset (Fin n)) : u.card + v.card = d ↔ v.card=d-u.card := by omega
          simp only [eqsum, mem_range, Nat.lt_succ_iff, le, if_true]
          rw [← sum_filter, ← powersetCard_eq_filter, sum_const, card_powersetCard, nsmul_eq_mul, mul_comm]
        · simp [show ¬u.card < d+1 by omega, show ∀ v : Finset (Fin n), u.card+v.card ≠ d by omega]
      _ = _ := by
        rw [bins t (range (d+1)) (fun j => -(-1:ℚ)^j * (b.card.choose (d-j) : ℚ)), tc, hb,
          ← sum_neg_distrib]
        refine sum_congr rfl fun j _ => ?_
        simp only [Nat.add_sub_cancel]
        ring

end HammingTail

namespace Hamming
open Finset OMA.S_mo_128755

private def row {ι α : Type*} [Fintype α] [DecidableEq ι] [DecidableEq α]
    (e : Finset (ι × α)) (i : ι) : Finset α := univ.filter fun j => (i,j) ∈ e

private def edgeEquiv (ι α : Type*) [Fintype ι] [Fintype α] [DecidableEq ι] [DecidableEq α] :
    (ι → Finset α) ≃ Finset (ι × α) where
  toFun f := univ.filter fun ij => ij.2 ∈ f ij.1
  invFun := row
  left_inv f := by ext; simp [row]
  right_inv e := by ext; simp [row]

private theorem row_filter {ι α : Type*} [Fintype α] [DecidableEq ι] [DecidableEq α]
    (e : Finset (ι × α)) (i : ι) :
    (row e i).map (Function.Embedding.sectR i α) = e.filter (fun ij => ij.1=i) := by
  ext ⟨i',j⟩
  simp only [mem_map, row, mem_filter, mem_univ, true_and]
  change (∃ z, (i,z) ∈ e ∧ (i,z)=(i',j)) ↔ (i',j) ∈ e ∧ i'=i
  constructor
  · rintro ⟨z,hz,h⟩
    cases h
    exact ⟨hz,rfl⟩
  · rintro ⟨he,rfl⟩
    exact ⟨j,he,rfl⟩

def readBit {n k : ℕ} (b : Fin (n+k-1) → Bool) (i : Fin k) (j : Fin n) : Bool :=
  if h : i.val+j.val < n+k-1 then b ⟨i.val+j.val,h⟩ else false

private def mismatch {n k : ℕ} (a : Fin n → Bool) (b : Fin (n+k-1) → Bool)
    (i : Fin k) : Finset (Fin n) := univ.filter fun j => a j ≠ readBit b i j

def edgeSign {n k : ℕ} (a : Fin n → Bool) (b : Fin (n+k-1) → Bool)
    (ij : Fin k × Fin n) : ℚ := if a ij.2 = readBit b ij.1 ij.2 then 1 else -1

private theorem allSigns {n k : ℕ} (a : Fin n → Bool) (b : Fin (n+k-1) → Bool)
    (e : Finset (Fin k × Fin n)) :
    ∏ i, character (row e i) (mismatch a b i) = ∏ ij ∈ e, edgeSign a b ij := by
  rw [← prod_fiberwise e Prod.fst (edgeSign a b)]
  refine prod_congr rfl fun i _ => ?_
  rw [← row_filter, prod_map]
  unfold character
  refine prod_congr rfl fun j _ => ?_
  by_cases h : a j = readBit b i j <;> simp [mismatch, edgeSign, h, Hamming.sign]

theorem window_product (n k r : ℕ) (a : Fin n → Bool) (b : Fin (n+k-1) → Bool)
    (tail : ∀ s : Finset (Fin n),
      (∑ y : Finset (Fin n), if r ≤ y.card then (-1:ℚ)^(s ∩ y).card else 0) =
        signedTail n r s.card) :
    (2:ℚ)^(n*k) * (∏ i : Fin k, if r ≤ windowWeight a b i.val then (1:ℚ) else 0) =
      ∑ e : Finset (Fin k × Fin n), (∏ ij ∈ e, edgeSign a b ij) *
        ∏ i : Fin k, signedTail n r (e.filter (fun ij => ij.1=i)).card := by
  classical
  have recRow (i : Fin k) := (window_indicator n r tail (mismatch a b i)).symm
  have w : (2:ℚ)^(n*k) = ∏ _ : Fin k, (2:ℚ)^n := by simp [pow_mul]
  rw [w, ← prod_mul_distrib]
  change (∏ i : Fin k, (2:ℚ)^n * (if r ≤ (mismatch a b i).card then 1 else 0)) = _
  simp_rw [recRow]
  rw [Fintype.prod_sum]
  let eqv := edgeEquiv (Fin k) (Fin n)
  rw [← eqv.symm.sum_comp]
  refine sum_congr rfl fun e _ => ?_
  change (∏ i, character (row e i) (mismatch a b i) * signedTail n r (row e i).card) = _
  rw [prod_mul_distrib, allSigns]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  rw [← row_filter, card_map]
end Hamming

namespace Hamming
open Finset OMA.S_mo_128755

private def bitSign (v : Bool) : ℚ := if v then -1 else 1

private theorem bitSign_eq (v w : Bool) :
    (if v = w then (1 : ℚ) else -1) = bitSign v * bitSign w := by
  cases v <;> cases w <;> norm_num [bitSign]

private theorem bitMoment (d : ℕ) :
    (∑ v : Bool, bitSign v ^ d) = if d % 2 = 0 then (2 : ℚ) else 0 := by
  rw [Fintype.sum_bool]
  by_cases h : d % 2 = 0 <;> norm_num [bitSign, neg_one_pow_eq_ite, Nat.even_iff, h]

private theorem sumLabels {E V : Type*} [Fintype V] [DecidableEq V]
    (edges : Finset E) (label : E → V) :
    (∑ f : V → Bool, ∏ p ∈ edges, bitSign (f (label p))) =
      if ∀ v : V, (edges.filter (fun p => label p = v)).card % 2 = 0
      then (2 : ℚ)^Fintype.card V else 0 := by
  classical
  have regroup (f : V → Bool) :
      (∏ p ∈ edges, bitSign (f (label p))) =
        ∏ v, bitSign (f v) ^ (edges.filter (fun p => label p = v)).card := by
    simpa using (prod_fiberwise' edges label (fun v => bitSign (f v))).symm
  simp_rw [regroup]
  rw [← Fintype.prod_sum (fun v (b : Bool) => bitSign b ^ (edges.filter (fun p => label p = v)).card)]
  simp_rw [bitMoment]
  split_ifs with evenAll
  · simp [evenAll]
  · push Not at evenAll
    obtain ⟨v,hv⟩ := evenAll
    exact prod_eq_zero (mem_univ v) (if_neg hv)

theorem parity_sum (n k : ℕ) (hk : 0 < k) (e : Finset (Fin k × Fin n)) :
    (∑ a : Fin n → Bool, ∑ b : Fin (n + k - 1) → Bool, ∏ ij ∈ e,
      (if a ij.2 = (if h : ij.1.val + ij.2.val < n + k - 1
        then b ⟨ij.1.val + ij.2.val, h⟩ else false) then (1 : ℚ) else -1)) =
      if e ∈ evenEdgeSets n k then (2 : ℚ)^(n+(n+k-1)) else 0 := by
  classical
  let dest (p : Fin k × Fin n) : Fin (n+k-1) := ⟨p.1.val+p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩
  have edge (a : Fin n → Bool) (b : Fin (n+k-1) → Bool) (p : Fin k × Fin n) :
      (if a p.2 = (if h : p.1.val + p.2.val < n+k-1 then b ⟨_,h⟩ else false) then (1 : ℚ) else -1) =
        bitSign (a p.2) * bitSign (b (dest p)) := by
    rw [dif_pos (dest p).isLt]
    exact bitSign_eq _ _
  simp_rw [edge, prod_mul_distrib, ← mul_sum, ← sum_mul]
  rw [sumLabels e Prod.snd, sumLabels e dest]
  have same (p : Fin k × Fin n) (u : Fin (n+k-1)) : dest p = u ↔ p.1.val + p.2.val = u.val := Fin.ext_iff
  simp only [same, evenEdgeSets, mem_filter, mem_powerset, subset_univ, true_and,
    Fintype.card_fin, pow_add]
  split_ifs <;> simp_all

end Hamming

namespace Hamming
open Finset OMA.S_mo_128755

private lemma threshold_fold (f : ℕ → ℕ) (r : ℕ) (l : List ℕ) (initial : ℕ) :
    r ≤ l.foldl (fun u i => min u (f i)) initial ↔
      r ≤ initial ∧ ∀ i ∈ l, r ≤ f i := by
  induction l generalizing initial with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl_cons, ih, le_min_iff, List.forall_mem_cons, and_assoc]

/-- The minimum distance counts the positive threshold levels reached by every window. -/
theorem layers (n k : ℕ) (a : Fin n → Bool) (b : Fin (n+k-1) → Bool) :
    (minWindowWeight k a b : ℚ) = ∑ r ∈ Icc 1 n, ∏ i : Fin k,
      (if r ≤ windowWeight a b i.val then (1:ℚ) else 0) := by
  let m := minWindowWeight k a b
  have threshold (r : ℕ) : r ≤ m ↔ r ≤ n ∧ ∀ i : Fin k, r ≤ windowWeight a b i.val := by
    rw [show m = (List.range k).foldl (fun u i => min u (windowWeight a b i)) n from rfl,
      threshold_fold]
    simp only [List.mem_range]
    exact and_congr_right' ⟨fun h i => h i i.isLt, fun h i hi => h ⟨i,hi⟩⟩
  have bound : m ≤ n := ((threshold m).mp le_rfl).1
  have cut : (Icc 1 n).filter (· ≤ m) = Icc 1 m := by
    ext i
    simp only [mem_filter, mem_Icc]
    omega
  calc
    (m:ℚ) = ∑ r ∈ Icc 1 n, (if r ≤ m then (1:ℚ) else 0) := by
      rw [← sum_filter,cut]; simp
    _ = _ := by
      refine sum_congr rfl fun r hr => ?_
      by_cases h : r ≤ m
      · simp [h, ((threshold r).mp h).2]
      · have ex : ∃ i : Fin k, ¬ r ≤ windowWeight a b i.val := by
          by_contra! hall
          exact h ((threshold r).mpr ⟨(mem_Icc.mp hr).2,hall⟩)
        obtain ⟨i,hi⟩ := ex
        rw [if_neg h]
        exact (prod_eq_zero (mem_univ i) (if_neg hi)).symm

end Hamming

namespace Hamming
open Finset OMA.S_mo_128755

private theorem exchange {A B C : Type*} [Fintype A] [Fintype B]
    (S : Finset C) (f : A → B → C → ℚ) :
    (∑ a, ∑ b, ∑ c ∈ S, f a b c) = ∑ c ∈ S, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ a, ∑ c ∈ S, ∑ b, f a b c := sum_congr rfl fun _ _ => sum_comm
    _ = _ := sum_comm

theorem expected_formula (n k : ℕ)
    (layers : ∀ (a : Fin n → Bool) (b : Fin (n+k-1) → Bool),
      (minWindowWeight k a b : ℚ) = ∑ r ∈ Icc 1 n,
        ∏ i : Fin k, (if r ≤ windowWeight a b i.val then (1:ℚ) else 0))
    (parity : ∀ e : Finset (Fin k × Fin n),
      (∑ a : Fin n → Bool, ∑ b : Fin (n+k-1) → Bool, ∏ ij ∈ e, edgeSign a b ij) =
        if e ∈ evenEdgeSets n k then (2:ℚ)^(n+(n+k-1)) else 0) :
    expectedMin n k = exactFormula n k := by
  classical
  let T (r : ℕ) (a : Fin n → Bool) (b : Fin (n+k-1) → Bool) : ℚ :=
    ∏ i : Fin k, if r ≤ windowWeight a b i.val then 1 else 0
  let W (r : ℕ) (e : Finset (Fin k × Fin n)) : ℚ :=
    ∏ i : Fin k, signedTail n r (e.filter fun ij => ij.1=i).card
  let C : ℚ := 2^(n*k)
  let D : ℚ := 2^(n+(n+k-1))
  have perWindow (r : ℕ) (hr : r ∈ Icc 1 n) (a : Fin n → Bool) (b : Fin (n+k-1) → Bool) :
      C*T r a b = ∑ e : Finset (Fin k × Fin n), (∏ ij ∈ e, edgeSign a b ij) * W r e :=
    window_product n k r a b (fun s => HammingTail.signed_tail s hr)
  have perLevel (r : ℕ) (hr : r ∈ Icc 1 n) :
      (∑ a : Fin n → Bool, ∑ b : Fin (n+k-1) → Bool, C*T r a b) =
        D * ∑ e ∈ evenEdgeSets n k, W r e := by
    simp_rw [perWindow r hr]
    rw [exchange (univ : Finset (Finset (Fin k × Fin n)))]
    simp_rw [← sum_mul, parity]
    rw [mul_sum]
    simp [D, ite_mul]
  unfold expectedMin exactFormula
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  change (∑ a : Fin n → Bool, ∑ b : Fin (n+k-1) → Bool, (minWindowWeight k a b : ℚ))*C =
    (∑ r ∈ Icc 1 n, ∑ e ∈ evenEdgeSets n k, W r e)*D
  rw [mul_comm _ C, mul_comm _ D]
  simp_rw [layers]
  change C*(∑ a, ∑ b, ∑ r ∈ Icc 1 n, T r a b) = _
  rw [exchange (Icc 1 n), mul_sum, mul_sum]
  refine sum_congr rfl fun r hr => ?_
  conv_lhs => simp only [mul_sum]
  exact perLevel r hr

end Hamming

theorem OMA.solution : type_of% @OMA.S_mo_128755.main := by
  intro n k hk
  exact Hamming.expected_formula n k (Hamming.layers n k) (Hamming.parity_sum n k hk)
