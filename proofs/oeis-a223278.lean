import OMAStatements.S_oeis_a223278
import Mathlib.Tactic

/-!
# Width-four rolling icosahedron arrays

R. H. Hardin introduced the sequence; Colin Barker conjectured the two formulas.
The face labels and adjacency relation are those in the statement formalized by @jleguina.
We adapt the width-three finite-function row decomposition to four columns. Each row's
degree is 9, 15, or 21 according as zero, one, or both opposite pairs coincide. Summing
the degrees of its successors gives seventeen times its degree minus thirty-six.
-/

namespace IcoCounts
open Finset OMA.S_oeis_a223278
private abbrev Row := Fin 20 × Fin 20 × Fin 20 × Fin 20

/-- The three neighboring faces of each of the twenty triangles, in the article's numbering. -/
private def neighbors (i : Fin 20) : Finset (Fin 20) :=
  match i.val with
  | 0 => {1, 2, 5}
  | 1 => {0, 4, 6}
  | 2 => {0, 3, 8}
  | 3 => {2, 4, 10}
  | 4 => {1, 3, 12}
  | 5 => {0, 7, 9}
  | 6 => {1, 7, 14}
  | 7 => {5, 6, 16}
  | 8 => {2, 9, 11}
  | 9 => {5, 8, 15}
  | 10 => {3, 11, 13}
  | 11 => {8, 10, 17}
  | 12 => {4, 13, 14}
  | 13 => {10, 12, 18}
  | 14 => {6, 12, 19}
  | 15 => {9, 16, 17}
  | 16 => {7, 15, 19}
  | 17 => {11, 15, 18}
  | 18 => {13, 17, 19}
  | _ => {14, 16, 18}

private theorem neighbors_spec : ∀ x y : Fin 20, adj x y ↔ y ∈ neighbors x := by
  decide +kernel


/-- Degree determined by the two horizontal backtracking tests. -/
def score (r : Fin 20 × Fin 20 × Fin 20 × Fin 20) : ℕ :=
  9 + (if r.1 = r.2.2.1 then 6 else 0) + (if r.2.1 = r.2.2.2 then 6 else 0)

private def box (r : Row) : Finset Row :=
  neighbors r.2.1 ×ˢ (neighbors r.1 ×ˢ (neighbors r.2.1 ×ˢ neighbors r.2.2.1))

private theorem mem_box {r s : Row} (h : ok r s) : s ∈ box r :=
  mem_product.mpr ⟨(neighbors_spec _ _).mp h.2.2.2.1,
    mem_product.mpr ⟨(neighbors_spec _ _).mp h.1,
    mem_product.mpr ⟨(neighbors_spec _ _).mp h.2.1, (neighbors_spec _ _).mp h.2.2.1⟩⟩⟩

private def rowOK (r : Row) : Prop :=
  r.2.1 ∈ neighbors r.1 ∧ r.2.2.1 ∈ neighbors r.2.1 ∧ r.2.2.2 ∈ neighbors r.2.2.1
private instance : DecidablePred rowOK := fun r => by unfold rowOK; infer_instance
private def crossOK (r s : Row) : Prop :=
  s.2.1 ∈ neighbors r.1 ∧ s.2.2.1 ∈ neighbors r.2.1 ∧ s.2.2.2 ∈ neighbors r.2.2.1 ∧
  s.1 ∈ neighbors r.2.1 ∧ s.2.1 ∈ neighbors r.2.2.1 ∧ s.2.2.1 ∈ neighbors r.2.2.2
private instance : DecidableRel crossOK := fun r s => by unfold crossOK; infer_instance
private theorem row_equiv (r : Row) : hrow r ↔ rowOK r := by
  simp only [hrow,rowOK,neighbors_spec]
private theorem cross_equiv (r s : Row) : ok r s ↔ crossOK r s := by
  simp only [ok,crossOK,neighbors_spec]

private def small (r : Row) := (box r).filter (fun s => rowOK s ∧ crossOK r s)
private theorem small_exact (r : Row) :
    (univ.filter fun s => hrow s ∧ ok r s) = small r := by
  ext s
  simp only [small,mem_filter,mem_univ,true_and]
  exact ⟨fun h => ⟨mem_box h.2,(row_equiv s).mp h.1,(cross_equiv r s).mp h.2⟩,
    fun h => ⟨(row_equiv s).mpr h.2.1,(cross_equiv r s).mpr h.2.2⟩⟩

set_option maxHeartbeats 8000000 in
private theorem check_rows : ∀ a : Fin 20, ∀ b ∈ neighbors a, ∀ c ∈ neighbors b,
    ∀ d ∈ neighbors c, let r : Row := (a,b,c,d)
    (small r).card = score r ∧ (∑ s ∈ small r, score s) + 36 = 17*score r := by
  intro a
  fin_cases a <;> decide +kernel

theorem successors (r : Fin 20 × Fin 20 × Fin 20 × Fin 20) (hr : hrow r) :
    (univ.filter (fun s => hrow s ∧ ok r s)).card = score r ∧
    (∑ s ∈ univ.filter (fun s => hrow s ∧ ok r s), score s) + 36 = 17*score r := by
  rw [small_exact]
  rcases r with ⟨a,b,c,d⟩
  have h := (row_equiv _).mp hr
  exact check_rows a b h.1 c h.2.1 d h.2.2

private def startBox : Finset Row :=
  ({0} : Finset (Fin 20)) ×ˢ (neighbors 0 ×ˢ ((univ : Finset (Fin 20)) ×ˢ univ))

private theorem start_exact :
    (univ.filter (fun s : Row => hrow s ∧ s.1=0)) =
      startBox.filter (fun s => rowOK s ∧ s.1=0) := by
  ext s
  simp only [startBox,mem_filter,mem_univ,true_and,mem_product,mem_singleton,and_true,row_equiv]
  exact ⟨fun h => ⟨⟨h.2,h.2 ▸ h.1.1⟩,h⟩, And.right⟩

theorem starters :
    (univ.filter (fun s : Row => hrow s ∧ s.1=0)).card = 27 ∧
    (∑ s ∈ univ.filter (fun s : Row => hrow s ∧ s.1=0), score s) = 351 := by
  rw [start_exact]
  decide +kernel
end IcoCounts

open Finset OMA.S_oeis_a223278

namespace BarkerRows

abbrev Row := Fin 20 × Fin 20 × Fin 20 × Fin 20

private def good {n : ℕ} (f : Fin n → Row) : Prop :=
  (∀ i, hrow (f i)) ∧ ∀ i j : Fin n, j.val = i.val+1 → ok (f i) (f j)

private def after {n : ℕ} (r : Row) (f : Fin n → Row) : Prop :=
  good f ∧ ∀ i : Fin n, i.val = 0 → ok r (f i)

private lemma good_cons {n : ℕ} (r : Row) (f : Fin n → Row) :
    good (Fin.cons r f) ↔ hrow r ∧ after r f := by
  constructor
  · rintro ⟨hr, hc⟩
    refine ⟨by simpa using hr 0, ⟨fun i => ?_, fun i j hj => ?_⟩, fun i hi => ?_⟩
    · simpa using hr i.succ
    · simpa using hc i.succ j.succ (by simpa using hj)
    · simpa using hc 0 i.succ (by simpa using hi)
  · rintro ⟨hr, ⟨hf,hc⟩,hfirst⟩
    constructor
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hr
      · simpa using hf j
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => simp at hij
        | succ j => simpa using hfirst j (by simpa using hij)
      | succ i =>
        cases j using Fin.cases with
        | zero => simp at hij
        | succ j => simpa using hc i j (by simpa using hij)

private lemma after_cons {n : ℕ} (r s : Row) (f : Fin n → Row) :
    after r (Fin.cons s f) ↔ (hrow s ∧ ok r s) ∧ after s f := by
  rw [after, good_cons]
  constructor
  · rintro ⟨⟨hs,hf⟩,hr⟩
    exact ⟨⟨hs, by simpa using hr 0 rfl⟩,hf⟩
  · rintro ⟨⟨hs,hrs⟩,hf⟩
    refine ⟨⟨hs,hf⟩, ?_⟩
    intro i
    cases i using Fin.cases <;> simp [hrs]

private noncomputable def ways (n : ℕ) (r : Row) : ℕ := by
  classical
  exact ((univ : Finset (Fin n → Row)).filter (after r)).card

private lemma split_count {n : ℕ} (P : (Fin (n+1) → Row) → Prop) [DecidablePred P] :
    (univ.filter P).card = ∑ r : Row,
      (univ.filter (fun f : Fin n → Row => P (Fin.cons r f))).card := by
  classical
  simp only [Finset.card_filter]
  let e := Fin.consEquiv (fun _ : Fin (n+1) => Row)
  calc
    _ = ∑ x : Row × (Fin n → Row), (if P (e x) then 1 else 0 : ℕ) :=
      (e.sum_comp (fun f => if P f then 1 else 0)).symm
    _ = _ := Fintype.sum_prod_type (fun x : Row × (Fin n → Row) => if P (e x) then 1 else 0)

private lemma ways_zero (r : Row) : ways 0 r = 1 := by
  classical
  have allGood (f : Fin 0 → Row) : after r f :=
    ⟨⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0⟩
  simp [ways, allGood]

private lemma ways_succ (n : ℕ) (r : Row) : ways (n+1) r =
    ∑ s : Row, if hrow s ∧ ok r s then ways n s else 0 := by
  classical
  unfold ways
  rw [split_count]
  refine sum_congr rfl fun s _ => ?_
  by_cases h : hrow s ∧ ok r s <;> simp [after_cons, h]

private lemma start_succ (n : ℕ) : a (n+1) =
    ∑ s : Row, if hrow s ∧ s.1=0 then ways n s else 0 := by
  classical
  let P (f : Fin (n+1) → Row) := good f ∧ ∀ i : Fin (n+1), i.val = 0 → (f i).1 = 0
  have start (s : Row) (f : Fin n → Row) : P (Fin.cons s f) ↔ (hrow s ∧ s.1=0) ∧ after s f := by
    dsimp only [P]
    rw [good_cons, Fin.forall_fin_succ]
    simp only [Fin.val_zero, Fin.cons_zero, Fin.val_succ, Nat.succ_ne_zero,
      false_implies, forall_const]
    tauto
  have ha : a (n+1) = (univ.filter P).card := by
    unfold a P good
    congr 1
    ext f
    simp only [mem_filter, mem_univ, true_and]
    tauto
  rw [ha, split_count]
  refine sum_congr rfl fun s _ => ?_
  by_cases h : hrow s ∧ s.1=0 <;> simp [start,h,ways]


theorem array_recurrence (d : Row → ℕ)
    (degrees : ∀ r : Row, hrow r → (univ.filter (fun s => hrow s ∧ ok r s)).card = d r)
    (mass : ∀ r : Row, hrow r →
      (∑ s ∈ univ.filter (fun s => hrow s ∧ ok r s), d s) + 36 = 17*d r)
    (start : (univ.filter (fun s : Row => hrow s ∧ s.1=0)).card = 27 ∧
      (∑ s ∈ univ.filter (fun s : Row => hrow s ∧ s.1=0), d s) = 351) :
    a 1 = 27 ∧ a 2 = 351 ∧ ∀ n, a (n+3)+36*a (n+1)=17*a (n+2) := by
  classical
  let S (r : Row) := univ.filter (fun s : Row => hrow s ∧ ok r s)
  let I := univ.filter (fun s : Row => hrow s ∧ s.1=0)
  have next (n : ℕ) (r : Row) : ways (n+1) r = ∑ s ∈ S r, ways n s := by
    simpa only [S, sum_filter] using ways_succ n r
  have initial (n : ℕ) : a (n+1) = ∑ s ∈ I, ways n s := by
    simpa only [I, sum_filter] using start_succ n
  have one (r : Row) (hr : hrow r) : ways 1 r = d r := by
    rw [next 0]
    simpa only [ways_zero, sum_const, smul_eq_mul, mul_one] using (degrees r hr)
  have lift (P : Finset Row) (n : ℕ) (row : ∀ s ∈ P, hrow s)
      (h : ∀ s, hrow s → ways (n+2) s + 36*ways n s = 17*ways (n+1) s) :
      (∑s ∈ P, ways (n+2) s) + 36*(∑s ∈ P, ways n s) = 17*(∑s ∈ P, ways (n+1) s) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun s hs => h s (row s hs)
  have step (n : ℕ) : ∀ r, hrow r → ways (n+2) r + 36*ways n r = 17*ways (n+1) r := by
    induction n with
    | zero =>
      intro r hr
      simp only [Nat.zero_add, ways_zero, mul_one, one r hr]
      rw [next 1]
      have eq : (∑ s ∈ S r, ways 1 s) = ∑ s ∈ S r, d s :=
        sum_congr rfl fun s hs => one s (mem_filter.mp hs).2.1
      rw [eq]
      exact mass r hr
    | succ n ih =>
      intro r hr
      rw [next (n+2), next n, next (n+1)]
      exact lift (S r) n (fun s hs => (mem_filter.mp hs).2.1) ih
  refine ⟨?_, ?_, ?_⟩
  · rw [initial 0]
    simpa only [ways_zero, sum_const, smul_eq_mul, mul_one] using start.1
  · rw [initial 1, ← start.2]
    exact sum_congr rfl fun s hs => one s (mem_filter.mp hs).2.1
  · intro n
    rw [initial (n+2), initial n, initial (n+1)]
    exact lift I n (fun s hs => (mem_filter.mp hs).2.1) (step n)

end BarkerRows

namespace BarkerRec4
open PowerSeries

/-- The characteristic polynomial gives both formulas from the positive-offset recurrence. -/
theorem of_recurrence (a : ℕ → ℕ) (h₁ : a 1 = 27) (h₂ : a 2 = 351)
    (step : ∀ n : ℕ, a (n+3) + 36*a (n+1) = 17*a (n+2)) :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - 17 * X + 36 * X ^ 2) = 27 * X * (1 - 4 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (3 * 2 ^ (-1 - (n : ℤ)) *
        ((17 - Real.sqrt 145) ^ n * (-1 + Real.sqrt 145) +
          (1 + Real.sqrt 145) * (17 + Real.sqrt 145) ^ n)) / Real.sqrt 145 := by
  constructor
  · let A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    change A * _ = _
    rw [show A * (1 - 17*X + 36*X^2) =
      A + ((A*X)*C (36:ℚ) - A*C (17:ℚ))*X by simp only [map_ofNat]; ring,
      show (27 * X * (1 - 4*X) : PowerSeries ℚ) = (C 27 - C 108*X)*X by simp only [map_ofNat]; ring]
    apply PowerSeries.ext
    intro n
    rcases n with _ | _ | _ | n
    · simp [A]
    · norm_num [A, coeff_succ_mul_X, coeff_mk, coeff_mul_C, coeff_C, h₁]
    · norm_num [A, coeff_succ_mul_X, coeff_mk, coeff_mul_C, coeff_C, h₁, h₂]
    · have hw : (a (n+3) : ℚ) + 36*a (n+1) = 17*a (n+2) := by exact_mod_cast step n
      simp [A, coeff_succ_mul_X, coeff_mk, coeff_mul_C]
      linarith
  · let r := Real.sqrt 145
    have hr : r ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    have hr₂ : r^2 = 145 := Real.sq_sqrt (by norm_num)
    let u := (17-r)/2
    let v := (17+r)/2
    let f (n : ℕ) := (3*(-1+r)*u^n + 3*(1+r)*v^n)/(2*r)
    have char_u : u^2 = 17*u-36 := by dsimp [u]; nlinarith [hr₂]
    have char_v : v^2 = 17*v-36 := by dsimp [v]; nlinarith [hr₂]
    have seq (x : ℝ) (char : x^2 = 17*x-36) (n : ℕ) :
        x^(n+3) + 36*x^(n+1) = 17*x^(n+2) := by
      calc
        _ = x^(n+1) * (x^2+36) := by ring
        _ = _ := by rw [char]; ring
    have sf (n : ℕ) : f (n+3) + 36*f (n+1) = 17*f (n+2) := by
      dsimp only [f]
      simp only [div_eq_mul_inv]
      linear_combination (3*(-1+r)*(2*r)⁻¹) * seq u char_u n +
        (3*(1+r)*(2*r)⁻¹) * seq v char_v n
    have first : (a 1 : ℝ) = f 1 := by
      rw [h₁]; dsimp [f,u,v]; field_simp; ring
    have second : (a 2 : ℝ) = f 2 := by
      rw [h₂]; dsimp [f,u,v]; field_simp
      linear_combination -r * hr₂ * 6
    have pair (n : ℕ) : (a (n+1) : ℝ) = f (n+1) ∧ (a (n+2) : ℝ) = f (n+2) := by
      induction n with
      | zero => exact ⟨first,second⟩
      | succ n ih =>
        refine ⟨ih.2, ?_⟩
        have hn : (a (n+3) : ℝ) + 36*a (n+1) = 17*a (n+2) := by exact_mod_cast step n
        change (a (n+3) : ℝ) = f (n+3)
        linarith [sf n, ih.1, ih.2]
    intro n hn
    have value : (a n : ℝ) = f n := by
      cases n with
      | zero => omega
      | succ n => exact (pair n).1
    have exponent : (2 : ℝ)^(-1 - (n : ℤ)) = (2 * (2:ℝ)^n)⁻¹ := by
      rw [show -1 - (n : ℤ) = -((n+1 : ℕ) : ℤ) by push_cast; ring,
        zpow_neg, zpow_natCast, pow_succ, mul_comm]
    rw [value, exponent]
    dsimp only [f,u,v,r]
    rw [div_pow, div_pow]
    ring

end BarkerRec4

theorem OMA.solution : type_of% @OMA.S_oeis_a223278.main := by
  obtain ⟨h₁,h₂,step⟩ := BarkerRows.array_recurrence IcoCounts.score
    (fun r hr => (IcoCounts.successors r hr).1) (fun r hr => (IcoCounts.successors r hr).2)
    IcoCounts.starters
  exact BarkerRec4.of_recurrence OMA.S_oeis_a223278.a h₁ h₂ step
