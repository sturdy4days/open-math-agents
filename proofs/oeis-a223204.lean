import OMAStatements.S_oeis_a223204
import Mathlib.Tactic

/-!
# Two-state transfer for OEIS A223204

R. H. Hardin introduced the rolling-icosahedron sequence. Colin Barker conjectured its
generating function and its closed form. This proof adapts our diagonal-move A223277 row decomposition to vertical moves. We count arrays using the face labels of the
statement formalized by @jleguina. A legal row with coinciding endpoints has 5 successors
of the same type and 6 of the other type. A row with distinct endpoints has 3 successors
of the first type and 4 of the second type.
-/

namespace IcoCounts
open Finset OMA.S_oeis_a223204
private abbrev Row := Fin 20 × Fin 20 × Fin 20

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

/-- The three vertical edge conditions leave only 27 triples to inspect. -/
private def box (r : Row) : Finset Row :=
  neighbors r.1 ×ˢ (neighbors r.2.1 ×ˢ neighbors r.2.2)

private theorem mem_box {r s : Row} (hs : ok r s) : s ∈ box r := by
  exact Finset.mem_product.mpr ⟨(neighbors_spec _ _).mp hs.1,
    Finset.mem_product.mpr ⟨(neighbors_spec _ _).mp hs.2.1, (neighbors_spec _ _).mp hs.2.2⟩⟩

private theorem restrict_box (r : Row) (P : Row → Prop) [DecidablePred P] :
    (univ.filter fun s => hrow s ∧ ok r s ∧ P s) =
      ((box r).filter fun s => hrow s ∧ ok r s ∧ P s) := by
  ext s
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h => ⟨mem_box h.2.1,h⟩, And.right⟩

private def quickRow (s : Row) : Prop := s.2.1 ∈ neighbors s.1 ∧ s.2.2 ∈ neighbors s.2.1
private instance : DecidablePred quickRow := fun s => by unfold quickRow; infer_instance
private def quickOk (r s : Row) : Prop := s.1 ∈ neighbors r.1 ∧ s.2.1 ∈ neighbors r.2.1 ∧
  s.2.2 ∈ neighbors r.2.2
private instance : DecidableRel quickOk := fun r s => by unfold quickOk; infer_instance
private theorem equivRow (s : Row) : hrow s ↔ quickRow s := by simp only [hrow, quickRow, neighbors_spec]
private theorem equivOk (r s : Row) : ok r s ↔ quickOk r s := by simp only [ok, quickOk, neighbors_spec]
private theorem as_quick (r : Row) (P : Row → Prop) [DecidablePred P] :
    ((box r).filter fun s => hrow s ∧ ok r s ∧ P s) =
      ((box r).filter fun s => quickRow s ∧ quickOk r s ∧ P s) := by
  ext s
  simp only [mem_filter, equivRow, equivOk]

private def startBox : Finset Row := ({0} : Finset (Fin 20)) ×ˢ (neighbors 0 ×ˢ univ)
private theorem start_quick (P : Row → Prop) [DecidablePred P] :
    (univ.filter fun s => hrow s ∧ s.1 = 0 ∧ P s) =
      (startBox.filter fun s => quickRow s ∧ s.1 = 0 ∧ P s) := by
  ext s
  simp only [mem_filter, mem_univ, true_and, equivRow, startBox, mem_product,
    mem_singleton, and_true]
  exact ⟨fun h => ⟨⟨h.2.1, h.2.1 ▸ h.1.1⟩,h⟩, And.right⟩

set_option maxHeartbeats 3000000 in
private theorem count_boxes : ∀ a b c : Fin 20, quickRow (a,b,c) →
    (((box (a,b,c)).filter fun s => quickRow s ∧ quickOk (a,b,c) s ∧ s.1 = s.2.2).card =
      (if a = c then 5 else 3)) ∧
    (((box (a,b,c)).filter fun s => quickRow s ∧ quickOk (a,b,c) s ∧ s.1 ≠ s.2.2).card = (if a = c then 6 else 4)) := by
  intro a
  fin_cases a <;> decide +kernel

theorem successors (r : Fin 20 × Fin 20 × Fin 20) (hr : hrow r) :
    ((univ.filter fun s => hrow s ∧ ok r s ∧ s.1 = s.2.2).card = (if r.1 = r.2.2 then 5 else 3)) ∧
    ((univ.filter fun s => hrow s ∧ ok r s ∧ s.1 ≠ s.2.2).card = (if r.1 = r.2.2 then 6 else 4)) := by
  rw [restrict_box r (fun s => s.1 = s.2.2), restrict_box r (fun s => s.1 ≠ s.2.2)]
  rw [as_quick r (fun s => s.1 = s.2.2), as_quick r (fun s => s.1 ≠ s.2.2)]
  exact count_boxes r.1 r.2.1 r.2.2 ((equivRow _).mp hr)

theorem starters :
    ((univ.filter fun s : Row => hrow s ∧ s.1 = 0 ∧ s.1 = s.2.2).card = 3) ∧
    ((univ.filter fun s : Row => hrow s ∧ s.1 = 0 ∧ s.1 ≠ s.2.2).card = 6) := by
  rw [start_quick (fun s => s.1 = s.2.2), start_quick (fun s => s.1 ≠ s.2.2)]
  decide +kernel
end IcoCounts

open Finset OMA.S_oeis_a223204

namespace BarkerRows

abbrev Row := Fin 20 × Fin 20 × Fin 20

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

private lemma weighted (P Q : Row → Prop) [DecidablePred P] [DecidablePred Q]
    (f : Row → ℕ) (u v : ℕ) (hf : ∀ s, P s → f s = if Q s then u else v) :
    (∑ s, if P s then f s else 0) =
      (univ.filter (fun s => P s ∧ Q s)).card * u +
      (univ.filter (fun s => P s ∧ ¬Q s)).card * v := by
  classical
  simp only [Finset.card_filter, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : P s
  · by_cases q : Q s <;> simp [h, q, hf s h]
  · simp [h]

private def values : ℕ → ℕ × ℕ
  | 0 => (1,1)
  | n+1 => (5*(values n).1 + 6*(values n).2, 3*(values n).1 + 4*(values n).2)

/-- Counts of legal suffixes depend only on equality of the two ends of the preceding row. -/
theorem array_recurrence
    (successors : ∀ r : Row, hrow r →
      ((univ.filter fun s => hrow s ∧ ok r s ∧ s.1 = s.2.2).card =
        if r.1 = r.2.2 then 5 else 3) ∧
      (univ.filter fun s => hrow s ∧ ok r s ∧ s.1 ≠ s.2.2).card = (if r.1 = r.2.2 then 6 else 4))
    (starters : ((univ.filter fun s : Row => hrow s ∧ s.1 = 0 ∧ s.1 = s.2.2).card = 3) ∧
      (univ.filter fun s : Row => hrow s ∧ s.1 = 0 ∧ s.1 ≠ s.2.2).card = 6) :
    a 1 = 9 ∧ a 2 = 75 ∧ ∀ n, a (n+3) + 2*a (n+1) = 9*a (n+2) := by
  classical
  have types (n : ℕ) (r : Row) (hr : hrow r) :
      ways n r = if r.1=r.2.2 then (values n).1 else (values n).2 := by
    induction n generalizing r with
    | zero => simp [ways_zero, values]
    | succ n ih =>
      rw [ways_succ]
      have h := weighted (fun s => hrow s ∧ ok r s) (fun s => s.1=s.2.2)
        (ways n) (values n).1 (values n).2 (fun s hs => ih s hs.1)
      simp only [and_assoc] at h
      rw [h, (successors r hr).1, (successors r hr).2]
      by_cases he : r.1=r.2.2 <;> simp [he, values]
  have total (n : ℕ) : a (n+1) = 3*(values n).1 + 6*(values n).2 := by
    rw [start_succ]
    have h := weighted (fun s => hrow s ∧ s.1=0) (fun s => s.1=s.2.2)
      (ways n) (values n).1 (values n).2 (fun s hs => types n s hs.1)
    simp only [and_assoc] at h
    rw [h, starters.1, starters.2]
  refine ⟨by simpa [values] using total 0, by simpa [values] using total 1, ?_⟩
  intro n
  rw [total (n+2), total n, total (n+1)]
  simp only [values]
  ring

end BarkerRows

namespace BarkerRec
open PowerSeries

/-- The characteristic polynomial gives both formulas from the positive-offset recurrence. -/
theorem of_recurrence (a : ℕ → ℕ) (h₁ : a 1 = 9) (h₂ : a 2 = 75)
    (step : ∀ n : ℕ, a (n+3) + 2*a (n+1) = 9*a (n+2)) :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - 9 * X + 2 * X ^ 2) = 3 * X * (3 - 2 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (3 * 2 ^ (-1 - (n : ℤ)) *
        ((9 - Real.sqrt 73) ^ n * (3 + Real.sqrt 73) +
          (-3 + Real.sqrt 73) * (9 + Real.sqrt 73) ^ n)) / Real.sqrt 73 := by
  constructor
  · let A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    change A * _ = _
    rw [show A * (1 - 9*X + 2*X^2) =
      A + ((A*X)*C (2:ℚ) - A*C (9:ℚ))*X by simp only [map_ofNat]; ring,
      show (3 * X * (3 - 2*X) : PowerSeries ℚ) = (C 9 - C 6*X)*X by simp only [map_ofNat]; ring]
    apply PowerSeries.ext
    intro n
    rcases n with _ | _ | _ | n
    · simp [A]
    · norm_num [A, coeff_succ_mul_X, coeff_mk, coeff_mul_C, coeff_C, h₁]
    · norm_num [A, coeff_succ_mul_X, coeff_mk, coeff_mul_C, coeff_C, h₁, h₂]
    · have hw : (a (n+3) : ℚ) + 2*a (n+1) = 9*a (n+2) := by exact_mod_cast step n
      simp [A, coeff_succ_mul_X, coeff_mk, coeff_mul_C]
      linarith
  · let r := Real.sqrt 73
    have hr : r ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    have hr₂ : r^2 = 73 := Real.sq_sqrt (by norm_num)
    let u := (9-r)/2
    let v := (9+r)/2
    let f (n : ℕ) := (3*((3+r)*u^n + (-3+r)*v^n))/(2*r)
    have char_u : u^2 = 9*u-2 := by dsimp [u]; nlinarith [hr₂]
    have char_v : v^2 = 9*v-2 := by dsimp [v]; nlinarith [hr₂]
    have seq (x : ℝ) (char : x^2 = 9*x-2) (n : ℕ) :
        x^(n+3) + 2*x^(n+1) = 9*x^(n+2) := by
      calc
        _ = x^(n+1) * (x^2+2) := by ring
        _ = _ := by rw [char]; ring
    have sf (n : ℕ) : f (n+3) + 2*f (n+1) = 9*f (n+2) := by
      dsimp only [f]
      linear_combination (3*(3+r)/(2*r)) * seq u char_u n +
        (3*(-3+r)/(2*r)) * seq v char_v n
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
        have hn : (a (n+3) : ℝ) + 2*a (n+1) = 9*a (n+2) := by exact_mod_cast step n
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

end BarkerRec

theorem OMA.solution : type_of% @OMA.S_oeis_a223204.main := by
  obtain ⟨h₁, h₂, step⟩ := BarkerRows.array_recurrence IcoCounts.successors IcoCounts.starters
  exact BarkerRec.of_recurrence OMA.S_oeis_a223204.a h₁ h₂ step
