import OMAStatements.S_oeis_a277798

/-!
# The forward decimal reading of cellular rule 1

Robert Price introduced A277798 in 2016, and Colin Barker conjectured its
closed form, recurrence and generating function. The source entry lists
eight rule codes giving the same reading. We prove precisely which codes
among 0 through 1023 give the entire alternating plane pattern.

Javier Leguina's public sibling proofs for A277797 (reversed decimal) and
A277800 (forward binary), open-math-agents PRs #23140 and #23131, already
established the two phases for rule 1. This proof uses a local classification
of the two transitions across all rule codes and evaluates the registered
forward-decimal digit sum. The registered statement was contributed by
@clementtrecourt. OEIS source: https://oeis.org/A277798.
-/

namespace OMA.S_oeis_a277798.RuleOne

def single (x y : ℤ) : Bool := decide (x = 0 ∧ y = 0)

def exterior (x y : ℤ) : Bool := decide (1 < x.natAbs + y.natAbs)

/-- The ten possible inputs to an outer-totalistic rule. -/
def index (f : ℤ → ℤ → Bool) (x y : ℤ) : ℕ :=
  (f x y).toNat + 2 * ((f (x + 1) y).toNat + (f (x - 1) y).toNat +
    (f x (y + 1)).toNat + (f x (y - 1)).toNat)

/-- A full orbit starting from a single live cell, alternating with
the complement of the five-cell cross about that cell. -/
def crossOrbit (c : ℕ) : Prop :=
  (∀ k x y, cell c (2 * k) x y = single x y) ∧
  (∀ k x y, cell c (2 * k + 1) x y = exterior x y)

private abbrev accepts (j : ℕ) (b : Bool) : Prop :=
  (j = 0 ∧ b = true) ∨ (j ∈ ([1, 2, 5, 6, 7, 9] : List ℕ) ∧ b = false)

private theorem local_indices (x y : ℤ) :
    accepts (index single x y) (exterior x y) ∧ accepts (index exterior x y) (single x y) := by
  have window : ∀ a b : Fin 5,
      let i : ℤ := (a : ℕ) - 2
      let j : ℤ := (b : ℕ) - 2
      accepts (index single i j) (exterior i j) ∧ accepts (index exterior i j) (single i j) := by
    decide +kernel
  by_cases h : -2 ≤ x ∧ x ≤ 2 ∧ -2 ≤ y ∧ y ≤ 2
  · let a : Fin 5 := ⟨(x + 2).toNat, by omega⟩
    let b : Fin 5 := ⟨(y + 2).toNat, by omega⟩
    have hx : (a : ℤ) - 2 = x := by dsimp [a]; omega
    have hy : (b : ℤ) - 2 = y := by dsimp [b]; omega
    simpa only [hx, hy] using window a b
  · have far (u v : ℤ) (ha : u < -1 ∨ 1 < u ∨ v < -1 ∨ 1 < v) :
        single u v = false ∧ exterior u v = true := by
      cases u <;> cases v <;> simp_all [single, exterior] <;> omega
    have h0 := far x y (by omega)
    have h1 := far (x + 1) y (by omega)
    have h2 := far (x - 1) y (by omega)
    have h3 := far x (y + 1) (by omega)
    have h4 := far x (y - 1) (by omega)
    simp [index, h0, h1, h2, h3, h4, accepts]

/-- The three unused neighborhood inputs can be chosen independently. -/
def requiredBits (c : ℕ) : Prop :=
  c.testBit 0 = true ∧ ∀ j ∈ ([1, 2, 5, 6, 7, 9] : List ℕ), c.testBit j = false

theorem orbit_iff_requiredBits (c : ℕ) : crossOrbit c ↔ requiredBits c := by
  constructor
  · rintro ⟨even, odd⟩
    have first (x y : ℤ) : c.testBit (index single x y) = exterior x y := odd 0 x y
    have second (x y : ℤ) : c.testBit (index exterior x y) = single x y := by
      have h := even 1 x y
      change c.testBit (index (cell c 1) x y) = single x y at h
      have hh : cell c 1 = exterior := funext fun i => funext fun j => odd 0 i j
      rwa [hh] at h
    refine ⟨first 2 0, ?_⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact first 0 0
    · exact first 1 0
    · exact second 1 1
    · exact second 1 0
    · exact second 2 0
    · exact second 3 0
  · intro h
    have applyBits {j b} : accepts j b → c.testBit j = b := by
      rintro (⟨rfl, rfl⟩ | ⟨hj, rfl⟩)
      · exact h.1
      · exact h.2 j hj
    have steps (k : ℕ) :
        cell c (2*k) = single ∧ cell c (2*k+1) = exterior := by
      have toOdd (t : ℕ) (ht : cell c t = single) : cell c (t+1) = exterior := by
        funext x y
        change c.testBit (index (cell c t) x y) = exterior x y
        rw [ht]
        exact applyBits (local_indices x y).1
      have toEven (t : ℕ) (ht : cell c t = exterior) : cell c (t+1) = single := by
        funext x y
        change c.testBit (index (cell c t) x y) = single x y
        rw [ht]
        exact applyBits (local_indices x y).2
      induction k with
      | zero => exact ⟨rfl, toOdd 0 rfl⟩
      | succ k ih =>
        have he : cell c (2*(k+1)) = single := by
          rw [show 2*(k+1) = (2*k+1)+1 by omega]
          exact toEven _ ih.2
        exact ⟨he, toOdd _ he⟩
    exact ⟨fun k x y => congrFun (congrFun (steps k).1 x) y,
      fun k x y => congrFun (congrFun (steps k).2 x) y⟩

/-- Exactly eight of the 1024 von Neumann outer-totalistic rule codes have this orbit. -/
theorem crossOrbit_iff {c : ℕ} (hc : c < 1024) :
    crossOrbit c ↔ c ∈ ([1, 9, 17, 25, 257, 265, 273, 281] : List ℕ) := by
  rw [orbit_iff_requiredBits]
  have test : ∀ j : Fin 1024,
      ((j : ℕ).testBit 0 = true ∧ ∀ k ∈ ([1, 2, 5, 6, 7, 9] : List ℕ),
        (j : ℕ).testBit k = false) ↔ (j : ℕ) ∈ ([1, 9, 17, 25, 257, 265, 273, 281] : List ℕ) := by
    decide +kernel
  exact test ⟨c, hc⟩

theorem even_state (k : ℕ) (i j : ℤ) :
    cell 1 (2*k) i j = decide (i=0 ∧ j=0) :=
  ((crossOrbit_iff (c:=1) (by decide)).2 (by decide)).1 k i j

theorem odd_state (k : ℕ) (i j : ℤ) :
    cell 1 (2*k+1) i j = decide (1 < i.natAbs+j.natAbs) :=
  ((crossOrbit_iff (c:=1) (by decide)).2 (by decide)).2 k i j

end OMA.S_oeis_a277798.RuleOne

namespace RuleOne

open OMA.S_oeis_a277798 Finset

/-- The forward decimal reading has one leading digit at even times. -/
theorem even_reading (k : ℕ) (phase : ∀ i j : ℤ,
    cell 1 (2*k) i j = decide (i=0 ∧ j=0)) : a (2*k) = (10:ℤ)^(2*k) := by
  simp [a, phase]

/-- After the two initial zeroes at odd times, every remaining digit is one. -/
theorem odd_reading (k : ℕ) (phase : ∀ i j : ℤ,
    cell 1 (2*k+1) i j = decide (1 < i.natAbs+j.natAbs)) :
    9*a (2*k+1) = (10:ℤ)^(2*k)-1 := by
  let n := 2*k+1
  have read : a n = ∑ j ∈ range (2*k), (10:ℤ)^j := by
    simp only [a, n, phase, Int.natAbs_natCast, Int.natAbs_zero, add_zero, decide_eq_true_eq]
    rw [← sum_range_reflect (fun j : ℕ => if 1 < j then (10:ℤ)^(2*k+1-j) else 0) (2*k+1+1)]
    simp only [Nat.add_sub_cancel]
    rw [show 2*k+1+1 = 2*k+2 by omega, sum_range_add]
    have tiny : (∑ j ∈ range 2, if 1 < 2*k+1-(2*k+j) then (10:ℤ)^(2*k+1-(2*k+1-(2*k+j))) else 0) = 0 := by
      apply sum_eq_zero
      intro j _
      rw [if_neg (by omega)]
    rw [tiny, add_zero]
    apply sum_congr rfl
    intro j hj
    have h := mem_range.mp hj
    rw [if_pos (by omega), show 2*k+1-(2*k+1-j) = j by omega]
  rw [show 2*k+1 = n by rfl, read]
  have geom := geom_sum_mul (10:ℤ) (2*k)
  linear_combination geom

/-- The even and odd readings give Barker's closed form. -/
theorem closed_of_readings
    (ev : ∀ k, a (2*k) = (10:ℤ)^(2*k))
    (od : ∀ k, 9*a (2*k+1) = (10:ℤ)^(2*k)-1) (n : ℕ) :
    (a n : ℚ) = (-10+89*(-10:ℚ)^n+10*(-1:ℚ)^n+91*(10:ℚ)^n)/180 := by
  let k := n/2
  rcases (show n=2*k ∨ n=2*k+1 by dsimp [k]; omega) with h|h
  · rw [h,ev]
    push_cast
    rw [show (-10:ℚ)^(2*k) = (10:ℚ)^(2*k) by simp [pow_mul],
      show (-1:ℚ)^(2*k)=1 by simp [pow_mul]]
    ring
  · rw [h,pow_succ,pow_succ,pow_succ]
    rw [show (-10:ℚ)^(2*k) = (10:ℚ)^(2*k) by simp [pow_mul],
      show (-1:ℚ)^(2*k)=1 by simp [pow_mul]]
    have oddQ : (9:ℚ)*a (2*k+1) = (10:ℚ)^(2*k)-1 := by exact_mod_cast od k
    linear_combination oddQ / 9

end RuleOne

namespace RuleOne

open PowerSeries

/-- The four geometric terms have the same fourth-order recurrence. -/
theorem recurrence_of_closed (f : ℕ → ℚ)
    (closed : ∀ n, f n = (-10+89*(-10:ℚ)^n+10*(-1:ℚ)^n+91*(10:ℚ)^n)/180)
    (n : ℕ) (hn : 4 ≤ n) : f n = 101*f (n-2)-100*f (n-4) := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+4 := ⟨n-4,by omega⟩
  rw [show m+4-2=m+2 by omega, Nat.add_sub_cancel, closed, closed, closed]
  simp only [pow_add]
  ring

/-- Coefficient comparison recovers the numerator from the four initial terms. -/
theorem gf_of_closed (f : ℕ → ℚ)
    (closed : ∀ n, f n = (-10+89*(-10:ℚ)^n+10*(-1:ℚ)^n+91*(10:ℚ)^n)/180) :
    mk f * ((1-X)*(1+X)*(1-10*X)*(1+10*X) : PowerSeries ℚ) =
    1-X^2+11*X^3 := by
  have expand (s : PowerSeries ℚ) : s*((1-X)*(1+X)*(1-10*X)*(1+10*X)) =
      s-(C 101*s)*X^2+(C 100*s)*X^4 := by rw [map_ofNat, map_ofNat]; ring
  rw [expand, ← show C (R:=ℚ) 11=11 by exact map_ofNat _ _]
  ext n
  simp only [map_add,map_sub]
  rw [coeff_C_mul_X_pow]
  simp only [coeff_one,coeff_X_pow,coeff_mul_X_pow',
    coeff_C_mul,coeff_mk]
  by_cases hn : n < 4
  · interval_cases n <;> norm_num [closed]
  · have recurrence :=  recurrence_of_closed f closed n (by omega)
    simp (disch := omega) only [if_pos,if_neg]
    linear_combination recurrence

end RuleOne

open OMA.S_oeis_a277798 in
theorem RuleOne.forward_formula (n : ℕ) :
    (a n : ℚ) = (-10 + 89*(-10:ℚ)^n + 10*(-1:ℚ)^n + 91*(10:ℚ)^n)/180 :=
  closed_of_readings (fun k => even_reading k (OMA.S_oeis_a277798.RuleOne.even_state k))
    (fun k => odd_reading k (OMA.S_oeis_a277798.RuleOne.odd_state k)) n

open OMA.S_oeis_a277798 in
theorem OMA.solution : type_of% @OMA.S_oeis_a277798.main :=
  ⟨RuleOne.gf_of_closed _ RuleOne.forward_formula,
    RuleOne.recurrence_of_closed _ RuleOne.forward_formula, RuleOne.forward_formula⟩
