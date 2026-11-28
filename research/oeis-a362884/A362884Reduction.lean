import OMAStatements.S_oeis_a362884

/-!
# A reduction of OEIS A362884 to one 44-step return for A276175

Checked against open-math-agents statement PR 14520 at
`816bc341d7e16f17a6bc9f83ba21aefc615660f3` with Lean 4.33.1.
The eight-step identity is due to mercio, and the two valuation words and
return calculation are due to Sil. The final theorem takes the block
return as an explicit hypothesis.

* https://oeis.org/A362884
* https://math.stackexchange.com/a/1906097
* https://github.com/TheSil/mse_1905063/blob/2e5b1c397ae89af800c4aee585a9d0eac982d962/proof.tex
-/

namespace A362884

open OMA.S_oeis_a362884 (a)

/-- The rational numbers whose reduced denominators are powers of two. -/
def dyadic : Subring ℚ where
  carrier := {q | ∃ (m : ℤ) (k : ℕ), q = (m : ℚ) / (2 : ℚ) ^ k}
  zero_mem' := ⟨0, 0, by norm_num⟩
  one_mem' := ⟨1, 0, by norm_num⟩
  neg_mem' := by
    rintro q ⟨m, k, rfl⟩
    exact ⟨-m, k, by push_cast; ring⟩
  add_mem' := by
    rintro q r ⟨m, k, rfl⟩ ⟨n, l, rfl⟩
    refine ⟨m * (2 : ℤ) ^ l + n * (2 : ℤ) ^ k, k + l, ?_⟩
    push_cast
    rw [pow_add]
    field_simp
  mul_mem' := by
    rintro q r ⟨m, k, rfl⟩ ⟨n, l, rfl⟩
    refine ⟨m * n, k + l, ?_⟩
    push_cast
    rw [pow_add, div_mul_div_comm]

theorem a_positive (n : ℕ) : 0 < a n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 4
    · interval_cases n <;> norm_num [a]
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 4 := ⟨n - 4, by omega⟩
      have h0 := ih m (by omega)
      have h1 := ih (m + 1) (by omega)
      have h2 := ih (m + 2) (by omega)
      have h3 := ih (m + 3) (by omega)
      rw [a]
      positivity

/-- Rescaling by four puts the sequence in mercio's normalized recurrence. -/
def b (n : ℕ) : ℚ := a n / 4

theorem b_rec (n : ℕ) :
    b n * b (n + 4) = b (n + 1) * b (n + 2) * b (n + 3) + 1 := by
  have hn : a n ≠ 0 := (a_positive n).ne'
  unfold b
  rw [a]
  field_simp
  ring

/-- The eight-step update is a polynomial in seven earlier entries. -/
def eightPolynomial (x0 x2 x3 x4 x5 x6 x7 : ℚ) : ℚ :=
  let X := x2 * x3
  let Y := x3 * x5
  let Z := x5 * x6
  x0 * x5 * x6 * x7 - (X + Y + Z) - x4 * (X * Y + X * Z + Y * Z) - x4 ^ 2 * X * Y * Z

theorem eight_step {x0 x1 x2 x3 x4 x5 x6 x7 x8 : ℚ}
    (h0 : x0 * x4 = x1 * x2 * x3 + 1)
    (h1 : x1 * x5 = x2 * x3 * x4 + 1)
    (h2 : x2 * x6 = x3 * x4 * x5 + 1)
    (h3 : x3 * x7 = x4 * x5 * x6 + 1)
    (h4 : x4 * x8 = x5 * x6 * x7 + 1)
    (hx4 : x4 ≠ 0) :
    x8 = eightPolynomial x0 x2 x3 x4 x5 x6 x7 := by
  have hprod :
      (x1 * x2 * x3) * (x5 * x6 * x7) =
        (1 + x4 * (x2 * x3)) * (1 + x4 * (x3 * x5)) * (1 + x4 * (x5 * x6)) := by
    calc
      _ = (x1 * x5) * (x2 * x6) * (x3 * x7) := by ring
      _ = _ := by rw [h1, h2, h3]; ring
  apply mul_left_cancel₀ hx4
  rw [h4]
  unfold eightPolynomial
  linear_combination -hprod - (x5 * x6 * x7) * h0

theorem b_eight (n : ℕ) :
    b (n + 8) = eightPolynomial (b n) (b (n + 2)) (b (n + 3)) (b (n + 4))
      (b (n + 5)) (b (n + 6)) (b (n + 7)) := by
  apply eight_step (b_rec n) (b_rec (n + 1)) (b_rec (n + 2))
    (b_rec (n + 3)) (b_rec (n + 4))
  exact (div_pos (a_positive _) (by norm_num)).ne'

private theorem eightPolynomial_mem {x0 x2 x3 x4 x5 x6 x7 : ℚ}
    (h0 : x0 ∈ dyadic) (h2 : x2 ∈ dyadic) (h3 : x3 ∈ dyadic) (h4 : x4 ∈ dyadic)
    (h5 : x5 ∈ dyadic) (h6 : x6 ∈ dyadic) (h7 : x7 ∈ dyadic) :
    eightPolynomial x0 x2 x3 x4 x5 x6 x7 ∈ dyadic := by
  have hx := dyadic.mul_mem h2 h3
  have hy := dyadic.mul_mem h3 h5
  have hz := dyadic.mul_mem h5 h6
  have hsum := dyadic.add_mem (dyadic.add_mem hx hy) hz
  have hpairs := dyadic.add_mem (dyadic.add_mem (dyadic.mul_mem hx hy) (dyadic.mul_mem hx hz))
    (dyadic.mul_mem hy hz)
  have hprod := dyadic.mul_mem (dyadic.mul_mem (dyadic.mul_mem h0 h5) h6) h7
  have hlast := dyadic.mul_mem (dyadic.mul_mem (dyadic.mul_mem (dyadic.pow_mem h4 2) hx) hy) hz
  exact dyadic.sub_mem (dyadic.sub_mem (dyadic.sub_mem hprod hsum) (dyadic.mul_mem h4 hpairs)) hlast

private theorem b_mem_dyadic (n : ℕ) : b n ∈ dyadic := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 8
    · interval_cases n
      · exact ⟨1, 1, by norm_num [b, a]⟩
      · exact ⟨4, 0, by norm_num [b, a]⟩
      · exact ⟨1, 1, by norm_num [b, a]⟩
      · exact ⟨1, 1, by norm_num [b, a]⟩
      · exact ⟨4, 0, by norm_num [b, a]⟩
      · exact ⟨1, 1, by norm_num [b, a]⟩
      · exact ⟨4, 0, by norm_num [b, a]⟩
      · exact ⟨18, 0, by norm_num [b, a]⟩
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 8 := ⟨n - 8, by omega⟩
      rw [b_eight]
      exact eightPolynomial_mem (ih m (by omega)) (ih (m + 2) (by omega))
        (ih (m + 3) (by omega)) (ih (m + 4) (by omega)) (ih (m + 5) (by omega))
        (ih (m + 6) (by omega)) (ih (m + 7) (by omega))

/-- Every term of A362884 has a denominator that is a power of two. -/
theorem a_dyadic (n : ℕ) : ∃ (m : ℤ) (k : ℕ), a n = (m : ℚ) / (2 : ℚ) ^ k := by
  have heq : a n = 4 * b n := by unfold b; ring
  have h4 : (4 : ℚ) ∈ dyadic := ⟨4, 0, by norm_num⟩
  rw [heq]
  exact dyadic.mul_mem h4 (b_mem_dyadic n)

/-- Sil's 44-term word for the 2-adic valuations of A276175. -/
def wWord : Fin 44 → ℤ :=
  ![0, 0, 0, 0, 3, 2, 1, 0, 2, 3, 4,
    0, 0, 0, 0, 3, 2, 1, 0, 2, 3, 4,
    0, 0, 0, 0, 4, 3, 2, 0, 1, 2, 3,
    0, 0, 0, 0, 4, 3, 2, 0, 1, 2, 3]

/-- Sil's 44-term word for the 2-adic valuations of one plus A276175. -/
def tWord : Fin 44 → ℤ :=
  ![1, 1, 1, 1, 0, 0, 0, 5, 0, 0, 0,
    2, 1, 1, 1, 0, 0, 0, 5, 0, 0, 0,
    2, 1, 1, 2, 0, 0, 0, 5, 0, 0, 0,
    1, 1, 1, 2, 0, 0, 0, 5, 0, 0, 0]

def w (n : ℕ) : ℤ := wWord ⟨n % 44, Nat.mod_lt _ (by decide)⟩

def t (n : ℕ) : ℤ := tWord ⟨n % 44, Nat.mod_lt _ (by decide)⟩

/-- The valuation of the candidate A362884 term at index `n + 2`. -/
def transferWord (n : ℕ) : ℤ := 2 + w (n + 2) + w n - w (n + 1) - t (n + 1)

private theorem finite_bounds :
    ∀ n : Fin 44, 0 ≤ transferWord n ∧ transferWord n < 6 := by decide

theorem transferWord_bounds (n : ℕ) : 0 ≤ transferWord n ∧ transferWord n < 6 := by
  have h : transferWord (n % 44) = transferWord n := by
    simp only [transferWord, w, t, Nat.mod_add_mod, Nat.mod_mod]
  rw [← h]
  exact finite_bounds ⟨n % 44, Nat.mod_lt n (by decide)⟩

/-- A276175 defined by its rational recurrence and initial conditions. -/
def c : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | n + 4 => ((1 + c (n + 1)) * (1 + c (n + 2)) * (1 + c (n + 3))) / c n

theorem c_pos (n : ℕ) : 0 < c n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain (_ | _ | _ | _ | n) := n
    · norm_num [c]
    · norm_num [c]
    · norm_num [c]
    · norm_num [c]
    · have h0 := ih n (by omega)
      have h1 := ih (n + 1) (by omega)
      have h2 := ih (n + 2) (by omega)
      have h3 := ih (n + 3) (by omega)
      change 0 < ((1 + c (n + 1)) * (1 + c (n + 2)) * (1 + c (n + 3))) / c n
      positivity

private theorem c_ne_zero (n : ℕ) : c n ≠ 0 := (c_pos n).ne'

private theorem one_add_c_ne_zero (n : ℕ) : 1 + c n ≠ 0 := by
  have := c_pos n
  positivity

private theorem c_mul_step (n : ℕ) :
    c n * c (n + 4) = (1 + c (n + 1)) * (1 + c (n + 2)) * (1 + c (n + 3)) := by
  change c n * (((1 + c (n + 1)) * (1 + c (n + 2)) * (1 + c (n + 3))) / c n) = _
  field_simp [c_ne_zero]

/-- If `α` is the A362884 sequence, this expression is `α (n + 2) / 4`. -/
def ratio (n : ℕ) : ℚ := c (n + 2) * c n / (c (n + 1) * (1 + c (n + 1)))

private theorem ratio_pos (n : ℕ) : 0 < ratio n := by
  unfold ratio
  exact div_pos (mul_pos (c_pos _) (c_pos _))
    (mul_pos (c_pos _) (add_pos_of_pos_of_nonneg (by norm_num) (c_pos _).le))

private theorem ratio_mul_step (n : ℕ) : ratio n * ratio (n + 4) = 1 + c (n + 3) := by
  change (c (n + 2) * c n / (c (n + 1) * (1 + c (n + 1)))) *
      (c (n + 6) * c (n + 4) / (c (n + 5) * (1 + c (n + 5)))) = _
  calc
    _ = ((c n * c (n + 4)) * (c (n + 2) * c (n + 6))) /
        ((1 + c (n + 1)) * (c (n + 1) * c (n + 5)) * (1 + c (n + 5))) := by
      field_simp [c_ne_zero, one_add_c_ne_zero]
    _ = _ := by
      rw [c_mul_step n, c_mul_step (n + 1), c_mul_step (n + 2)]
      field_simp [one_add_c_ne_zero]

private theorem ratio_three (n : ℕ) :
    ratio (n + 1) * ratio (n + 2) * ratio (n + 3) = c (n + 3) := by
  change (c (n + 3) * c (n + 1) / (c (n + 2) * (1 + c (n + 2)))) *
      (c (n + 4) * c (n + 2) / (c (n + 3) * (1 + c (n + 3)))) *
      (c (n + 5) * c (n + 3) / (c (n + 4) * (1 + c (n + 4)))) = _
  calc
    _ = (c (n + 1) * c (n + 5)) * c (n + 3) /
        ((1 + c (n + 2)) * (1 + c (n + 3)) * (1 + c (n + 4))) := by
      field_simp [c_ne_zero, one_add_c_ne_zero]
    _ = _ := by
      rw [c_mul_step (n + 1)]
      field_simp [one_add_c_ne_zero]

private theorem ratio_step (n : ℕ) :
    ratio (n + 4) = (1 + ratio (n + 3) * ratio (n + 2) * ratio (n + 1)) / ratio n := by
  apply (eq_div_iff (ratio_pos n).ne').mpr
  rw [mul_comm (ratio (n + 4)), ratio_mul_step, ← ratio_three n]
  ring

theorem alpha_eq_four_mul_ratio (α : ℕ → ℚ)
    (ha0 : α 0 = 2) (ha1 : α 1 = 16) (ha2 : α 2 = 2) (ha3 : α 3 = 2)
    (hstep : ∀ n, α (n + 4) = (α (n + 3) * α (n + 2) * α (n + 1) + 64) / (4 * α n))
    (n : ℕ) : α (n + 2) = 4 * ratio n := by
  have ha4 := hstep 0
  norm_num [ha0, ha1, ha2, ha3] at ha4
  have ha5 := hstep 1
  norm_num [ha1, ha2, ha3, ha4] at ha5
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain (_ | _ | _ | _ | n) := n
    · norm_num [ha2, ratio, c]
    · norm_num [ha3, ratio, c]
    · norm_num [ha4, ratio, c]
    · norm_num [ha5, ratio, c]
    · have h0 := ih n (by omega)
      have h1 := ih (n + 1) (by omega)
      have h2 := ih (n + 2) (by omega)
      have h3 := ih (n + 3) (by omega)
      change α (n + 4 + 2) = 4 * ratio (n + 4)
      have hrec :
          α (n + 4 + 2) =
            (α (n + 3 + 2) * α (n + 2 + 2) * α (n + 1 + 2) + 64) / (4 * α (n + 2)) := by
        convert hstep (n + 2) using 2
      rw [hrec, h3, h2, h1, h0, ratio_step]
      field_simp [(ratio_pos n).ne']
      ring

private theorem valuation_two_pow (n : ℕ) :
    padicValRat 2 ((2 : ℚ) ^ n) = (n : ℤ) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (p := 2) (by decide)
  rw [padicValRat.pow, hv, mul_one]

theorem valuation_of_ratio (α : ℕ → ℚ) (ha : ∀ n, α (n + 2) = 4 * ratio n) (n : ℕ) :
    padicValRat 2 (α (n + 2)) =
      2 + padicValRat 2 (c (n + 2)) + padicValRat 2 (c n) -
        padicValRat 2 (c (n + 1)) - padicValRat 2 (1 + c (n + 1)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : padicValRat 2 (4 : ℚ) = 2 := by
    rw [show (4 : ℚ) = 2 ^ (2 : ℕ) by norm_num, valuation_two_pow]
    norm_num
  rw [ha n, padicValRat.mul (by norm_num : (4 : ℚ) ≠ 0) (ratio_pos n).ne', h4]
  unfold ratio
  rw [padicValRat.div (mul_ne_zero (c_ne_zero _) (c_ne_zero _))
        (mul_ne_zero (c_ne_zero _) (one_add_c_ne_zero _)),
      padicValRat.mul (c_ne_zero _) (c_ne_zero _),
      padicValRat.mul (c_ne_zero _) (one_add_c_ne_zero _)]
  omega

/-- The only external assumptions are the valuation words for the explicit A276175 sequence. -/
theorem bounds_of_words (α : ℕ → ℚ)
    (ha0 : α 0 = 2) (ha1 : α 1 = 16) (ha2 : α 2 = 2) (ha3 : α 3 = 2)
    (hstep : ∀ n, α (n + 4) = (α (n + 3) * α (n + 2) * α (n + 1) + 64) / (4 * α n))
    (hw : ∀ n, padicValRat 2 (c n) = w n)
    (ht : ∀ n, padicValRat 2 (1 + c n) = t n) (n : ℕ) :
    0 ≤ padicValRat 2 (α n) ∧ padicValRat 2 (α n) < 6 := by
  obtain (_ | _ | n) := n
  · rw [ha0, show (2 : ℚ) = 2 ^ (1 : ℕ) by norm_num, valuation_two_pow]
    norm_num
  · rw [ha1, show (16 : ℚ) = 2 ^ (4 : ℕ) by norm_num, valuation_two_pow]
    norm_num
  · rw [valuation_of_ratio α (alpha_eq_four_mul_ratio α ha0 ha1 ha2 ha3 hstep) n, hw, hw, hw, ht]
    exact transferWord_bounds n

/-- For a nonzero dyadic rational, valuation in `[0,6)` gives an integral value
whose representative is not divisible by 64. -/
theorem integer_of_dyadic_valuation (q : ℚ) (hq : q ≠ 0)
    (hdyadic : ∃ (a : ℤ) (k : ℕ), q = (a : ℚ) / 2 ^ k)
    (hlo : 0 ≤ padicValRat 2 q) (hhi : padicValRat 2 q < 6) :
    ∃ z : ℤ, q = z ∧ ¬ 64 ∣ z := by
  obtain ⟨a, k, ha⟩ := hdyadic
  have ha0 : (a : ℚ) ≠ 0 := by
    intro hz
    exact hq (by rw [ha, hz, zero_div])
  have htwo : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by decide : 1 < 2)
  have hv := hlo
  rw [ha, padicValRat.div ha0 (by positivity), padicValRat.pow, htwo, mul_one,
    padicValRat.of_int] at hv
  have hdiv : (2 : ℤ)^k ∣ a :=
    (padicValInt_dvd_iff (p := 2) k a).mpr (Or.inr (by omega))
  obtain ⟨z, hz⟩ := hdiv
  have hqz : q = (z : ℚ) := by
    rw [ha, hz]
    push_cast
    field_simp
  refine ⟨z, hqz, ?_⟩
  intro hd
  have hpow : (2 : ℤ)^6 ∣ z := by norm_num; exact hd
  have hz0 : z ≠ 0 := by
    intro h
    exact hq (by rw [hqz, h, Int.cast_zero])
  have v := ((padicValInt_dvd_iff (p := 2) 6 z).mp hpow).resolve_left hz0
  rw [hqz, padicValRat.of_int] at hhi
  omega

/-- The four consecutive values at a block boundary are all 1 modulo 16 in ℤ₂.
The first alternative includes exact equality because `padicValRat 2 0 = 0`. -/
def inTube (n : ℕ) : Prop :=
  ∀ i : Fin 4, c (n + i) = 1 ∨ 4 ≤ padicValRat 2 (c (n + i) - 1)

theorem initial_tube : inTube 0 := by
  intro i
  fin_cases i <;> exact Or.inl rfl

/-- The single-block assertion targeted by the finite polynomial computation.
At any visit to the tube the valuation readings match Sil's two words and the
four values at the next block boundary belong to the same tube. -/
def blockReturn : Prop :=
  ∀ n : ℕ, inTube n → inTube (n + 44) ∧
    ∀ j : Fin 44, padicValRat 2 (c (n + j)) = wWord j ∧
      padicValRat 2 (1 + c (n + j)) = tWord j

/-- Iterating a verified block would propagate both valuations to every index. -/
theorem valuation_words_of_block (hblock : blockReturn) (n : ℕ) :
    padicValRat 2 (c n) = w n ∧ padicValRat 2 (1 + c n) = t n := by
  have hwindow (q : ℕ) : inTube (44 * q) := by
    induction q with
    | zero => exact initial_tube
    | succ q ih =>
      rw [Nat.mul_succ]
      exact (hblock (44 * q) ih).1
  have idx : 44 * (n / 44) + n % 44 = n :=
    (Nat.add_comm _ _).trans (Nat.mod_add_div n 44)
  have h := (hblock (44 * (n / 44)) (hwindow _)).2 ⟨n % 44, Nat.mod_lt n (by decide)⟩
  change padicValRat 2 (c (44 * (n / 44) + n % 44)) = w n ∧
    padicValRat 2 (1 + c (44 * (n / 44) + n % 44)) = t n at h
  rwa [idx] at h

/-- Sil's 44-step return and its valuation readings imply both conjectures
in the exact A362884 statement. The block is the remaining formalization. -/
theorem main_of_block_return (hblock : blockReturn) : type_of% @OMA.S_oeis_a362884.main := by
  intro n
  have hv := bounds_of_words a rfl rfl rfl rfl (fun _ => rfl)
    (fun k => (valuation_words_of_block hblock k).1)
    (fun k => (valuation_words_of_block hblock k).2) n
  exact integer_of_dyadic_valuation (a n) (a_positive n).ne' (a_dyadic n) hv.1 hv.2

end A362884
