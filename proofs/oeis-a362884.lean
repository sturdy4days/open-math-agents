import OMAStatements.S_oeis_a362884

/-!
# Integrality and the bound on powers of two in OEIS A362884

Rescale the recurrence by four. Mercio's eight-step polynomial identity puts
every term in the dyadic rationals. The product relation with A276175 then
expresses the 2-adic valuation in terms of Sil's two period-44 words.

We prove those words here by following four 11-step blocks. At the start of
each block the four successive terms of A276175 lie in specified residue
classes modulo 8, 16, 16, and 8. Sparse polynomials in four variables track
the normalized terms at finite precision. The kernel checks the coefficients
of each recurrence identity and the four return conditions. Iterating the
blocks bounds the valuation of every A362884 term between 0 and 5.

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

end A362884

/-! Kernel-checkable sparse polynomial identities in four variables over `ZMod m`. -/

namespace SparseResidual

structure Powers where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  deriving DecidableEq

structure Term where
  powers : Powers
  coeff : ℤ

abbrev Poly := List Term
abbrev Point (m : ℕ) := ZMod m × ZMod m × ZMod m × ZMod m

def term (a b c d : ℕ) (coeff : ℤ) : Term := ⟨⟨a, b, c, d⟩, coeff⟩

def evalPowers {m : ℕ} (x : Point m) (e : Powers) : ZMod m :=
  x.1 ^ e.a * x.2.1 ^ e.b * x.2.2.1 ^ e.c * x.2.2.2 ^ e.d

def evalTerm {m : ℕ} (x : Point m) (t : Term) : ZMod m :=
  (t.coeff : ZMod m) * evalPowers x t.powers

def eval {m : ℕ} (x : Point m) : Poly → ZMod m
  | [] => 0
  | t :: ts => evalTerm x t + eval x ts

theorem eval_append {m : ℕ} (x : Point m) (p q : Poly) :
    eval x (p ++ q) = eval x p + eval x q := by
  induction p with
  | nil => simp [eval]
  | cons t ts ih => simp only [List.cons_append, eval, ih, add_assoc]

def consReduced (m : ℕ) (e : Powers) (c : ℤ) (p : Poly) : Poly :=
  let r := c % (m : ℤ)
  if r = 0 then p else ⟨e, r⟩ :: p

theorem eval_consReduced {m : ℕ} (x : Point m) (e : Powers) (c : ℤ) (p : Poly) :
    eval x (consReduced m e c p) = (c : ZMod m) * evalPowers x e + eval x p := by
  by_cases h : c % (m : ℤ) = 0
  · have hcast : (c : ZMod m) = 0 := by rw [← ZMod.intCast_mod c m, h, Int.cast_zero]
    simp [consReduced, h, hcast]
  · simp [consReduced, h, eval, evalTerm, ZMod.intCast_mod]

def insertTerm (m : ℕ) (t : Term) : Poly → Poly
  | [] => consReduced m t.powers t.coeff []
  | u :: us =>
    if t.powers = u.powers then consReduced m u.powers (t.coeff + u.coeff) us
    else u :: insertTerm m t us

theorem eval_insertTerm {m : ℕ} (x : Point m) (t : Term) (p : Poly) :
    eval x (insertTerm m t p) = evalTerm x t + eval x p := by
  induction p with
  | nil => simp only [insertTerm, eval_consReduced, evalTerm]
  | cons u us ih =>
    by_cases h : t.powers = u.powers
    · simp only [insertTerm, h, if_true, eval_consReduced, evalTerm, eval, Int.cast_add,
        add_mul, add_assoc]
    · simp only [insertTerm, h, if_false, eval, ih]
      ac_rfl

def normalize (m : ℕ) : Poly → Poly
  | [] => []
  | t :: ts => insertTerm m t (normalize m ts)

theorem eval_normalize {m : ℕ} (x : Point m) (p : Poly) :
    eval x (normalize m p) = eval x p := by
  induction p with
  | nil => rfl
  | cons t ts ih => rw [normalize, eval_insertTerm, ih, eval]

def neg (p : Poly) : Poly := p.map fun t => ⟨t.powers, -t.coeff⟩

theorem eval_neg {m : ℕ} (x : Point m) (p : Poly) : eval x (neg p) = -eval x p := by
  induction p with
  | nil => simp [neg, eval]
  | cons t ts ih =>
    change evalTerm x ⟨t.powers, -t.coeff⟩ + eval x (neg ts) =
      -(evalTerm x t + eval x ts)
    rw [ih]
    simp only [evalTerm, Int.cast_neg, neg_mul, neg_add_rev]
    exact add_comm _ _

def eqCheck (m : ℕ) (p q : Poly) : Bool := (normalize m (p ++ neg q)).isEmpty

theorem eval_eq_of_check {m : ℕ} {p q : Poly} (x : Point m) (h : eqCheck m p q = true) :
    eval x p = eval x q := by
  have hnil : normalize m (p ++ neg q) = [] := List.isEmpty_iff.mp h
  have hz : eval x (normalize m (p ++ neg q)) = 0 := by rw [hnil, eval]
  rw [eval_normalize, eval_append, eval_neg, ← sub_eq_add_neg, sub_eq_zero] at hz
  exact hz

def addPowers (x y : Powers) : Powers := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩

def termMul (m : ℕ) (t u : Term) : Term :=
  ⟨addPowers t.powers u.powers, (t.coeff * u.coeff) % (m : ℤ)⟩

theorem eval_termMul {m : ℕ} (x : Point m) (t u : Term) :
    evalTerm x (termMul m t u) = evalTerm x t * evalTerm x u := by
  simp only [termMul, evalTerm, addPowers, evalPowers, ZMod.intCast_mod, Int.cast_mul, pow_add]
  ac_rfl

def mul (m : ℕ) (p q : Poly) : Poly := p.flatMap fun t => q.map (termMul m t)

theorem eval_mul {m : ℕ} (x : Point m) (p q : Poly) :
    eval x (mul m p q) = eval x p * eval x q := by
  have hm (t : Term) : eval x (q.map (termMul m t)) = evalTerm x t * eval x q := by
    induction q with
    | nil => simp [eval]
    | cons u us ih => simp only [List.map_cons, eval, eval_termMul, ih, mul_add]
  induction p with
  | nil => simp [mul, eval]
  | cons t ts ih =>
    change eval x (q.map (termMul m t) ++ mul m ts q) =
      (evalTerm x t + eval x ts) * eval x q
    rw [eval_append, hm, ih, add_mul]

def constant (c : ℤ) : Poly := [term 0 0 0 0 c]

theorem eval_constant {m : ℕ} (x : Point m) (c : ℤ) :
    eval x (constant c) = c := by
  simp [constant, term, eval, evalTerm, evalPowers]

end SparseResidual

namespace A362884Sound

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev K := ℚ_[2]
abbrev O := ℤ_[2]

/-- `x − y` is divisible by `2^prec` in the 2-adic integers. -/
def Close (prec : ℕ) (x y : K) : Prop :=
  ∃ e : O, x - y = (2 : K) ^ prec * (e : K)

theorem close_of_residue_eq {prec : ℕ} {x y : O}
    (h : PadicInt.toZModPow prec x = PadicInt.toZModPow prec y) :
    Close prec (x : K) (y : K) := by
  have hmem : x - y ∈ RingHom.ker (PadicInt.toZModPow prec) := by
    rw [RingHom.mem_ker, map_sub, h, sub_self]
  rw [PadicInt.ker_toZModPow] at hmem
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp hmem
  exact ⟨e, congrArg (fun z : O => (z : K)) he⟩

theorem Close.symm {prec : ℕ} {x y : K} (h : Close prec x y) : Close prec y x := by
  obtain ⟨e, he⟩ := h
  refine ⟨-e, ?_⟩
  rw [PadicInt.coe_neg, ← neg_sub, he, mul_neg]

theorem Close.trans {prec : ℕ} {x y z : K} (hxy : Close prec x y) (hyz : Close prec y z) :
    Close prec x z := by
  obtain ⟨e, he⟩ := hxy
  obtain ⟨f, hf⟩ := hyz
  refine ⟨e + f, ?_⟩
  rw [PadicInt.coe_add, mul_add, ← he, ← hf]
  ring

theorem Close.weaken {p q : ℕ} {x y : K} (hpq : p ≤ q) (h : Close q x y) :
    Close p x y := by
  obtain ⟨e, he⟩ := h
  refine ⟨(2 : O) ^ (q - p) * e, ?_⟩
  rw [he, PadicInt.coe_mul, PadicInt.coe_pow]
  change (2 : K) ^ q * (e : K) = 2 ^ p * (2 ^ (q - p) * (e : K))
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hpq]

theorem Close.mul {prec : ℕ} {a b x y : K}
    (hax : Close prec a x) (hby : Close prec b y) (hb : ‖b‖ ≤ 1) (hx : ‖x‖ ≤ 1) :
    Close prec (a * b) (x * y) := by
  obtain ⟨e, he⟩ := hax
  obtain ⟨f, hf⟩ := hby
  refine ⟨e * ⟨b, hb⟩ + ⟨x, hx⟩ * f, ?_⟩
  change a * b - x * y = (2 : K)^prec * ((e : K) * b + x * (f : K))
  calc
    _ = (a - x) * b + x * (b - y) := by ring
    _ = _ := by rw [he, hf]; ring

theorem integral_mul {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ hx (norm_nonneg _) hy

theorem norm_two : ‖(2 : K)‖ = (2 : ℝ)⁻¹ := Padic.norm_p (p := 2)

theorem norm_two_pow_le_one (prec : ℕ) : ‖(2 : K) ^ prec‖ ≤ 1 := by
  rw [norm_pow, norm_two]
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem Close.integral {prec : ℕ} {x y : K} (h : Close prec x y) (hy : ‖y‖ ≤ 1) :
    ‖x‖ ≤ 1 := by
  obtain ⟨e, he⟩ := h
  have he1 : ‖(2 : K) ^ prec * (e : K)‖ ≤ 1 :=
    integral_mul (norm_two_pow_le_one _) e.2
  have hx : x = y + (2 : K) ^ prec * (e : K) := by
    calc x = y + (x - y) := by ring
         _ = _ := by rw [he]
  rw [hx]
  exact (Padic.nonarchimedean _ _).trans (max_le_iff.mpr ⟨hy, he1⟩)

theorem Close.unit {prec : ℕ} {x y : K} (h : Close prec x y) (hp : 1 ≤ prec)
    (hy : ‖y‖ = 1) : ‖x‖ = 1 := by
  obtain ⟨e, he⟩ := h.weaken hp
  have hlt : ‖x - y‖ < ‖y‖ := by
    rw [he, pow_one, norm_mul, norm_two, hy]
    calc
      _ ≤ (2 : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left e.2 (by norm_num)
      _ < 1 := by norm_num
  exact (Padic.norm_eq_of_norm_sub_lt_right hlt).trans hy

theorem Close.cancel_left {prec : ℕ} {a x y : K} (h : Close prec (a * x) (a * y))
    (ha : ‖a‖ = 1) : Close prec x y := by
  obtain ⟨e, he⟩ := h
  have ha0 : a ≠ 0 := by intro hz; simp [hz] at ha
  have hai : ‖a⁻¹‖ ≤ 1 := by simp [norm_inv, ha]
  refine ⟨⟨a⁻¹, hai⟩ * e, ?_⟩
  change x - y = (2 : K)^prec * (a⁻¹ * (e : K))
  have hd : a * (x - y) = (2 : K)^prec * (e : K) := by rwa [mul_sub]
  calc
    _ = a⁻¹ * (a * (x - y)) := by rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
    _ = _ := by rw [hd]; ring

theorem Close.mul_right {prec : ℕ} {x y a : K} (h : Close prec x y) (ha : ‖a‖ ≤ 1) :
    Close prec (x * a) (y * a) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e * ⟨a, ha⟩, ?_⟩
  change x * a - y * a = (2 : K) ^ prec * ((e : K) * a)
  rw [← sub_mul, he, mul_assoc]

theorem Close.add_same_left {prec : ℕ} {x y : K} (h : Close prec x y) (a : K) :
    Close prec (a + x) (a + y) := by
  simpa [Close, add_sub_add_left_eq_sub] using h

theorem Close.shift_mul {prec : ℕ} {x y : K} (h : Close prec x y) (k : ℕ) :
    Close (k + prec) ((2 : K) ^ k * x) ((2 : K) ^ k * y) := by
  obtain ⟨e, he⟩ := h
  exact ⟨e, by rw [← mul_sub, he, pow_add, mul_assoc]⟩

theorem Close.unshift_mul {prec k : ℕ} {x y : K}
    (h : Close (k + prec) ((2 : K) ^ k * x) ((2 : K) ^ k * y)) : Close prec x y := by
  obtain ⟨e, he⟩ := h
  rw [← mul_sub, pow_add, mul_assoc] at he
  exact ⟨e, mul_left_cancel₀ (pow_ne_zero k (by norm_num)) he⟩

theorem factor_close {prec input w t : ℕ} {u r s v : K}
    (hinput : Close input u r) (hprec : t + prec ≤ w + input)
    (hjet : 1 + (2 : K) ^ w * r = (2 : K) ^ t * s)
    (hv : (2 : K) ^ t * v = 1 + (2 : K) ^ w * u) : Close prec v s := by
  have h := ((hinput.shift_mul w).weaken hprec).add_same_left 1
  rw [← hv, hjet] at h
  exact h.unshift_mul

theorem step {prec : ℕ} {u0 u4 v1 v2 v3 r0 r4 s1 s2 s3 : K}
    (hstep : u0 * u4 = v1 * v2 * v3)
    (hcert : Close prec (r0 * r4) (s1 * s2 * s3)) (hu0 : ‖u0‖ = 1)
    (h0 : Close prec u0 r0) (h1 : Close prec v1 s1) (h2 : Close prec v2 s2)
    (h3 : Close prec v3 s3) (hr4 : ‖r4‖ ≤ 1)
    (hs1 : ‖s1‖ ≤ 1) (hs2 : ‖s2‖ ≤ 1) (hs3 : ‖s3‖ ≤ 1) : Close prec u4 r4 := by
  have h12 := h1.mul h2 (h2.integral hs2) hs1
  have h123 := h12.mul h3 (h3.integral hs3) (integral_mul hs1 hs2)
  rw [← hstep] at h123
  exact ((h123.trans hcert.symm).trans (h0.mul_right hr4).symm).cancel_left hu0

theorem norm_one_of_residue_one {x : O} (h : PadicInt.toZModPow 1 x = 1) : ‖(x : K)‖ = 1 := by
  have hc : Close 1 (x : K) 1 := close_of_residue_eq (y := 1) (by simpa using h)
  exact hc.unit (by decide) norm_one

noncomputable def normalized (q : ℚ) (w : ℕ) : K := (q : K) / (2 : K) ^ w

theorem scale_normalized (q : ℚ) (w : ℕ) : (2 : K) ^ w * normalized q w = (q : K) := by
  rw [normalized, mul_comm, div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num))]

theorem normalized_step {w0 w4 t1 t2 t3 : ℕ} {q0 q1 q2 q3 q4 : ℚ}
    (hs : q0 * q4 = (1 + q1) * (1 + q2) * (1 + q3))
    (hw : w0 + w4 = t1 + t2 + t3) :
    normalized q0 w0 * normalized q4 w4 =
      normalized (1 + q1) t1 * normalized (1 + q2) t2 * normalized (1 + q3) t3 := by
  apply mul_left_cancel₀ (pow_ne_zero (w0 + w4) (by norm_num : (2 : K) ≠ 0))
  calc
    (2 : K) ^ (w0 + w4) * (normalized q0 w0 * normalized q4 w4) =
        ((2 : K) ^ w0 * normalized q0 w0) * ((2 : K) ^ w4 * normalized q4 w4) := by
          rw [pow_add]; ring
    _ = (((1 + q1) * (1 + q2) * (1 + q3) : ℚ) : K) := by simp only [scale_normalized, Rat.cast_mul, ← hs]
    _ = ((2 : K) ^ t1 * normalized (1 + q1) t1) *
        ((2 : K) ^ t2 * normalized (1 + q2) t2) *
        ((2 : K) ^ t3 * normalized (1 + q3) t3) := by simp only [scale_normalized, Rat.cast_mul]
    _ = _ := by rw [hw, pow_add, pow_add]; ring

theorem normalized_factor {prec input w t : ℕ} {q : ℚ} {j f : O}
    (hinput : Close input (normalized q w) (j : K)) (hprec : t + prec ≤ w + input)
    (hf : 1 + (2 : O) ^ w * j = (2 : O) ^ t * f) :
    Close prec (normalized (1 + q) t) (f : K) := by
  apply factor_close hinput hprec (congrArg (fun z : O => (z : K)) hf)
  rw [scale_normalized, scale_normalized, Rat.cast_add, Rat.cast_one]

theorem jet_step {p0 p1 p2 p3 p4 w0 w1 w2 w3 w4 t1 t2 t3 : ℕ}
    {q0 q1 q2 q3 q4 : ℚ} {j0 j1 j2 j3 j4 f1 f2 f3 : O}
    (hp : 0 < p4) (hs : q0 * q4 = (1 + q1) * (1 + q2) * (1 + q3))
    (hw : w0 + w4 = t1 + t2 + t3)
    (hp0 : p4 ≤ p0) (hp1 : t1 + p4 ≤ w1 + p1) (hp2 : t2 + p4 ≤ w2 + p2)
    (hp3 : t3 + p4 ≤ w3 + p3) (hj0 : PadicInt.toZModPow 1 j0 = 1)
    (h0 : Close p0 (normalized q0 w0) (j0 : K))
    (h1 : Close p1 (normalized q1 w1) (j1 : K))
    (h2 : Close p2 (normalized q2 w2) (j2 : K))
    (h3 : Close p3 (normalized q3 w3) (j3 : K))
    (hf1 : 1 + (2 : O) ^ w1 * j1 = (2 : O) ^ t1 * f1)
    (hf2 : 1 + (2 : O) ^ w2 * j2 = (2 : O) ^ t2 * f2)
    (hf3 : 1 + (2 : O) ^ w3 * j3 = (2 : O) ^ t3 * f3)
    (hres : PadicInt.toZModPow p4 (j0 * j4) = PadicInt.toZModPow p4 (f1 * f2 * f3)) :
    Close p4 (normalized q4 w4) (j4 : K) := by
  exact step (normalized_step hs hw) (close_of_residue_eq hres)
    ((h0.weaken hp0).unit hp (norm_one_of_residue_one hj0)) (h0.weaken hp0)
    (normalized_factor h1 hp1 hf1) (normalized_factor h2 hp2 hf2)
    (normalized_factor h3 hp3 hf3) j4.2 f1.2 f2.2 f3.2

theorem valuation_two : Padic.valuation (2 : K) = 1 := Padic.valuation_p (p := 2)

theorem valuation_of_norm_one {x : K} (hx : ‖x‖ = 1) : x.valuation = 0 := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hpow : (2 : ℝ) ^ (-x.valuation) = (2 : ℝ) ^ (0 : ℤ) := by
    simpa using (Padic.norm_eq_zpow_neg_valuation hx0).symm.trans hx
  have hneg := (zpow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).injective hpow
  omega

theorem valuation_of_unit_scaled (q : ℚ) (w : ℕ) (u : K)
    (hq : (q : K) = (2 : K) ^ w * u) (hu : ‖u‖ = 1) : padicValRat 2 q = (w : ℤ) := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  rw [← Padic.valuation_ratCast, hq, Padic.valuation_mul (pow_ne_zero _ (by norm_num)) hu0,
    Padic.valuation_pow, valuation_two, valuation_of_norm_one hu, mul_one, add_zero]

theorem reading {prec w : ℕ} {q : ℚ} {u r : K}
    (hq : (q : K) = (2 : K) ^ w * u) (hc : Close prec u r) (hp : 0 < prec)
    (hr : ‖r‖ = 1) : padicValRat 2 q = (w : ℤ) :=
  valuation_of_unit_scaled q w u hq (hc.unit hp hr)

theorem jet_reading {prec w : ℕ} {q : ℚ} {j : O} (hp : 0 < prec)
    (hc : Close prec (normalized q w) (j : K)) (hj : PadicInt.toZModPow 1 j = 1) :
    padicValRat 2 q = (w : ℤ) :=
  reading (scale_normalized q w).symm hc hp (norm_one_of_residue_one hj)

theorem factor_reading {input w t : ℕ} {q : ℚ} {j f : O}
    (hc : Close input (normalized q w) (j : K)) (hp : t + 1 ≤ w + input)
    (hf : 1 + (2 : O) ^ w * j = (2 : O) ^ t * f) (hf1 : PadicInt.toZModPow 1 f = 1) :
    padicValRat 2 (1 + q) = (t : ℤ) :=
  jet_reading (by decide : 0 < 1) (normalized_factor hc hp hf) hf1

end A362884Sound

namespace A362884Endpoint

open A362884Sound (Close K O)

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- A residue of a certified approximation gives the exact output tube witness. -/
theorem witness_of_close_residue {p d center : ℕ} {q : K} {J : O}
    (hclose : Close p q (J : K)) (hle : d ≤ p)
    (hres : PadicInt.toZModPow d J = (center : ZMod (2 ^ d))) :
    ∃ x : O, q = (center : K) + (2 : K) ^ d * (x : K) := by
  have hj : Close d (J : K) ((center : O) : K) :=
    A362884Sound.close_of_residue_eq (by simpa only [map_natCast] using hres)
  obtain ⟨x, hx⟩ := (hclose.weaken hle).trans hj
  refine ⟨x, ?_⟩
  rw [PadicInt.coe_natCast] at hx
  exact (sub_eq_iff_eq_add.mp hx).trans (add_comm _ _)

/-- The initial linear expression can be reduced to a finite jet at any precision. -/
theorem close_of_input_residue {p d center : ℕ} {q : K} {X J : O}
    (hq : q = (center : K) + (2 : K) ^ d * (X : K))
    (hres : PadicInt.toZModPow p J =
      (center : ZMod (2 ^ p)) + (2 : ZMod (2 ^ p)) ^ d * PadicInt.toZModPow p X) :
    Close p q (J : K) := by
  let z : O := (center : O) + (2 : O) ^ d * X
  have htwo : ((2 : O) : K) = (2 : K) := PadicInt.coe_natCast 2
  have hz : q = (z : K) := by
    simpa only [z, PadicInt.coe_add, PadicInt.coe_natCast, PadicInt.coe_mul,
      PadicInt.coe_pow, htwo] using hq
  rw [hz]
  apply A362884Sound.close_of_residue_eq
  simpa only [z, map_add, map_mul, map_pow, map_natCast, map_ofNat] using hres.symm

/-- Without truncation the initial linear expression is an exact jet. -/
theorem close_of_input_eq {p d center : ℕ} {q : K} {X : O}
    (hq : q = (center : K) + (2 : K) ^ d * (X : K)) :
    Close p q (((center : O) + (2 : O) ^ d * X : O) : K) := by
  exact close_of_input_residue hq (by simp only [map_add, map_mul, map_pow, map_natCast, map_ofNat])

end A362884Endpoint

/-! The four 11-step certificates for the A276175 valuation words. -/

namespace A362884Cert

open SparseResidual

def radius : Fin 4 → ℕ := ![3, 4, 4, 3]
def center : Fin 4 → Fin 4 → ℕ :=
  ![![1, 1, 1, 1], ![3, 9, 5, 1], ![3, 13, 13, 3], ![1, 5, 9, 3]]

def W (b : Fin 4) (i : ℕ) : ℕ := (A362884.w (11 * b.val + i)).toNat
def T (b : Fin 4) (i : ℕ) : ℕ := (A362884.t (11 * b.val + i)).toNat

/-- Number of bits required for each of the fifteen values in a block. -/
def P (b : Fin 4) (i : ℕ) : ℕ :=
  (([
    [7, 8, 9, 10, 7, 8, 9, 10, 5, 4, 3, 7, 5, 4, 3],
    [7, 8, 9, 10, 7, 8, 9, 10, 5, 4, 3, 7, 5, 4, 3],
    [6, 7, 8, 10, 6, 7, 8, 10, 5, 4, 3, 6, 5, 4, 3],
    [6, 7, 8, 10, 6, 7, 8, 10, 5, 4, 3, 6, 5, 4, 3]] : List (List ℕ))[b.val]?.getD [])[i]?.getD 0

/-- Each row stores the four starting values followed by eleven recurrence
updates. A term lists the exponents of its four variables, then its coefficient. -/
def jPoly (b : Fin 4) (i : ℕ) : SparseResidual.Poly :=
  (([
    -- Block beginning at residue 0
    [
      [term 0 0 0 0 1, term 1 0 0 0 8],
      [term 0 0 0 0 1, term 0 1 0 0 16],
      [term 0 0 0 0 1, term 0 0 1 0 16],
      [term 0 0 0 0 1, term 0 0 0 1 8],
      [term 0 0 0 0 1, term 1 0 0 0 120, term 2 0 0 0 64, term 0 0 0 1 4,
        term 1 0 0 1 96, term 0 0 1 0 8, term 1 0 1 0 64, term 0 0 1 1 32,
        term 0 1 0 0 8, term 1 1 0 0 64, term 0 1 0 1 32, term 0 1 1 0 64],
      [term 0 0 0 0 9, term 0 1 0 0 176, term 1 0 0 0 192, term 0 0 0 1 68,
        term 0 1 0 1 192, term 0 0 1 0 136, term 0 1 1 0 128, term 0 0 0 2 128,
        term 0 0 1 1 32],
      [term 0 0 0 0 333, term 0 0 1 0 400, term 0 0 2 0 256, term 1 0 0 0 448,
        term 0 0 0 1 356, term 0 0 1 1 192, term 0 0 0 2 192],
      [term 0 0 0 0 927, term 0 0 0 1 64, term 0 0 0 2 768, term 0 0 1 0 704,
        term 0 0 1 1 768, term 0 0 2 0 512, term 1 0 0 0 192, term 1 0 0 1 256,
        term 0 1 0 0 512, term 2 0 0 0 512, term 1 0 1 0 512, term 1 1 0 0 512],
      [term 0 0 0 0 11, term 0 0 0 1 26, term 0 0 1 0 2, term 0 1 0 0 24,
        term 0 0 0 2 16, term 1 0 0 0 2, term 0 1 0 1 16, term 1 0 0 1 16,
        term 0 1 1 0 16, term 1 0 1 0 16],
      [term 0 0 0 0 11, term 0 0 0 1 2, term 0 0 1 0 10, term 1 0 0 0 2],
      [term 0 0 0 0 5, term 0 0 0 1 6, term 0 0 1 0 6, term 1 0 0 0 6],
      [term 0 0 0 0 43, term 0 0 0 1 104, term 0 0 1 0 8, term 1 0 0 0 72,
        term 0 1 0 0 32, term 0 0 0 2 64, term 0 1 0 1 64, term 1 0 0 1 64,
        term 0 1 1 0 64, term 1 0 1 0 64],
      [term 0 0 0 0 9, term 0 0 0 1 16, term 0 0 1 0 16, term 0 1 0 0 16],
      [term 0 0 0 0 5],
      [term 0 0 0 0 1]
    ],
    -- Block beginning at residue 11
    [
      [term 0 0 0 0 3, term 1 0 0 0 8],
      [term 0 0 0 0 9, term 0 1 0 0 16],
      [term 0 0 0 0 5, term 0 0 1 0 16],
      [term 0 0 0 0 1, term 0 0 0 1 8],
      [term 0 0 0 0 5, term 1 0 0 0 72, term 2 0 0 0 64, term 0 0 0 1 20,
        term 1 0 0 1 32, term 0 0 1 0 56, term 1 0 1 0 64, term 0 0 1 1 96,
        term 0 1 0 0 8, term 1 1 0 0 64, term 0 1 0 1 32, term 0 1 1 0 64],
      [term 0 0 0 0 99, term 0 1 0 0 16, term 1 0 0 0 192, term 0 0 0 1 108,
        term 0 1 0 1 64, term 0 0 1 0 72, term 0 1 1 0 128, term 0 0 0 2 128,
        term 0 0 1 1 32],
      [term 0 0 0 0 81, term 0 0 1 0 400, term 0 0 2 0 256, term 0 1 0 0 384,
        term 1 0 0 0 320, term 0 0 0 1 84, term 0 0 1 1 192, term 0 0 0 2 64],
      [term 0 0 0 0 991, term 0 0 0 1 192, term 0 0 0 2 256, term 0 0 1 0 64,
        term 0 0 1 1 256, term 0 0 2 0 512, term 0 1 0 0 896, term 1 0 0 0 320,
        term 1 0 0 1 768, term 0 1 0 1 512, term 2 0 0 0 512, term 1 0 1 0 512,
        term 1 1 0 0 512],
      [term 0 0 0 0 5, term 1 0 0 0 6, term 0 1 0 0 12, term 0 0 0 2 16,
        term 0 0 0 1 22, term 0 0 1 0 30, term 1 0 0 1 16, term 0 1 1 0 16,
        term 0 1 0 1 16, term 1 0 1 0 16],
      [term 0 0 0 0 11, term 0 0 0 1 2, term 0 0 1 0 10, term 1 0 0 0 10,
        term 0 1 0 0 12],
      [term 0 0 0 0 3, term 0 0 0 1 2, term 0 0 1 0 2, term 0 1 0 0 4,
        term 1 0 0 0 2],
      [term 0 0 0 0 99, term 0 0 0 1 56, term 0 0 1 0 88, term 1 0 0 0 56,
        term 0 1 0 0 48, term 0 0 0 2 64, term 1 0 0 1 64, term 0 1 1 0 64,
        term 0 1 0 1 64, term 1 0 1 0 64],
      [term 0 0 0 0 13, term 0 0 1 0 16, term 0 1 0 0 16, term 0 0 0 1 16],
      [term 0 0 0 0 13],
      [term 0 0 0 0 3]
    ],
    -- Block beginning at residue 22
    [
      [term 0 0 0 0 3, term 1 0 0 0 8],
      [term 0 0 0 0 13, term 0 1 0 0 16],
      [term 0 0 0 0 13, term 0 0 1 0 16],
      [term 0 0 0 0 3, term 0 0 0 1 8],
      [term 0 0 0 0 59, term 1 0 0 0 56, term 0 0 0 1 54, term 1 0 0 1 48,
        term 0 0 1 0 40, term 0 0 1 1 16, term 0 1 0 0 40, term 0 1 0 1 16],
      [term 0 0 0 0 115, term 0 1 0 0 16, term 0 0 0 1 6, term 0 1 0 1 32,
        term 0 0 0 2 64, term 0 0 1 0 40, term 0 0 1 1 80],
      [term 0 0 0 0 173, term 0 0 1 0 176, term 0 0 0 1 42, term 0 0 1 1 224,
        term 1 0 0 0 128, term 0 0 0 2 160],
      [term 0 0 0 0 607, term 0 0 0 1 320, term 0 0 0 2 256, term 0 0 1 0 640,
        term 0 0 1 1 256, term 1 0 0 0 640, term 0 1 0 0 256, term 0 1 0 1 512,
        term 1 0 0 1 256],
      [term 0 0 0 0 21, term 0 0 0 1 20, term 0 0 1 0 20, term 1 0 0 0 4],
      [term 0 0 0 0 7, term 0 0 0 1 4, term 0 0 1 0 4, term 1 0 0 0 12,
        term 0 1 0 0 8],
      [term 0 0 0 0 1, term 0 0 0 1 4, term 0 0 1 0 4, term 1 0 0 0 4],
      [term 0 0 0 0 9, term 0 0 0 1 40, term 0 0 1 0 40, term 1 0 0 0 40,
        term 0 1 0 0 32],
      [term 0 0 0 0 21, term 0 0 0 1 16, term 0 0 1 0 16, term 0 1 0 0 16],
      [term 0 0 0 0 9],
      [term 0 0 0 0 3]
    ],
    -- Block beginning at residue 33
    [
      [term 0 0 0 0 1, term 1 0 0 0 8],
      [term 0 0 0 0 5, term 0 1 0 0 16],
      [term 0 0 0 0 9, term 0 0 1 0 16],
      [term 0 0 0 0 3, term 0 0 0 1 8],
      [term 0 0 0 0 15, term 1 0 0 0 8, term 0 0 0 1 30, term 1 0 0 1 16,
        term 0 0 1 0 24, term 0 0 1 1 48, term 0 1 0 0 40, term 0 1 0 1 16],
      [term 0 0 0 0 113, term 0 1 0 0 48, term 0 0 0 1 66, term 0 1 0 1 96,
        term 0 0 0 2 64, term 0 0 1 0 104, term 0 0 1 1 80],
      [term 0 0 0 0 113, term 0 0 1 0 48, term 0 0 0 1 82, term 0 0 1 1 224,
        term 1 0 0 0 128, term 0 0 0 2 224],
      [term 0 0 0 0 991, term 0 0 0 1 832, term 0 0 0 2 768, term 0 0 1 0 896,
        term 0 0 1 1 768, term 1 0 0 0 384, term 1 0 0 1 768],
      [term 0 0 0 0 29, term 1 0 0 0 12, term 0 1 0 0 8, term 0 0 0 1 12,
        term 0 0 1 0 12],
      [term 0 0 0 0 9, term 0 0 0 1 4, term 0 0 1 0 4, term 1 0 0 0 12],
      [term 0 0 0 0 1, term 0 0 0 1 4, term 0 0 1 0 4, term 1 0 0 0 4],
      [term 0 0 0 0 33, term 0 0 0 1 56, term 0 0 1 0 56, term 1 0 0 0 24,
        term 0 1 0 0 48],
      [term 0 0 0 0 1, term 0 1 0 0 16, term 0 0 0 1 16, term 0 0 1 0 16],
      [term 0 0 0 0 1],
      [term 0 0 0 0 1]
    ]
  ] : List (List Poly))[b.val]?.getD [])[i]?.getD []

/-- Coefficients of the unit factor (1 + 2^w J) / 2^t.
Every stored jet has exactly one constant coefficient. The equality after
multiplication by 2^t is verified in `factor_data`. -/
def fPoly (b : Fin 4) (i : ℕ) : SparseResidual.Poly :=
  (jPoly b i).map fun u =>
    let offset : ℤ := if u.powers = ⟨0, 0, 0, 0⟩ then 1 else 0
    ⟨u.powers, ((2 : ℤ) ^ W b i * u.coeff + offset) / (2 : ℤ) ^ T b i⟩

def evalRing {R : Type*} [CommRing R] (x : Fin 4 → R) : Poly → R
  | [] => 0
  | ⟨e,c⟩ :: ts => (c:R) * (x 0 ^ e.a * x 1 ^ e.b * x 2 ^ e.c * x 3 ^ e.d) + evalRing x ts

theorem evalRing_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (X : Fin 4 → R) (p : Poly) : φ (evalRing X p) = evalRing (φ ∘ X) p := by
  induction p with
  | nil => exact map_zero φ
  | cons u us ih =>
    rcases u with ⟨e,c⟩
    simp only [evalRing, map_add, map_mul, map_pow, map_intCast, ih, Function.comp_apply]

noncomputable def J (b : Fin 4) (i : ℕ) (X : Fin 4 → ℤ_[2]) : ℤ_[2] := evalRing X (jPoly b i)
noncomputable def F (b : Fin 4) (i : ℕ) (X : Fin 4 → ℤ_[2]) : ℤ_[2] := evalRing X (fPoly b i)

noncomputable def pointMod (p : ℕ) (X : Fin 4 → ℤ_[2]) : Point (2^p) :=
  (PadicInt.toZModPow p (X 0), PadicInt.toZModPow p (X 1),
    PadicInt.toZModPow p (X 2), PadicInt.toZModPow p (X 3))

theorem map_eval (p : ℕ) (X : Fin 4 → ℤ_[2]) (v : Poly) :
    PadicInt.toZModPow p (evalRing X v) = eval (pointMod p X) v := by
  rw [evalRing_map]
  induction v with
  | nil => rfl
  | cons u us ih =>
    rcases u with ⟨e,c⟩
    change _ + evalRing _ us = _ + eval _ us
    rw [ih]
    rfl

theorem map_J (b : Fin 4) (i : ℕ) (X : Fin 4 → ℤ_[2]) (p : ℕ) :
    PadicInt.toZModPow p (J b i X) = eval (pointMod p X) (jPoly b i) := map_eval p X _

theorem map_F (b : Fin 4) (i : ℕ) (X : Fin 4 → ℤ_[2]) (p : ℕ) :
    PadicInt.toZModPow p (F b i X) = eval (pointMod p X) (fPoly b i) := map_eval p X _

end A362884Cert

namespace A362884Cert
open SparseResidual

deriving instance DecidableEq for SparseResidual.Term

private def scale (n : ℕ) (p : Poly) : Poly :=
  p.map fun u => ⟨u.powers, (n : ℤ) * u.coeff⟩

private def addOne : Poly → Poly
  | [] => constant 1
  | u :: us => if u.powers = ⟨0,0,0,0⟩ then ⟨u.powers, 1 + u.coeff⟩ :: us
               else term 0 0 0 0 1 :: u :: us

private theorem eval_scale (X : Fin 4 → ℤ_[2]) (n : ℕ) (p : Poly) :
    evalRing X (scale n p) = n * evalRing X p := by
  induction p with
  | nil => simp [evalRing, scale]
  | cons u us ih =>
    rcases u with ⟨e,c⟩
    change (((n : ℤ) * c : ℤ) : ℤ_[2]) * _ + evalRing X (scale n us) = _ * (_ + _)
    rw [ih, Int.cast_mul, Int.cast_natCast]
    ring

private theorem eval_addOne (X : Fin 4 → ℤ_[2]) (p : Poly) :
    evalRing X (addOne p) = 1 + evalRing X p := by
  cases p with
  | nil => simp [addOne, constant, term, evalRing]
  | cons u us =>
    rcases u with ⟨e,c⟩
    by_cases h : e = ⟨0,0,0,0⟩
    · subst e
      simp [addOne, evalRing, add_assoc]
    · simp [addOne, h, evalRing, term]

set_option maxRecDepth 16000 in
private theorem factor_data : ∀ b : Fin 4, ∀ i : Fin 15,
    addOne (scale (2 ^ W b i) (jPoly b i)) = scale (2 ^ T b i) (fPoly b i) := by decide

theorem factor_eq (b : Fin 4) (i : ℕ) (hi : i < 15) (X : Fin 4 → ℤ_[2]) :
    1 + (2 : ℤ_[2]) ^ W b i * J b i X = (2 : ℤ_[2]) ^ T b i * F b i X := by
  have h := congrArg (evalRing X) (factor_data b ⟨i,hi⟩)
  simpa only [J, F, eval_addOne, eval_scale, Nat.cast_pow, Nat.cast_ofNat] using h

set_option maxRecDepth 16000 in
private theorem parity_data : ∀ b : Fin 4, ∀ i : Fin 15,
    eqCheck 2 (jPoly b i) (constant 1) = true ∧ eqCheck 2 (fPoly b i) (constant 1) = true := by decide

theorem j_odd (b : Fin 4) (i : ℕ) (hi : i < 15) (X : Fin 4 → ℤ_[2]) :
    PadicInt.toZModPow 1 (J b i X) = 1 := by
  rw [map_J]
  exact (eval_eq_of_check (pointMod 1 X) (parity_data b ⟨i,hi⟩).1).trans
    (by simp only [eval_constant, Int.cast_one])

theorem f_odd (b : Fin 4) (i : ℕ) (hi : i < 15) (X : Fin 4 → ℤ_[2]) :
    PadicInt.toZModPow 1 (F b i X) = 1 := by
  rw [map_F]
  exact (eval_eq_of_check (pointMod 1 X) (parity_data b ⟨i,hi⟩).2).trans
    (by simp only [eval_constant, Int.cast_one])

private def axes : Fin 4 → Powers :=
  ![⟨1,0,0,0⟩, ⟨0,1,0,0⟩, ⟨0,0,1,0⟩, ⟨0,0,0,1⟩]

private def affine (c k : ℕ) (i : Fin 4) : Poly :=
  [term 0 0 0 0 c, ⟨axes i, (2 : ℤ)^k⟩]

private theorem eval_affine (c k : ℕ) (i : Fin 4) (X : Fin 4 → ℤ_[2]) :
    evalRing X (affine c k i) = c + (2 : ℤ_[2]) ^ k * X i := by
  fin_cases i <;> simp [affine, term, axes, evalRing]

private theorem initial_data : ∀ b i : Fin 4, jPoly b i = affine (center b i) (radius i) i := by decide

theorem j_start (b i : Fin 4) (X : Fin 4 → ℤ_[2]) :
    J b (i:ℕ) X = (center b i : ℤ_[2]) + (2:ℤ_[2])^(radius i) * X i := by
  rw [J, initial_data, eval_affine]

private theorem endpoint_data : ∀ b i : Fin 4,
    eqCheck (2^(radius i)) (jPoly b (11+i)) (constant (center (b+1) i)) = true := by decide

theorem j_end (b i : Fin 4) (X : Fin 4 → ℤ_[2]) :
    PadicInt.toZModPow (radius i) (J b (11+(i:ℕ)) X) =
      (center (b+1) i : ZMod (2 ^ radius i)) := by
  rw [map_J]
  exact (eval_eq_of_check (pointMod (radius i) X) (endpoint_data b i)).trans
    (by simp only [eval_constant, Int.cast_natCast])

end A362884Cert

/-! The 44 modular polynomial product identities for the A362884 certificates. -/

namespace A362884Cert

open SparseResidual

private def productCheck (b : Fin 4) (i : ℕ) : Bool :=
  let m := 2 ^ P b (i + 4)
  let left := mul m (jPoly b i) (jPoly b (i + 4))
  let right := mul m (normalize m (mul m (fPoly b (i + 1)) (fPoly b (i + 2)))) (fPoly b (i + 3))
  eqCheck m left right

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem productChecks : ∀ (b : Fin 4) (i : Fin 11), productCheck b i = true := by
  decide

theorem product_eq (b : Fin 4) (i : ℕ) (hi : i < 11) (X : Fin 4 → ℤ_[2]) :
    PadicInt.toZModPow (P b (i + 4)) (J b i X * J b (i + 4) X) =
      PadicInt.toZModPow (P b (i + 4)) (F b (i + 1) X * F b (i + 2) X * F b (i + 3) X) := by
  simp only [map_mul, map_J, map_F]
  have h := productChecks b ⟨i, hi⟩
  simp only [productCheck] at h
  simpa only [eval_mul, eval_normalize] using eval_eq_of_check (pointMod (P b (i + 4)) X) h

end A362884Cert

namespace A362884QuarterInduction

/-- Propagate an invariant for a fourth-order recurrence through a finite block. -/
theorem run {length : ℕ} {Rep : ℕ → Prop}
    (hbase : ∀ k < 4, Rep k)
    (hstep : ∀ k < length, Rep k → Rep (k + 1) → Rep (k + 2) → Rep (k + 3) → Rep (k + 4))
    (n : ℕ) (hn : n < length + 4) : Rep n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hsmall : n < 4
    · exact hbase n hsmall
    · let k := n - 4
      have hnk : n = k + 4 := by dsimp [k]; omega
      have hlen : k < length := by dsimp [k]; omega
      have hk0 : k < n := by omega
      have hk1 : k + 1 < n := by omega
      have hk2 : k + 2 < n := by omega
      have hk3 : k + 3 < n := by omega
      rw [hnk]
      exact hstep k hlen
        (ih k hk0 (hk0.trans hn))
        (ih (k + 1) hk1 (hk1.trans hn))
        (ih (k + 2) hk2 (hk2.trans hn))
        (ih (k + 3) hk3 (hk3.trans hn))

/-- A quarter has eleven recurrence steps and fifteen represented values. -/
theorem quarter {Rep : ℕ → Prop} (hbase : ∀ k < 4, Rep k)
    (hstep : ∀ k < 11, Rep k → Rep (k + 1) → Rep (k + 2) → Rep (k + 3) → Rep (k + 4))
    (n : ℕ) (hn : n < 15) : Rep n :=
  run (length := 11) hbase hstep n hn

end A362884QuarterInduction

namespace A362884Quarter

open A362884Sound

/-- Arithmetic conditions independent of both the sequence and the jet parameters. -/
structure StepArithmetic (P W T : ℕ → ℕ) : Prop where
  positive : ∀ i < 15, 0 < P i
  readable : ∀ i < 15, T i + 1 ≤ W i + P i
  balance : ∀ i < 11, W i + W (i + 4) = T (i + 1) + T (i + 2) + T (i + 3)
  keep0 : ∀ i < 11, P (i + 4) ≤ P i
  keep1 : ∀ i < 11, T (i + 1) + P (i + 4) ≤ W (i + 1) + P (i + 1)
  keep2 : ∀ i < 11, T (i + 2) + P (i + 4) ≤ W (i + 2) + P (i + 2)
  keep3 : ∀ i < 11, T (i + 3) + P (i + 4) ≤ W (i + 3) + P (i + 3)

theorem stepArithmetic_of_fin {P W T : ℕ → ℕ}
    (hpositive : ∀ i : Fin 15, 0 < P i ∧ T i + 1 ≤ W i + P i)
    (hsteps : ∀ i : Fin 11,
      let k := i.val
      W k + W (k + 4) = T (k + 1) + T (k + 2) + T (k + 3) ∧
      P (k + 4) ≤ P k ∧
      T (k + 1) + P (k + 4) ≤ W (k + 1) + P (k + 1) ∧
      T (k + 2) + P (k + 4) ≤ W (k + 2) + P (k + 2) ∧
      T (k + 3) + P (k + 4) ≤ W (k + 3) + P (k + 3)) :
    StepArithmetic P W T where
  positive i hi := (hpositive ⟨i, hi⟩).1
  readable i hi := (hpositive ⟨i, hi⟩).2
  balance i hi := (hsteps ⟨i, hi⟩).1
  keep0 i hi := (hsteps ⟨i, hi⟩).2.1
  keep1 i hi := (hsteps ⟨i, hi⟩).2.2.1
  keep2 i hi := (hsteps ⟨i, hi⟩).2.2.2.1
  keep3 i hi := (hsteps ⟨i, hi⟩).2.2.2.2

/-- Algebraic and modular facts about the jets for one fixed tube parameter. -/
structure CheckedJets (P W T : ℕ → ℕ) (J F : ℕ → O) : Prop where
  jet_odd : ∀ i < 15, PadicInt.toZModPow 1 (J i) = 1
  factor_odd : ∀ i < 15, PadicInt.toZModPow 1 (F i) = 1
  factor_eq : ∀ i < 15, 1 + (2 : O) ^ W i * J i = (2 : O) ^ T i * F i
  product_eq : ∀ i < 11,
    PadicInt.toZModPow (P (i + 4)) (J i * J (i + 4)) =
      PadicInt.toZModPow (P (i + 4)) (F (i + 1) * F (i + 2) * F (i + 3))

/-- Each jet in a quarter represents the exact normalized rational value. -/
theorem represented {P W T : ℕ → ℕ} {q : ℕ → ℚ} {J F : ℕ → O}
    (arith : StepArithmetic P W T) (jets : CheckedJets P W T J F)
    (hrec : ∀ i < 11, q i * q (i + 4) = (1 + q (i + 1)) * (1 + q (i + 2)) * (1 + q (i + 3)))
    (hstart : ∀ i < 4, Close (P i) (normalized (q i) (W i)) (J i : K))
    (i : ℕ) (hi : i < 15) : Close (P i) (normalized (q i) (W i)) (J i : K) := by
  apply A362884QuarterInduction.quarter hstart ?_ i hi
  intro k hk h0 h1 h2 h3
  exact jet_step (arith.positive (k + 4) (by omega))
    (hrec k hk) (arith.balance k hk)
    (arith.keep0 k hk) (arith.keep1 k hk) (arith.keep2 k hk) (arith.keep3 k hk)
    (jets.jet_odd k (by omega)) h0 h1 h2 h3
    (jets.factor_eq (k + 1) (by omega)) (jets.factor_eq (k + 2) (by omega))
    (jets.factor_eq (k + 3) (by omega)) (jets.product_eq k hk)

/-- Read both rational valuation words from all fifteen normalized witnesses. -/
theorem readings {P W T : ℕ → ℕ} {q : ℕ → ℚ} {J F : ℕ → O}
    (arith : StepArithmetic P W T) (jets : CheckedJets P W T J F)
    (hrep : ∀ i < 15, Close (P i) (normalized (q i) (W i)) (J i : K))
    (i : ℕ) (hi : i < 15) :
    padicValRat 2 (q i) = (W i : ℤ) ∧ padicValRat 2 (1 + q i) = (T i : ℤ) :=
  ⟨jet_reading (arith.positive i hi) (hrep i hi) (jets.jet_odd i hi),
    factor_reading (hrep i hi) (arith.readable i hi) (jets.factor_eq i hi)
      (jets.factor_odd i hi)⟩

end A362884Quarter

namespace A362884Quarter

open A362884Sound

theorem endpoints_and_readings {q : ℕ → ℚ} {P W T : ℕ → ℕ} {J F : ℕ → O}
    {centerIn centerOut radius : Fin 4 → ℕ} {x : Fin 4 → O}
    (arith : StepArithmetic P W T) (jets : CheckedJets P W T J F)
    (hrec : ∀ i < 11, q i * q (i + 4) = (1 + q (i + 1)) * (1 + q (i + 2)) * (1 + q (i + 3)))
    (weightIn : ∀ i : Fin 4, W i.val = 0)
    (weightOut : ∀ i : Fin 4, W (11 + i.val) = 0)
    (enough : ∀ i : Fin 4, radius i ≤ P (11 + i.val))
    (hinput : ∀ i : Fin 4,
      (q i.val : K) = (centerIn i : K) + (2 : K) ^ radius i * (x i : K))
    (jStart : ∀ i : Fin 4,
      J i.val = (centerIn i : O) + (2 : O) ^ radius i * x i)
    (jEnd : ∀ i : Fin 4,
      PadicInt.toZModPow (radius i) (J (11 + i.val)) = (centerOut i : ZMod (2 ^ radius i))) :
    (∃ y : Fin 4 → O, ∀ i : Fin 4,
        (q (11 + i.val) : K) = (centerOut i : K) + (2 : K) ^ radius i * (y i : K)) ∧
      ∀ j : Fin 11, padicValRat 2 (q j.val) = (W j.val : ℤ) ∧
        padicValRat 2 (1 + q j.val) = (T j.val : ℤ) := by
  have hbase : ∀ i < 4, Close (P i) (normalized (q i) (W i)) (J i : K) := by
    intro i hi
    let k : Fin 4 := ⟨i, hi⟩
    have hw : W i = 0 := weightIn k
    have hj : J i = (centerIn k : O) + (2 : O) ^ radius k * x k := jStart k
    rw [hw, normalized, pow_zero, div_one, hj]
    exact A362884Endpoint.close_of_input_eq (p := P i) (hinput k)
  have hrep := represented arith jets hrec hbase
  have hout (i : Fin 4) : ∃ y : O,
      (q (11 + i.val) : K) = (centerOut i : K) + (2 : K) ^ radius i * (y : K) := by
    have hi : 11 + i.val < 15 := by have := i.isLt; omega
    have hc := hrep (11 + i.val) hi
    rw [weightOut i, normalized, pow_zero, div_one] at hc
    exact A362884Endpoint.witness_of_close_residue hc (enough i) (jEnd i)
  choose y hy using hout
  exact ⟨⟨y, hy⟩, fun j => readings arith jets hrep j.val (j.isLt.trans (by decide))⟩

end A362884Quarter

namespace A362884.BlockLink

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev K := ℚ_[2]
abbrev O := ℤ_[2]
abbrev Digits := Fin 4 → ℕ

/-- A point in a four-coordinate box with coordinate-wise precision. -/
noncomputable def point (center radius : Digits) (x : Fin 4 → O) (i : Fin 4) : K :=
  (center i : K) + (2 : K) ^ radius i * (x i : K)

/-- The exact multiplicative recurrence at an arbitrary offset. -/
theorem c_mul_step_at (s i : ℕ) :
    c (s + i) * c (s + (i + 4)) =
      (1 + c (s + (i + 1))) * (1 + c (s + (i + 2))) * (1 + c (s + (i + 3))) := by
  simp only [← Nat.add_assoc]
  change c (s + i) * (((1 + c (s + i + 1)) * (1 + c (s + i + 2)) *
    (1 + c (s + i + 3))) / c (s + i)) = _
  field_simp [(c_pos (s + i)).ne']

/-- The exact rational trajectory lies in the specified 2-adic box at index `s`. -/
def InBox (center radius : Digits) (s : ℕ) : Prop :=
  ∃ x : Fin 4 → O, ∀ i : Fin 4, (c (s + i.val) : K) = point center radius x i

/-- A segment certificate gives a destination point and reads each valuation in the segment.
The offset selects the expected entries of the periodic valuation words. -/
def SegmentCertificate (length offset : ℕ) (centerIn centerOut radius : Digits) : Prop :=
  ∀ (s : ℕ) (x : Fin 4 → O),
    (∀ i : Fin 4, (c (s + i.val) : K) = point centerIn radius x i) →
    InBox centerOut radius (s + length) ∧
    ∀ j : Fin length,
      padicValRat 2 (c (s + j.val)) = w (offset + j.val) ∧
        padicValRat 2 (1 + c (s + j.val)) = t (offset + j.val)

theorem SegmentCertificate.apply_at {length offset : ℕ} {centerIn centerOut radius : Digits}
    (h : SegmentCertificate length offset centerIn centerOut radius) {s : ℕ}
    (hs : InBox centerIn radius s) :
    InBox centerOut radius (s + length) ∧
      ∀ j : Fin length, padicValRat 2 (c (s + j.val)) = w (offset + j.val) ∧
        padicValRat 2 (1 + c (s + j.val)) = t (offset + j.val) := by
  obtain ⟨x, hx⟩ := hs
  exact h s x hx

theorem initial_box {center radius : Digits} (hcenter : ∀ i : Fin 4, center i = 1) :
    InBox center radius 0 := by
  refine ⟨fun _ => 0, ?_⟩
  intro i
  rw [point, hcenter]
  fin_cases i <;> simp [c]

theorem four_segments_at {centerA centerB centerC centerD radius : Digits}
    (hA : SegmentCertificate 11 0 centerA centerB radius)
    (hB : SegmentCertificate 11 11 centerB centerC radius)
    (hC : SegmentCertificate 11 22 centerC centerD radius)
    (hD : SegmentCertificate 11 33 centerD centerA radius) {s : ℕ}
    (hs : InBox centerA radius s) :
    InBox centerA radius (s + 44) ∧
      ∀ j : Fin 44, padicValRat 2 (c (s + j.val)) = w j.val ∧
        padicValRat 2 (1 + c (s + j.val)) = t j.val := by
  obtain ⟨hb, haRead⟩ := hA.apply_at hs
  obtain ⟨hc, hbRead⟩ := hB.apply_at hb
  obtain ⟨hd, hcRead⟩ := hC.apply_at hc
  obtain ⟨ha, hdRead⟩ := hD.apply_at hd
  refine ⟨by simpa only [Nat.add_assoc] using ha, ?_⟩
  intro j
  by_cases h0 : j.val < 11
  · simpa only [Nat.zero_add] using haRead ⟨j.val, h0⟩
  by_cases h1 : j.val < 22
  · have hj := hbRead ⟨j.val - 11, by omega⟩
    change padicValRat 2 (c (s + 11 + (j.val - 11))) = w (11 + (j.val - 11)) ∧
      padicValRat 2 (1 + c (s + 11 + (j.val - 11))) = t (11 + (j.val - 11)) at hj
    simpa only [Nat.add_assoc, show 11 + (j.val - 11) = j.val by omega] using hj
  by_cases h2 : j.val < 33
  · have hj := hcRead ⟨j.val - 22, by omega⟩
    change padicValRat 2 (c (s + 11 + 11 + (j.val - 22))) = w (22 + (j.val - 22)) ∧
      padicValRat 2 (1 + c (s + 11 + 11 + (j.val - 22))) = t (22 + (j.val - 22)) at hj
    have hindex : s + 11 + 11 + (j.val - 22) = s + j.val := by omega
    simpa only [hindex, show 22 + (j.val - 22) = j.val by omega] using hj
  have hj := hdRead ⟨j.val - 33, by omega⟩
  change padicValRat 2 (c (s + 11 + 11 + 11 + (j.val - 33))) = w (33 + (j.val - 33)) ∧
    padicValRat 2 (1 + c (s + 11 + 11 + 11 + (j.val - 33))) = t (33 + (j.val - 33)) at hj
  have hindex : s + 11 + 11 + 11 + (j.val - 33) = s + j.val := by omega
  simpa only [hindex, show 33 + (j.val - 33) = j.val by omega] using hj

theorem box_at_multiples {centerA centerB centerC centerD radius : Digits}
    (hinit : InBox centerA radius 0)
    (hA : SegmentCertificate 11 0 centerA centerB radius)
    (hB : SegmentCertificate 11 11 centerB centerC radius)
    (hC : SegmentCertificate 11 22 centerC centerD radius)
    (hD : SegmentCertificate 11 33 centerD centerA radius) (q : ℕ) :
    InBox centerA radius (44 * q) := by
  induction q with
  | zero => exact hinit
  | succ q ih =>
    rw [Nat.mul_succ]
    exact (four_segments_at hA hB hC hD ih).1

theorem words_of_four_segments {centerA centerB centerC centerD radius : Digits}
    (hinit : InBox centerA radius 0)
    (hA : SegmentCertificate 11 0 centerA centerB radius)
    (hB : SegmentCertificate 11 11 centerB centerC radius)
    (hC : SegmentCertificate 11 22 centerC centerD radius)
    (hD : SegmentCertificate 11 33 centerD centerA radius) (n : ℕ) :
    padicValRat 2 (c n) = w n ∧ padicValRat 2 (1 + c n) = t n := by
  have hwindow := box_at_multiples hinit hA hB hC hD (n / 44)
  have hidx : 44 * (n / 44) + n % 44 = n :=
    (Nat.add_comm _ _).trans (Nat.mod_add_div n 44)
  have h := (four_segments_at hA hB hC hD hwindow).2 ⟨n % 44, Nat.mod_lt n (by decide)⟩
  change padicValRat 2 (c (44 * (n / 44) + n % 44)) = w (n % 44) ∧
    padicValRat 2 (1 + c (44 * (n / 44) + n % 44)) = t (n % 44) at h
  simpa only [hidx, w, t, Nat.mod_mod] using h

open OMA.S_oeis_a362884 (a)

theorem main_of_four_segments {centerA centerB centerC centerD radius : Digits}
    (hinit : InBox centerA radius 0)
    (hA : SegmentCertificate 11 0 centerA centerB radius)
    (hB : SegmentCertificate 11 11 centerB centerC radius)
    (hC : SegmentCertificate 11 22 centerC centerD radius)
    (hD : SegmentCertificate 11 33 centerD centerA radius) :
    type_of% @OMA.S_oeis_a362884.main := by
  intro n
  have hwords := words_of_four_segments hinit hA hB hC hD
  have hv := bounds_of_words a rfl rfl rfl rfl (fun _ => rfl)
    (fun k => (hwords k).1) (fun k => (hwords k).2) n
  exact integer_of_dyadic_valuation (a n) (a_positive n).ne' (a_dyadic n) hv.1 hv.2

theorem main_of_cycle (center : Fin 4 → Digits) (radius : Digits)
    (hcenter : ∀ i : Fin 4, center 0 i = 1)
    (hcert : ∀ b : Fin 4, SegmentCertificate 11 (11 * b.val)
      (center b) (center (b + 1)) radius) :
    type_of% @OMA.S_oeis_a362884.main :=
  main_of_four_segments (initial_box hcenter) (hcert 0) (hcert 1) (hcert 2) (hcert 3)

end A362884.BlockLink

namespace A362884Quarter

open A362884Sound

theorem segment_of_certificates {offset : ℕ} {P W T : ℕ → ℕ}
    {J F : ℕ → (Fin 4 → O) → O}
    {centerIn centerOut radius : Fin 4 → ℕ}
    (arith : StepArithmetic P W T)
    (jets : ∀ x, CheckedJets P W T (fun i => J i x) (fun i => F i x))
    (weightIn : ∀ i : Fin 4, W i.val = 0)
    (weightOut : ∀ i : Fin 4, W (11 + i.val) = 0)
    (enough : ∀ i : Fin 4, radius i ≤ P (11 + i.val))
    (matchW : ∀ j : Fin 11, (W j.val : ℤ) = A362884.w (offset + j.val))
    (matchT : ∀ j : Fin 11, (T j.val : ℤ) = A362884.t (offset + j.val))
    (jStart : ∀ (x : Fin 4 → O) (i : Fin 4),
      J i.val x = (centerIn i : O) + (2 : O) ^ radius i * x i)
    (jEnd : ∀ (x : Fin 4 → O) (i : Fin 4),
      PadicInt.toZModPow (radius i) (J (11 + i.val) x) = (centerOut i : ZMod (2 ^ radius i))) :
    A362884.BlockLink.SegmentCertificate 11 offset centerIn centerOut radius := by
  intro s x hinput
  have h := endpoints_and_readings (q := fun i => A362884.c (s + i))
    arith (jets x) (fun i _ => A362884.BlockLink.c_mul_step_at s i)
    weightIn weightOut enough hinput (jStart x) (jEnd x)
  refine ⟨?_, ?_⟩
  · simpa only [A362884.BlockLink.InBox, A362884.BlockLink.point, Nat.add_assoc] using h.1
  · intro j
    exact ⟨(h.2 j).1.trans (matchW j), (h.2 j).2.trans (matchT j)⟩

end A362884Quarter

namespace A362884Integration

open A362884 A362884.BlockLink A362884Cert A362884Quarter

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem arithmetic_positive :
    ∀ b : Fin 4, ∀ i : Fin 15, 0 < P b i ∧ T b i + 1 ≤ W b i + P b i := by decide

private theorem arithmetic_steps :
    ∀ b : Fin 4, ∀ i : Fin 11,
      let k := i.val
      W b k + W b (k + 4) = T b (k + 1) + T b (k + 2) + T b (k + 3) ∧
      P b (k + 4) ≤ P b k ∧
      T b (k + 1) + P b (k + 4) ≤ W b (k + 1) + P b (k + 1) ∧
      T b (k + 2) + P b (k + 4) ≤ W b (k + 2) + P b (k + 2) ∧
      T b (k + 3) + P b (k + 4) ≤ W b (k + 3) + P b (k + 3) := by decide

private theorem initial_weight : ∀ b i : Fin 4, W b i.val = 0 := by decide

private theorem terminal_weight : ∀ b i : Fin 4, W b (11 + i.val) = 0 := by decide

private theorem terminal_precision : ∀ b i : Fin 4, radius i ≤ P b (11 + i.val) := by decide

private theorem reading_words : ∀ b : Fin 4, ∀ j : Fin 11,
    (W b j.val : ℤ) = w (11 * b.val + j.val) ∧ (T b j.val : ℤ) = t (11 * b.val + j.val) := by decide

private theorem checked_jets (b : Fin 4) (x : Fin 4 → ℤ_[2]) :
    CheckedJets (P b) (W b) (T b) (fun i => J b i x) (fun i => F b i x) where
  jet_odd i hi := j_odd b i hi x
  factor_odd i hi := f_odd b i hi x
  factor_eq i hi := A362884Cert.factor_eq b i hi x
  product_eq i hi := A362884Cert.product_eq b i hi x

theorem certified_segment (b : Fin 4) :
    SegmentCertificate 11 (11 * b.val) (center b) (center (b + 1)) radius := by
  exact segment_of_certificates
    (stepArithmetic_of_fin (arithmetic_positive b) (arithmetic_steps b)) (checked_jets b)
    (initial_weight b) (terminal_weight b) (terminal_precision b)
    (fun j => (reading_words b j).1) (fun j => (reading_words b j).2)
    (fun x i => j_start b i x) (fun x i => j_end b i x)

end A362884Integration

theorem OMA.solution : type_of% @OMA.S_oeis_a362884.main := by
  apply A362884.BlockLink.main_of_cycle A362884Cert.center A362884Cert.radius _
    A362884Integration.certified_segment
  decide
