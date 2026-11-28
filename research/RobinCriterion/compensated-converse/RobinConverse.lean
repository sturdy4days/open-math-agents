import OMAReductions.R_RiemannHypothesis_robin_criterion_R1
import Mathlib

/-!
# Robin's divisor-sum inequality implies the Riemann hypothesis

Nicolas (1983) and Robin (1984) supply the oscillation argument.  The positive
Mellin and rightmost-zero continuation proofs below adapt Jonas Whidden's
Robin1984 (Apache-2.0, e3697139babfe0f6cc7a76a08bf41a92aa7a2978),
as assembled for the earlier OMA Lagarias reductions.  The Mertens arguments
are credited in place.  The compensated primitive, its damped Frullani transform
and Abel boundary argument replace the quantitative prime-number-theorem input.
-/

section
/-
# A one-sided psi-error bound implied by Robin's inequality

Following Nicolas (1983) and Robin (1984), compare the prime product with the
Chebyshev tail and then transfer its logarithm to the divisor sum of lcm(1,…,N).
The product estimate is adapted from the OMA Lagarias converse work and the
PNT+ and Mertens contributors credited below. The lcm estimates are from the
OMA Lagarias converse, R1.H2.R1.H1.R1 and its H2 proof. The little-o argument
follows Jonas Whidden's Robin1984, e3697139babfe0f6cc7a76a08bf41a92aa7a2978.
-/

section
/- Reuses the existing open-math-agents #12357 proof of the identical Mertens product
input. The statements differ only by the parent reduction namespace. -/

-- Port of the PrimeNumberTheoremAnd project contributors,
-- AlexKontorovich/PrimeNumberTheoremAnd at 55270df80721, Apache-2.0.
-- Mertens contributions include Terence Tao, A. J. Irving, Giuseppe Sorge,
-- Robby Sneiderman and Yan Yablonovskiy. The comparison uses the reciprocal product.
-- The last step inverts the standard prime product to match the target.
-- Credit: @marcusbuffett

section
open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

end

section

namespace Real

open Filter Asymptotics

theorem inv_log_eq_o_one : (fun x ↦ 1 / log x) =o[atTop] (fun _ ↦ (1:ℝ)) := by
    rw [isLittleO_one_iff]
    convert tendsto_log_atTop.inv_tendsto_atTop using 1
    ext; simp

end Real

section Issue1584
open MeasureTheory Set Filter Topology

private lemma integral_log_mul_exp_neg_eq_deriv_Gamma :
    ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) = deriv Real.Gamma 1 := by
  set I : ℝ := ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) with hI

  have h1 := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)

  have hval : (∫ t : ℝ in Ioi 0, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t))))
      = (I : ℂ) := by
    have key : ∀ t : ℝ, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t)))
        = ((Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
      intro t
      rw [sub_self, Complex.cpow_zero, one_mul, Complex.ofReal_mul]
    simp_rw [key]
    rw [integral_complex_ofReal, hI]
  rw [hval] at h1

  have h2 : HasDerivAt Complex.Gamma (I : ℂ) 1 := by
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0:ℝ) < (1:ℂ).re by norm_num)] with z hz
    exact Complex.Gamma_eq_integral hz

  have h3 := h2.real_of_complex
  have h4 : HasDerivAt Real.Gamma I 1 := by
    have hcongr : (fun x : ℝ => (Complex.Gamma ↑x).re) = Real.Gamma := by
      funext x
      rw [Complex.Gamma_ofReal, Complex.ofReal_re]
    rw [hcongr, Complex.ofReal_re] at h3
    exact h3
  rw [← h4.deriv]

open Real in
private theorem mul_integ_log_log_eq_aux (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) =
      - Real.log (s - 1) + deriv Real.Gamma 1 := by
  have hgamma := integral_log_mul_exp_neg_eq_deriv_Gamma
  have hint : IntegrableOn (fun u : ℝ => log u * exp (-u)) (Ioi 0) := by
    by_contra h
    have hz := integral_undef h
    rw [hgamma] at hz
    linarith [eulerMascheroniConstant_eq_neg_deriv, one_half_lt_eulerMascheroniConstant]
  let a := s-1
  have ha : 0<a := by dsimp [a]; linarith
  let g (u : ℝ) := log u * exp (-u) - log a * exp (-u)
  have move := integral_comp_exp_Ioi (fun x : ℝ => log (log x)*x^(-s)) 0
  rw [exp_zero] at move
  have scale := integral_comp_mul_left_Ioi' g 0 ha
  rw [mul_zero,smul_eq_mul] at scale
  have replace : (∫ u in Ioi (0:ℝ), exp u • (log (log (exp u))*(exp u)^(-s))) =
      ∫ u in Ioi (0:ℝ), g (a*u) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change 0<u at hu
    dsimp only [g]
    rw [log_exp,smul_eq_mul,log_mul ha.ne' hu.ne',rpow_def_of_pos (exp_pos u),log_exp]
    have h : exp u*exp (u*(-s))=exp (-(a*u)) := by
      rw [← exp_add]; congr 1; dsimp [a]; ring
    linear_combination log u * h
  change a * _ = -log a + _
  rw [←move,replace,scale,integral_sub hint ((integrableOn_exp_neg_Ioi 0).const_mul (log a)),
    integral_const_mul,integral_exp_neg_Ioi_zero,hgamma]
  ring

end Issue1584

namespace Mertens

open Real Finset Filter Asymptotics Topology
open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa

theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

theorem sum_mangoldt_div_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d = log x + E₁Λ x := by
    grind

theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

theorem sum_mangoldt_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x| ≤ log 4 + 4 := by
  grind [E₁Λ.le hx, E₁Λ.ge hx, log_nonneg]

theorem E₁Λ.bounded' : ∃ c > 0, ∀ x ≥ 1, |E₁Λ x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun x hx ↦ sum_mangoldt_div_eq_log hx⟩

noncomputable abbrev γ : ℝ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)

noncomputable abbrev E₂Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ

lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

private theorem integrable_E₁Λ_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁Λ x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁Λ.bounded'
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)

theorem E₂Λ.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂Λ x = E₁Λ x / log x - ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) := by
  unfold E₂Λ
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  conv => lhs; arg 1; arg 1; arg 2; ext n; rw [(by field : Λ n / (n * log n) = (Λ n / n) / log n)]
  rw [sum_div_log_eq hx]
  rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, Λ n / n) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁Λ t / (t * log t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold γ
    calc
    _ = E₁Λ x / log x + (∫ (x : ℝ) in 2..x, E₁Λ x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁Λ t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁Λ_div_mul_log_sq (by rfl)) (integrable_E₁Λ_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁Λ_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp

theorem E₂Λ.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂Λ.eq hx, abs_le']
    constructor
    · grw [E₁Λ.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≥ - 2 / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2) hx)
            (integrable_E₁Λ_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2) hx
      grw [this]
      grind
    grw [E₁Λ.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁Λ_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

theorem E₂Λ.bound : E₂Λ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6, 2
    intro x hx
    convert E₂Λ.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]

theorem E₂Λ.bound' : E₂Λ =o[atTop] (fun _ ↦ (1:ℝ)) := E₂Λ.bound.trans_isLittleO inv_log_eq_o_one

theorem log_zeta_eq_sum (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = ∑' n, Λ n / (n^s * log n) := log_riemannZeta_eq hs

section
open MeasureTheory Set

namespace LogZetaInteg

private noncomputable def c (d : ℕ) : ℝ := Λ d / (d * Real.log d)

private noncomputable def f (s : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
    c d * (Set.Ici (d:ℝ)).indicator (fun x => x ^ (-s)) x

@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]

private lemma c_nonneg (d : ℕ) : 0 ≤ c d := by
  unfold c
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  · apply div_nonneg vonMangoldt_nonneg
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
    positivity

private lemma summable_c_term (s : ℝ) (hs : 1 < s) :
    Summable (fun d : ℕ => c d * ((d:ℝ) ^ (1 - s) / (s - 1))) := by
  unfold c
  refine ((Real.summable_nat_rpow.mpr (by linarith : -s < -1)).div_const (s-1)).of_norm_bounded_eventually_nat ?_
  filter_upwards [eventually_ge_atTop 2] with d hd
  have pos : 0 < (d:ℝ) := by positivity
  have hlog : 0 < log (d:ℝ) := log_pos (by exact_mod_cast (by omega : 1<d))
  have hp : 0 < s-1 := by linarith
  rw [sub_eq_add_neg 1 s, Real.rpow_add pos, Real.rpow_one,
    Real.norm_of_nonneg (by exact mul_nonneg (div_nonneg vonMangoldt_nonneg (by positivity)) (by positivity))]
  calc (Λ d/(d*log d))*((d:ℝ)*d^(-s)/(s-1)) = (Λ d/log d) * (d:ℝ)^(-s)/(s-1) := by
        field_simp
    _ ≤ 1*(d:ℝ)^(-s)/(s-1) := by
        gcongr
        exact (div_le_one hlog).mpr vonMangoldt_le_log
    _ = _ := by simp

theorem log_zeta_eq_integ_aux (s : ℝ) (hs : 1 < s) :
    Real.log (riemannZeta (s:ℂ)).re =
      (s - 1) * ∫ x in Set.Ioi 1, (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) := by
  rw [Mertens.log_zeta_eq_sum s hs]
  symm
  have hstep1 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s)
        = (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, c d) * x ^ (-s) := by
    intro x hx
    simp only [Mertens.E₂Λ, c]
    ring
  have hstep2 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) = ∑' d : ℕ, f s d x := by
    intro x hx
    rw [hstep1 x hx]
    simp only [f]
    rw [Finset.sum_mul]
    have hx0 : (0:ℝ) ≤ x := by have := hx; simp only [Set.mem_Ioi] at this; linarith
    rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊x⌋₊) ?_]
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [Finset.mem_Ioc] at hd
      have hdx : (d:ℝ) ≤ x := by
        rw [← Nat.le_floor_iff hx0]; exact hd.2
      rw [Set.indicator_of_mem (by simpa using hdx)]
    · intro d hd
      simp only [Finset.mem_Ioc, not_and, not_le] at hd
      rcases Nat.eq_zero_or_pos d with hd0 | hd0
      · subst hd0; simp
      · have hfloor : ⌊x⌋₊ < d := hd hd0
        have hdx : x < (d:ℝ) := by
          rw [← Nat.floor_lt hx0]; exact hfloor
        rw [Set.indicator_of_notMem (by simpa using not_le.mpr hdx)]
        ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hstep2]
  have hperterm : ∀ d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0; simp [f]
    simp only [f]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_indicator measurableSet_Ici]
    congr 1
    have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd0
    have hdR0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    set A : Set ℝ := Set.Ioi (1:ℝ) ∩ Set.Ici (d:ℝ) with hA
    have hae : A =ᵐ[volume] Set.Ioi (d:ℝ) := by
      have h1 : A =ᵐ[volume] (Set.Ici (1:ℝ) ∩ Set.Ici (d:ℝ) : Set ℝ) :=
        MeasureTheory.ae_eq_set_inter MeasureTheory.Ioi_ae_eq_Ici (ae_eq_refl _)
      rw [Set.Ici_inter_Ici, max_eq_right hdR] at h1
      exact h1.trans MeasureTheory.Ioi_ae_eq_Ici.symm
    rw [MeasureTheory.setIntegral_congr_set hae]
    rw [integral_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) hdR0,
      show (-s + 1 : ℝ) = 1 - s by ring]
    have hs1 : (1 - s) ≠ 0 := by linarith
    have hs2 : (s - 1) ≠ 0 := by linarith
    field_simp
    ring
  have hint : ∀ d : ℕ, MeasureTheory.IntegrableOn (f s d) (Set.Ioi (1:ℝ)) := by
    intro d
    unfold f
    apply MeasureTheory.Integrable.const_mul
    rw [show MeasureTheory.Integrable ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
        (volume.restrict (Set.Ioi (1:ℝ)))
      ↔ MeasureTheory.IntegrableOn ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
          (Set.Ioi (1:ℝ)) volume from Iff.rfl,
      MeasureTheory.integrableOn_indicator_iff measurableSet_Ici]
    apply MeasureTheory.IntegrableOn.mono_set
      (integrableOn_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) (by norm_num : (0:ℝ) < 1/2))
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    linarith [hx.2]
  have hnorm_int : ∀ d : ℕ,
      ∫ x in Set.Ioi (1:ℝ), ‖f s d x‖ = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rw [← hperterm d]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hfnn : 0 ≤ f s d x := by
      simp only [f]
      apply mul_nonneg (c_nonneg d)
      by_cases hxd : (d:ℝ) ≤ x
      · rw [Set.indicator_of_mem (by simpa using hxd)]
        exact le_of_lt (Real.rpow_pos_of_pos (by linarith) _)
      · rw [Set.indicator_of_notMem (by simpa using hxd)]
    change ‖f s d x‖ = f s d x
    rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
  have hinterchange : ∫ x in Set.Ioi (1:ℝ), ∑' d : ℕ, f s d x
      = ∑' d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x := by
    refine (MeasureTheory.integral_tsum_of_summable_integral_norm hint ?_).symm
    apply (summable_c_term s hs).congr
    intro d
    exact (hnorm_int d).symm
  rw [hinterchange]
  simp_rw [hperterm]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro d
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0; simp
  · have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    have hsub : (d:ℝ) ^ (1 - s) = (d:ℝ) ^ (-s) * (d:ℝ) := by
      rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hdR, Real.rpow_one]
    have hs1 : s - 1 ≠ 0 := by linarith
    have hneg : (d:ℝ) ^ (-s) = ((d:ℝ) ^ s)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hdR)]
    unfold c
    rw [hsub, hneg]
    field_simp

end LogZetaInteg
end

private theorem log_zeta_eq_integ (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = (s - 1) * ∫ x in .Ioi 1, (log (log x) + γ + E₂Λ x) * x^(-s) :=
  LogZetaInteg.log_zeta_eq_integ_aux s hs

private theorem mul_integ_log_log_eq (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in .Ioi 1, log (log x) * x^(-s) = - log (s - 1) + deriv Gamma 1 :=
  mul_integ_log_log_eq_aux s hs

private theorem mul_integ_gamma_eq (s) (hs : 1 < s) : (s - 1) * ∫ x in .Ioi 1, γ * x^(-s) = γ := by
  rw [MeasureTheory.integral_const_mul γ (· ^ (-s)), @integral_Ioi_rpow_of_lt (-s), one_rpow] <;>
    grind

private theorem integrableOn_Ioi_mul_rpow_neg_of_abs_le
    {c B a s : ℝ} (hc : 0 < c) (has : a + 1 < s) {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x ∈ Set.Ioi c, |f x| ≤ B * x ^ a) :
    MeasureTheory.IntegrableOn (fun x => f x * x ^ (-s)) (Set.Ioi c) := by
  have hg : MeasureTheory.IntegrableOn (fun x => B * x ^ (a - s)) (Set.Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : a - s < -1) hc).const_mul B
  refine MeasureTheory.Integrable.mono' hg
    (hf.mul (measurable_id.pow_const (-s))).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : (0:ℝ) < x := hc.trans hx
  have hxs : (0:ℝ) < x ^ (-s) := Real.rpow_pos_of_pos hxpos _
  rw [norm_mul, norm_eq_abs, norm_eq_abs, abs_of_pos hxs]
  calc |f x| * x ^ (-s) ≤ B * x ^ a * x ^ (-s) :=
        mul_le_mul_of_nonneg_right (hbound x hx) hxs.le
    _ = B * x ^ (a - s) := by rw [mul_assoc, ← Real.rpow_add hxpos, sub_eq_add_neg]

private theorem integrableOn_log_log_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => log (log x) * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (1:ℝ) ≤ 2)]
  apply MeasureTheory.IntegrableOn.union
  ·
    have hll : MeasureTheory.IntegrableOn (fun x => log (log x)) (Set.Ioc 1 2) := by
      have h : IntervalIntegrable (log ∘ log) MeasureTheory.volume 1 2 := by
        apply MeromorphicOn.intervalIntegrable_log
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hx
        exact (analyticAt_log (by linarith [hx.1] : 0 < x)).meromorphicAt
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h
    have hmul : MeasureTheory.IntegrableOn (fun x => x ^ (-s) * log (log x)) (Set.Ioc 1 2) := by
      apply hll.bdd_mul (c := 1)
      · fun_prop
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        rw [norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x) _)]
        calc x ^ (-s) ≤ (1:ℝ) ^ (-s) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1.le (by linarith)
          _ = 1 := Real.one_rpow _
    simpa [mul_comm] using hmul
  ·
    set ε := (s - 1) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := ε) (B := 1 / ε + |log (log 2)|)
      (by norm_num) (by rw [hε]; linarith) (Real.measurable_log.comp Real.measurable_log) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hx1 : (1:ℝ) ≤ x ^ ε := Real.one_le_rpow (by linarith) hεpos.le
    have hlogx : 0 < log x := Real.log_pos (by linarith)
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hmono : log 2 ≤ log x := Real.log_le_log (by norm_num) (by linarith)
    have hub : log (log x) ≤ x ^ ε / ε :=
      calc log (log x) ≤ log x := (Real.log_le_sub_one_of_pos hlogx).trans (by linarith)
        _ ≤ x ^ ε / ε := Real.log_le_rpow_div (by linarith) hεpos
    have hlb : log (log 2) ≤ log (log x) := Real.log_le_log hlog2 hmono
    have hxε : 0 ≤ x ^ ε / ε := by positivity
    calc |log (log x)| ≤ x ^ ε / ε + |log (log 2)| := by
          rw [abs_le]
          exact ⟨by linarith [neg_abs_le (log (log 2))],
            by linarith [abs_nonneg (log (log 2))]⟩
      _ ≤ (1 / ε + |log (log 2)|) * x ^ ε := by
          have h2 : |log (log 2)| ≤ |log (log 2)| * x ^ ε := le_mul_of_one_le_right (abs_nonneg _) hx1
          have h1 : x ^ ε / ε = 1 / ε * x ^ ε := by ring
          rw [add_mul]; linarith

private theorem integrableOn_γ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => γ * x ^ (-s)) (Set.Ioi 1) := by
  exact (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) one_pos).const_mul γ

private theorem integrableOn_E₂Λ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => E₂Λ x * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioo_union_Ici_eq_Ioi (by norm_num : (1:ℝ) < 2)]
  apply MeasureTheory.IntegrableOn.union
  ·
    have hsub : Set.Ioo (1:ℝ) 2 ⊆ Set.Ioi 1 := fun x hx => hx.1
    have h1 := (integrableOn_γ_mul_rpow s hs).mono_set hsub
    have h2 := (integrableOn_log_log_mul_rpow s hs).mono_set hsub
    have hb : MeasureTheory.IntegrableOn
        (fun x => -(log (log x) * x ^ (-s)) - γ * x ^ (-s)) (Set.Ioo 1 2) :=
      h2.neg.sub h1
    apply hb.congr_fun _ measurableSet_Ioo
    intro x hx
    simp only [Set.mem_Ioo] at hx
    have hfloor : ⌊ x ⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      exact ⟨by push_cast; linarith [hx.1], by push_cast; linarith [hx.2]⟩
    have hsum : (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / ((d:ℝ) * log d)) = 0 := by rw [hfloor]; norm_num
    change -(log (log x) * x ^ (-s)) - γ * x ^ (-s)
        = (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ) * x ^ (-s)
    rw [hsum]; ring
  ·
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := 0) (B := (log 4 + 6) / log 2)
      (by norm_num) (by linarith) (by fun_prop) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hc : 0 ≤ log 4 + 6 := by positivity
    rw [Real.rpow_zero, mul_one]
    have hb2 : (log 4 + 6) / log x ≤ (log 4 + 6) / log 2 :=
      div_le_div_of_nonneg_left hc hlog2 (Real.log_le_log (by norm_num) (le_of_lt hx))
    exact (E₂Λ.abs_le (le_of_lt hx)).trans hb2

private theorem log_zeta_eq (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = - log (s - 1) + deriv Gamma 1 + γ + (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x^(-s) := by

  rw [log_zeta_eq_integ s hs]

  have key : (∫ x in Set.Ioi 1, (log (log x) + γ + E₂Λ x) * x ^ (-s))
      = (∫ x in Set.Ioi 1, log (log x) * x ^ (-s))
        + (∫ x in Set.Ioi 1, γ * x ^ (-s))
        + (∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)) := by
    rw [← MeasureTheory.integral_add (integrableOn_log_log_mul_rpow s hs)
      (integrableOn_γ_mul_rpow s hs)]
    rw [← MeasureTheory.integral_add (f := fun x => log (log x) * x ^ (-s) + γ * x ^ (-s))
      (g := fun x => E₂Λ x * x ^ (-s))
      ((integrableOn_log_log_mul_rpow s hs).add (integrableOn_γ_mul_rpow s hs))
      (integrableOn_E₂Λ_mul_rpow s hs)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring

  rw [key, mul_add, mul_add, mul_integ_log_log_eq s hs, mul_integ_gamma_eq s hs]

private lemma zeta_pole_mul_re_tendsto_one :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (riemannZeta (s : ℂ)).re)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have hofReal :
      Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
        (nhdsWithin (1 : ℂ) ({1} : Set ℂ)ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_compl_singleton_iff.mpr (by
        norm_num
        exact ne_of_gt (Set.mem_Ioi.mp hs))
  have hcomplex :
      Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    riemannZeta_residue_one.comp hofReal
  have hreal :
      Filter.Tendsto
        (fun s : ℝ => (((s : ℂ) - 1) * riemannZeta (s : ℂ)).re)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 : ℝ)) :=
    (Complex.continuous_re.tendsto (1 : ℂ)).comp hcomplex
  simpa [Complex.ofReal_sub, Complex.ofReal_mul] using hreal

private theorem log_zeta_limit :
    Filter.Tendsto
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  have hlog :
      Filter.Tendsto
        (fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.log 1)) :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      zeta_pole_mul_re_tendsto_one
  have hEq :
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
        =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s - 1 := sub_pos.mpr (Set.mem_Ioi.mp hs)
    have hzpos : 0 < (riemannZeta (s : ℂ)).re :=
      riemannZeta_re_pos_of_one_lt (Set.mem_Ioi.mp hs)
    rw [Real.log_mul hspos.ne' hzpos.ne']
    ring
  simpa using hlog.congr' (hEq.mono fun s hs => hs.symm)

section
open MeasureTheory Set

private lemma measurable_E₂Λ : Measurable E₂Λ := by fun_prop

private lemma qualitative_local_integrable {F : ℝ → ℝ} {X : ℝ}
    (h : IntegrableOn (fun x : ℝ => F x * x ^ (-(2:ℝ))) (Ioi 1)) :
    IntegrableOn F (Ioo 1 X) := by
  have sub : Ioo 1 X ⊆ Ioi 1 := fun x hx => hx.1
  have product : IntegrableOn (fun x : ℝ => x^2 * (F x*x^(-(2:ℝ)))) (Ioo 1 X) := by
    apply (h.mono_set sub).bdd_mul (c:=X^2)
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [norm_eq_abs,abs_of_nonneg (sq_nonneg x)]
      exact pow_le_pow_left₀ (by linarith [hx.1]) hx.2.le _
  apply product.congr_fun _ measurableSet_Ioo
  intro x hx
  have hp : 0<x := by linarith [hx.1]
  change x^2*(F x*x^(-(2:ℝ))) = F x
  rw [Real.rpow_neg hp.le]
  norm_num
  field_simp

private lemma sub_one_mul_integral_E₂Λ_tendsto :
    Filter.Tendsto (fun s : ℝ => (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε

  obtain ⟨X₀, hX₀⟩ : ∃ X, ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := by
    have := E₂Λ.bound'.def (by positivity : (0:ℝ) < ε / 2)
    simp only [Real.norm_eq_abs, abs_one, mul_one] at this
    rw [Filter.eventually_atTop] at this; exact this
  set X := max X₀ 2 with hXdef
  have hX2 : 2 ≤ X := le_max_right _ _
  have hXge : ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := fun x hx => hX₀ x (le_trans (le_max_left _ _) hx)

  set B := ∫ x in Set.Ioo 1 X, |E₂Λ x| with hBdef
  have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_Ioo (fun x _ => abs_nonneg _)
  refine ⟨min 1 (ε / 2 / (B + 1)), by positivity, ?_⟩
  intro s hs hdist
  simp only [Set.mem_Ioi] at hs
  rw [Real.dist_eq] at hdist
  have hs1 : s - 1 < min 1 (ε / 2 / (B + 1)) := by
    rw [abs_of_pos (by linarith)] at hdist; exact hdist
  have hsm1 : 0 < s - 1 := by linarith

  have hintAbs : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi 1) volume := by
    have h2 : IntegrableOn (fun x => |E₂Λ x * x ^ (-s)|) (Set.Ioi 1) volume :=
      (integrableOn_E₂Λ_mul_rpow s hs).abs
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro x hx; simp only [Set.mem_Ioi] at hx
    change |E₂Λ x * x ^ (-s)| = |E₂Λ x| * x ^ (-s)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have hintAbsIoc : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioc 1 X) volume :=
    hintAbs.mono_set Set.Ioc_subset_Ioi_self
  have hintAbsIoiX : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi X) volume :=
    hintAbs.mono_set (Set.Ioi_subset_Ioi (by linarith))

  have hsplit : ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) =
      (∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s)) + ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) := by
    have hu : Set.Ioi (1:ℝ) = Set.Ioc 1 X ∪ Set.Ioi X :=
      (Set.Ioc_union_Ioi_eq_Ioi (by linarith)).symm
    rw [hu, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_left))
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_right))]

  have hp1 : ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ B := by
    rw [hBdef]
    have ha : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioo 1 X) volume := (qualitative_local_integrable (X:=X) (integrableOn_E₂Λ_mul_rpow 2 (by norm_num))).abs
    have habsIoc : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioc 1 X) volume :=
      ha.congr_set_ae (Ioo_ae_eq_Ioc).symm
    rw [← integral_Ioc_eq_integral_Ioo]
    apply setIntegral_mono_on hintAbsIoc habsIoc measurableSet_Ioc
    intro x hx
    have hx1 : (1:ℝ) ≤ x := by have := hx.1; linarith
    have hle1 : x ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    calc |E₂Λ x| * x ^ (-s) ≤ |E₂Λ x| * 1 := by gcongr
      _ = |E₂Λ x| := mul_one _

  have hp2 : ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ (ε / 2) * (X ^ (1 - s) / (s - 1)) := by
    have hrpow_int : IntegrableOn (fun x : ℝ => x ^ (-s)) (Set.Ioi X) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X)
    have hval : ∫ x in Set.Ioi X, x ^ (-s) = X ^ (1 - s) / (s - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X),
        show -s + 1 = 1 - s by ring, show (1:ℝ) - s = -(s - 1) by ring]
      rw [div_neg, neg_div, neg_neg]
    rw [← hval, ← integral_const_mul]
    apply setIntegral_mono_on hintAbsIoiX (hrpow_int.const_mul (ε / 2)) measurableSet_Ioi
    intro x hx
    have hxpos : (0:ℝ) < x := by simp only [Set.mem_Ioi] at hx; linarith
    have hnn : 0 ≤ x ^ (-s) := Real.rpow_nonneg hxpos.le _
    have hb : |E₂Λ x| ≤ ε / 2 := hXge x (by simp only [Set.mem_Ioi] at hx; linarith)
    gcongr
  have hXpow : X ^ (1 - s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)

  have hbound : (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B + ε / 2 := by
    rw [hsplit, mul_add]
    have ht2 : (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ ε / 2 := by
      calc (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s)
          ≤ (s - 1) * ((ε / 2) * (X ^ (1 - s) / (s - 1))) :=
            mul_le_mul_of_nonneg_left hp2 hsm1.le
        _ = (ε / 2) * X ^ (1 - s) := by
              have hne : s - 1 ≠ 0 := by linarith
              field_simp
        _ ≤ (ε / 2) * 1 := by gcongr
        _ = ε / 2 := mul_one _
    have ht1 : (s - 1) * ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B :=
      mul_le_mul_of_nonneg_left hp1 hsm1.le
    linarith

  have habs_le : |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := by
    rw [abs_mul, abs_of_pos hsm1]
    gcongr
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Set.mem_Ioi] at hx
    change ‖E₂Λ x * x ^ (-s)‖ = |E₂Λ x| * x ^ (-s)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  rw [Real.dist_eq, sub_zero]

  have hfin : (s - 1) * B + ε / 2 < ε := by
    have hlt : s - 1 < ε / 2 / (B + 1) := lt_of_lt_of_le hs1 (min_le_right _ _)
    have hBp : 0 < B + 1 := by linarith
    have h1 : (s - 1) * B ≤ (s - 1) * (B + 1) := by nlinarith
    have h2 : (s - 1) * (B + 1) < (ε / 2 / (B + 1)) * (B + 1) := mul_lt_mul_of_pos_right hlt hBp
    have h3 : (ε / 2 / (B + 1)) * (B + 1) = ε / 2 := by field_simp
    linarith
  calc |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := habs_le
    _ ≤ (s - 1) * B + ε / 2 := hbound
    _ < ε := hfin

end

theorem deriv_gamma_add_γ_eq_zero : deriv Gamma 1 + γ = 0 := by

  have key : ∀ s : ℝ, 1 < s →
      (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s) = deriv Gamma 1 + γ := by
    intro s hs
    have h := log_zeta_eq s hs
    linarith

  have hconst : Filter.Tendsto
      (fun s : ℝ => (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (deriv Gamma 1 + γ)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (key s hs).symm

  have hlim := log_zeta_limit.sub sub_one_mul_integral_E₂Λ_tendsto
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique hconst hlim

theorem γ.eq_eulerMascheroni : γ = eulerMascheroniConstant := by
  linarith [Real.eulerMascheroniConstant_eq_neg_deriv, deriv_gamma_add_γ_eq_zero]

theorem sum_mangoldt_div_log_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) = log (log x) + eulerMascheroniConstant + E₂Λ x := by
    grind [γ.eq_eulerMascheroni]

lemma HasSum_log_one_sub_one_div_prime {p : ℕ} (hp : p.Prime) :
    HasSum (fun n : ℕ ↦ (-1 : ℝ) / (( n + 1) * p ^ (n + 1))) (log (1 - 1 / p)) := by
  convert! Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / p) _|>.neg using 1
  · ext
    rw [div_pow, one_pow, div_div]
    ring
  · ring
  · simp only [one_div, abs_inv, Nat.abs_cast]
    exact inv_lt_one_of_one_lt₀ (mod_cast hp.one_lt)

noncomputable abbrev M_eq_f (n : ℕ) :=
    if ¬n.Prime then Λ n /(n * log n) else 0

lemma M_eq_f.sum_primes :
    ∑' (p : Nat.Primes), M_eq_f p = 0 := by
  convert! tsum_zero with p
  grind

lemma tsum_primes_eq_tsum_ite (f : ℕ → ℝ) :
    ∑' (n : Nat.Primes), f n = ∑' (n : ℕ), if n.Prime then f n else 0 := by
  convert! _root_.tsum_subtype Nat.Prime f using 2
  ext
  simp [Set.indicator]
  congr

noncomputable def E₃ (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, log (1 - (1:ℝ) / p) + log (log x) + eulerMascheroniConstant

theorem prod_one_minus_div_prime_eq {x : ℝ} (hx : 1 < x) :
    ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p) =
      exp (-eulerMascheroniConstant) * exp (E₃ x) / log x := by
  have hlog : 0 < log x := log_pos hx
  have hpos : ∀ {p : ℕ}, p.Prime → (0 : ℝ) < 1 - 1 / p := fun {p} hp ↦ by
    have : (2 : ℝ) ≤ p := mod_cast hp.two_le
    grind [one_div_le_one_div_of_le two_pos this]
  rw [E₃, exp_add, exp_add, exp_sum, exp_log hlog, exp_neg,
    prod_congr rfl fun p hp ↦ exp_log (hpos (mem_filter.mp hp).2)]
  field_simp

noncomputable abbrev M_eq_summand (p : ℕ) := if p.Prime then log (1 - 1 / p) + 1 / p else 0

lemma M_eq_summand_bound (n : ℕ) :
    |M_eq_summand n| ≤ 2 / n ^ 2 := by
  unfold M_eq_summand
  split_ifs with h
  · trans 1 / n ^ 2 / (1 - 1 / n)
    · convert abs_log_sub_add_sum_range_le (x := 1 / n) _ 1 using 1
      · rw [add_comm]
        simp
      · rw [abs_of_nonneg (by simp)]
        ring
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast h.one_lt)
    rw [(by ring : (2 : ℝ) / n ^ 2 = 1 / n ^ 2 / (1 / 2))]
    gcongr
    suffices (1 : ℝ) / n ≤ 1 / 2 by linarith
    gcongr
    exact_mod_cast h.two_le
  · rw [abs_zero]
    positivity

lemma M_eq_summable : Summable M_eq_summand := by
  apply Summable.of_abs
  exact Summable.of_nonneg_of_le (by simp) M_eq_summand_bound (Summable.const_div (by simp) _)

lemma M_eq_f.summable : Summable M_eq_f := by
  refine (vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)).of_norm_bounded_eventually_nat ?_
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 1 ≤ log (n : ℝ) := (le_log_iff_exp_le (by linarith : 0 < (n : ℝ))).2
    (exp_one_lt_three.le.trans hn')
  by_cases hp : n.Prime
  · simp [M_eq_f, hp]
  · simp only [M_eq_f, hp, not_false_eq_true, if_true, if_false]
    have hΛ : vonMangoldt.residueClass (0 : ZMod 1) n = Λ n := by
      simp [vonMangoldt.residueClass, Set.indicator, Subsingleton.elim (n : ZMod 1) 0]
    rw [hΛ, ← div_div, Real.norm_of_nonneg (by positivity)]
    exact div_le_self (by positivity) hl

lemma tsum_M_eq_f_eq_tsum :
    -∑' (n : ℕ), M_eq_f n = ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers M_eq_f.summable
    (fun n hn ↦ (by simp_all [vonMangoldt_ne_zero_iff])), M_eq_f.sum_primes, zero_add,
    tsum_primes_eq_tsum_ite (fun p ↦ ∑' (k : ℕ), M_eq_f (p ^ (k + 2))), ← tsum_neg]
  refine tsum_congr fun n ↦ ?_
  split_ifs with hn
  · rw [← HasSum_log_one_sub_one_div_prime hn|>.tsum_eq, HasSum_log_one_sub_one_div_prime hn|>.summable.tsum_eq_zero_add]
    simp only [ite_not, Nat.cast_pow, log_pow, Nat.cast_add, Nat.cast_ofNat, CharP.cast_eq_zero,
      zero_add, pow_one, one_mul, Nat.cast_one, one_div]
    trans -∑' (k : ℕ), (1 : ℝ) / ((k + 2) * n ^ (k + 2))
    · congr
      ext k
      have : ¬(Nat.Prime (n ^ (k + 2))) := by exact Nat.Prime.not_prime_pow (by grind)
      simp only [this, ↓reduceIte, one_div, mul_inv_rev]
      rw [vonMangoldt_apply_pow (by grind), vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · rw [← tsum_neg]
      ring_nf
      congr
      ext
      ring_nf
  · ring

private lemma partial_zero_floor {f : ℕ → ℝ} (hf : Summable f) (h0 : f 0=0) :
    Tendsto (fun x : ℝ => ∑ n ∈ Ioc 0 ⌊x⌋₊, f n) atTop (𝓝 (∑' n, f n)) := by
  have h := hf.hasSum.tendsto_sum_nat.comp ((tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_atTop (α:=ℝ)))
  apply h.congr
  intro x
  change ∑ n ∈ range (⌊x⌋₊+1), f n = _
  rw [Nat.range_succ_eq_Icc_zero, ←add_sum_Ioc_eq_sum_Icc (Nat.zero_le _), h0, zero_add]

lemma qualitative_product_error (hf : Summable M_eq_f)
    (cancel : -(∑' n : ℕ, M_eq_f n)=∑' p : ℕ, M_eq_summand p) :
    Tendsto E₃ atTop (𝓝 0) := by
  have hs := partial_zero_floor M_eq_summable (by simp [M_eq_summand])
  have hn := partial_zero_floor hf (by simp [M_eq_f])
  have herr : Tendsto E₂Λ atTop (𝓝 0) := (isLittleO_one_iff ℝ).mp E₂Λ.bound'
  have both := (hs.add hn).sub herr
  rw [←cancel, neg_add_cancel, sub_zero] at both
  apply both.congr
  intro x
  have split (n : ℕ) : M_eq_summand n + M_eq_f n =
      (if n.Prime then log (1-1/(n:ℝ)) else 0) + Λ n / (n*log n) := by
    by_cases prime : n.Prime
    · simp only [M_eq_summand,M_eq_f,prime,not_true_eq_false,↓reduceIte,add_zero,
        vonMangoldt_apply_prime prime]
      have ne : log n ≠ 0 := by simp; grind [prime.two_le]
      field_simp
    · simp [M_eq_summand,M_eq_f,prime]
  change (∑ p ∈ Ioc 0 ⌊x⌋₊, M_eq_summand p) + (∑ p ∈ Ioc 0 ⌊x⌋₊, M_eq_f p) - E₂Λ x = _
  rw [←sum_add_distrib]
  simp_rw [split]
  rw [sum_add_distrib, sum_mangoldt_div_log_eq, E₃, sum_filter]
  ring


end Mertens
end

end
section
/- Reconstruct Mertens's constant from the convergent logarithmic correction.
Uses the quantitative tail bound from the PrimeNumberTheoremAnd Mertens proof. -/
open Real MeasureTheory Set Finset Filter Asymptotics Topology
namespace Mertens
noncomputable def M : ℝ := (∑' n:ℕ, M_eq_summand n) + eulerMascheroniConstant
lemma sum_one_div_sq_le {N : ℝ} (hN : 1 ≤ N) :
    ∑' (n : ℕ), (1 : ℝ) / (n + N) ^ 2 ≤ 2 / N := by
  grw [AntitoneOn.tsum_le_integral (f := (fun t ↦ 1 / (t + N) ^ 2))]
  · have hd : ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ -1 / (t + N)) (1 / (x + N) ^ 2) x := by
      intro t ht
      convert! HasDerivAt.fun_div (d' := (1 : ℝ)) (hasDerivAt_const ..) _ _ using 1
      · ring
      · simpa using hasDerivAt_id' t
      · simp at ht
        linarith
    have lim : Tendsto (fun t ↦ -1 / (t + N)) atTop (nhds 0) := by
      exact (tendsto_atTop_add_const_right atTop N tendsto_id).const_div_atTop _
    rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun _ _ ↦ (by positivity)) lim]
    ring_nf
    rw [mul_two]
    gcongr
    field_simp
    exact hN
  · unfold AntitoneOn
    intro a ha b hb h
    beta_reduce
    simp at ha hb
    gcongr
  · convert! integrableOn_add_rpow_Ioi_of_lt (by norm_num : (-2 : ℝ) < -1) (by linarith : -N < 0) using 2
    simp
  · exact fun _ _ ↦ (by positivity)

lemma sum_M_eq_summand_le {N : ℕ} (hN : 0 < N) :
    |∑ n ∈ range N, M_eq_summand n - (M - eulerMascheroniConstant)| ≤ 4 / N := by
  rw [show M - eulerMascheroniConstant = ∑' n, M_eq_summand n by simp [M], ← M_eq_summable.sum_add_tsum_nat_add N]
  simp only [sub_add_cancel_left, abs_neg]
  rw [← norm_eq_abs]
  have summable := summable_nat_add_iff N|>.mpr M_eq_summable.norm
  apply norm_tsum_le_tsum_norm summable|>.trans
  apply Summable.tsum_le_tsum (fun _ ↦ M_eq_summand_bound _) summable _|>.trans
  · conv => lhs; arg 1; ext; rw [← mul_one_div]
    rw [tsum_mul_left]
    push_cast
    grw [sum_one_div_sq_le (mod_cast hN)]
    ring_nf
    rfl
  · exact (summable_nat_add_iff N|>.mpr (summable_one_div_nat_pow.mpr one_lt_two))|>.const_div _

lemma sum_M_eq_summand_le' {x : ℝ} (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - eulerMascheroniConstant)| ≤ 4 / x := by
  have := sum_M_eq_summand_le (by grind : 0 < ⌊x⌋₊ + 1)
  rw [Nat.range_eq_Icc_zero_sub_one _ (by grind), ← add_sum_Ioc_eq_sum_Icc (by grind),
    (by simp : M_eq_summand 0 = 0), zero_add] at this
  simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one] at this
  grw [this]
  gcongr
  exact Nat.lt_floor_add_one _|>.le


end Mertens
namespace LagariasComparison
private theorem factor_pos {N p : ℕ} (hp : p ∈ Nat.primesLE N) : 0 < 1 - 1/(p : ℝ) := by
  have prime := Nat.prime_of_mem_primesLE hp
  have one : (1 : ℝ) < p := by exact_mod_cast prime.one_lt
  exact sub_pos.mpr ((div_lt_one (by linarith)).mpr one)

private theorem log_product (x : ℝ) :
    log (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - 1/(p:ℝ))) =
      (∑ n ∈ Ioc 0 ⌊x⌋₊, Mertens.M_eq_summand n) -
        ∑ p ∈ Nat.primesLE ⌊x⌋₊, 1/(p:ℝ) := by
  rw [Real.log_prod (fun p hp => (factor_pos hp).ne')]
  simp only [Mertens.M_eq_summand]
  rw [← Finset.sum_filter, ← Nat.primesLE_eq_filter_Ioc_zero,Finset.sum_add_distrib]
  ring

private theorem tangent {a b : ℝ} (ha : 0<a) (hb : 0<b) : log a-log b ≤ (a-b)/b := by
  calc
    log a - log b = log (a/b) := (log_div ha.ne' hb.ne').symm
    _ ≤ a/b-1 := log_le_sub_one_of_pos (div_pos ha hb)
    _ = (a-b)/b := by field_simp

private theorem theta_gt_one {x : ℝ} (hx : 3≤x) : 1 < Chebyshev.theta x := by
  have h3 : Chebyshev.theta (3:ℝ) = log 6 := by
    rw [Chebyshev.theta_eq_log_primorial,show Nat.floor (3:ℝ)=3 by norm_num,
      show primorial 3=6 by decide]
    norm_num
  have h6 : 1<log (6:ℝ) :=
    (Real.lt_log_iff_exp_lt (by norm_num)).2 (Real.exp_one_lt_three.trans (by norm_num))
  exact (h6.trans_eq h3.symm).trans_le (Chebyshev.theta_mono hx)

private theorem height_shift {x : ℝ} (hx : 3≤x) :
    log (log (Chebyshev.theta x)) - log (log x) ≤ (Chebyshev.theta x-x)/(x*log x) := by
  have pos : 0<x := by linarith
  have lp : 0 < log x := log_pos (by linarith)
  have ht := theta_gt_one hx
  calc
    _ ≤ (log (Chebyshev.theta x) - log x)/log x := tangent (log_pos ht) lp
    _ ≤ ((Chebyshev.theta x - x)/x) /log x :=
      div_le_div_of_nonneg_right (tangent (by linarith) pos) lp.le
    _ = _ := by rw [div_div]

/-- Combining concavity twice with the signed Mertens remainder bounds the finite product.
The parameter K is the complete theta-tail identified by partial summation. -/
theorem finite_product_bound {x K : ℝ} (hx : 3≤x)
    (reciprocal : (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1/(p:ℝ)) =
      log (log x) + Mertens.M + (Chebyshev.theta x-x)/(x*log x) - K) :
    log (exp eulerMascheroniConstant * log (Chebyshev.theta x) *
      ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1-1/(p:ℝ))) ≤ K + 4/x := by
  have p := Finset.prod_pos (s := Nat.primesLE ⌊x⌋₊) (fun i hi => factor_pos hi)
  have l := (log_pos (theta_gt_one hx)).ne'
  rw [log_mul (mul_ne_zero (exp_pos _).ne' l) p.ne',
    log_mul (exp_pos _).ne' l,log_exp,log_product,reciprocal]
  have h := Mertens.sum_M_eq_summand_le' (show 2≤x by linarith)
  linarith only [(abs_le.mp h).2,height_shift hx]


theorem prime_reciprocal_limit :
    Tendsto (fun x : ℝ => (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1/(p:ℝ)) - log (log x)) atTop (𝓝 Mertens.M) := by
  have hraw := Mertens.M_eq_summable.hasSum.tendsto_sum_nat.comp
    ((tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_atTop (α := ℝ)))
  have partials : Tendsto (fun x:ℝ => ∑ n ∈ Ioc 0 ⌊x⌋₊, Mertens.M_eq_summand n)
      atTop (𝓝 (∑' n, Mertens.M_eq_summand n)) := by
    apply hraw.congr
    intro x
    change ∑ n ∈ range (⌊x⌋₊+1), Mertens.M_eq_summand n = _
    rw [Nat.range_succ_eq_Icc_zero, ←add_sum_Ioc_eq_sum_Icc (Nat.zero_le _),
      show Mertens.M_eq_summand 0=0 by simp [Mertens.M_eq_summand], zero_add]
  have err := Mertens.qualitative_product_error Mertens.M_eq_f.summable Mertens.tsum_M_eq_f_eq_tsum
  have both := (partials.sub err).add (tendsto_const_nhds (x := eulerMascheroniConstant))
  rw [sub_zero] at both
  apply both.congr
  intro x
  rw [Mertens.E₃, ← Nat.primesLE_eq_filter_Ioc_zero]
  have h := log_product x
  rw [Real.log_prod (fun i hi => (factor_pos hi).ne')] at h
  linarith only [h]

end LagariasComparison

end
section
/- Partial summation in the Rosser–Schoenfeld identity for prime reciprocals. -/
namespace LagariasPartial
open Real Finset MeasureTheory Filter
open scoped Topology
private theorem recipDeriv {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s : ℝ => (s * log s)⁻¹)
      (-((1 / log t + 1 / log t ^ 2) / t ^ 2)) t := by
  have ht0 := (one_pos.trans ht).ne'
  have hl := (log_pos ht).ne'
  convert ((hasDerivAt_id t).mul (hasDerivAt_log ht0)).inv (mul_ne_zero ht0 hl) using 1 <;> first | rfl | simp [Pi.mul_apply,id_eq,field]

private theorem primitive {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s : ℝ => log (log s) - (log s)⁻¹)
      (t * ((1 / log t + 1 / log t ^ 2) / t ^ 2)) t := by
  have ht0 := (one_pos.trans ht).ne'
  have hl := (log_pos ht).ne'
  have h := hasDerivAt_log ht0
  convert (h.log hl).sub (h.inv hl) using 1 <;> first | rfl | (field_simp; ring)

theorem reciprocal_finite {x y : ℝ} (hx : 2 ≤ x) (hy : x ≤ y) :
    (∑ p ∈ Nat.primesLE ⌊y⌋₊, 1/(p:ℝ)) - log (log y)
    - ((∑ p ∈ Nat.primesLE ⌊x⌋₊, 1/(p:ℝ)) - log (log x)) =
    (Chebyshev.theta y-y)/(y*log y) - (Chebyshev.theta x-x)/(x*log x) +
      ∫ t in x..y, (Chebyshev.theta t-t)*((1/log t+1/log t^2)/t^2) := by
  classical
  let a : ℕ → ℝ := fun n => if n.Prime then log n else 0
  let f : ℝ → ℝ := fun t => (t*log t)⁻¹
  let K : ℝ → ℝ := fun t => (1/log t+1/log t^2)/t^2
  have hi (t : ℝ) (ht : t ∈ Set.Icc x y) : 1<t := by linarith [ht.1]
  have cont : ContinuousOn K (Set.Icc x y) := by
    intro t ht
    have ht0 := (one_pos.trans (hi t ht)).ne'
    have hl := (log_pos (hi t ht)).ne'
    dsimp [K]
    exact (by fun_prop (disch := norm_num [ht0,hl]) : ContinuousAt (fun t : ℝ => (1/log t+1/log t^2)/t^2) t).continuousWithinAt
  have der : ∀ t ∈ Set.Icc x y, deriv f t = -K t :=
    fun t ht => (recipDeriv (hi t ht)).deriv
  have sumTheta (t : ℝ) : (∑ n ∈ Icc 0 ⌊t⌋₊, a n) = Chebyshev.theta t := by
    rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  have abel := sum_mul_eq_sub_sub_integral_mul a (f:=f) (by linarith : 0≤x) hy
    (fun t ht => (recipDeriv (hi t ht)).differentiableAt)
    ((cont.neg.congr der).integrableOn_Icc)
  simp only [sumTheta] at abel
  have value (n : ℕ) : f n * a n = (if n.Prime then 1 / (n:ℝ) else 0) := by
    by_cases hn : n.Prime
    · have h0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne_zero
      have h1 : (1:ℝ) < n := by exact_mod_cast hn.one_lt
      have hl := (log_pos h1).ne'
      simp [a, f, hn, field]
    · simp [a,hn]
  simp_rw [value] at abel
  have hsum (z : ℝ) : (∑ p ∈ Nat.primesLE ⌊z⌋₊, 1/(p:ℝ)) =
      ∑ n ∈ Ioc 0 ⌊z⌋₊, if n.Prime then 1/(n:ℝ) else 0 := by
    rw [Nat.primesLE_eq_filter_Ioc_zero,Finset.sum_filter]
  rw [hsum,hsum]
  have agg : Ioc 0 ⌊x⌋₊ ∪ Ioc ⌊x⌋₊ ⌊y⌋₊ = Ioc 0 ⌊y⌋₊ := by
    ext i
    have hxy := Nat.floor_le_floor hy
    simp
    omega
  have dj : Disjoint (Ioc 0 ⌊x⌋₊) (Ioc ⌊x⌋₊ ⌊y⌋₊) :=
    Finset.disjoint_left.mpr fun _ h g => (not_lt_of_ge (mem_Ioc.mp h).2) (mem_Ioc.mp g).1
  rw [← agg, Finset.sum_union dj]
  have integ := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f:=fun s : ℝ => log (log s) - (log s)⁻¹)
    (f':=fun t => t*K t)
    (fun t h => primitive (hi t (Set.uIcc_of_le hy ▸ h)))
    ((continuousOn_id.mul cont).intervalIntegrable_of_Icc hy)
  have intTheta : IntervalIntegrable (fun t => K t * Chebyshev.theta t) volume x y := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hy]
    exact (integrableOn_mul_sum_Icc (m:=0) a (by linarith : 0≤x) cont.integrableOn_Icc).congr_fun
      (fun t _ => by dsimp; rw [sumTheta]) measurableSet_Icc
  have intK : (∫ t in Set.Ioc x y, deriv f t * Chebyshev.theta t) =
      -(∫ t in x..y, K t * Chebyshev.theta t) := by
    rw [← intervalIntegral.integral_of_le hy, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    change deriv f t * _ = -_
    rw [der _ (Set.uIcc_of_le hy ▸ ht)]
    ring
  rw [intK] at abel
  change _ = _ + ∫ t in x..y, (Chebyshev.theta t-t)*K t
  have split : (∫ t in x..y, (Chebyshev.theta t-t)*K t) =
      (∫ t in x..y, K t * Chebyshev.theta t) - ∫ t in x..y, t*K t := by
    have ig : IntervalIntegrable (fun t => t * K t) volume x y := (continuousOn_id.mul cont).intervalIntegrable_of_Icc hy
    rw [← intervalIntegral.integral_sub intTheta ig]
    exact intervalIntegral.integral_congr fun _ _ => by ring
  rw [split,integ,abel]
  dsimp [f]
  have lx : log x ≠ 0 := (log_pos (by linarith)).ne'
  have ly : log y ≠ 0 := (log_pos (by linarith)).ne'
  have xx : x ≠ 0 := by linarith
  have yy : y ≠ 0 := by linarith
  field_simp
  ring
theorem theta_endpoint :
    Tendsto (fun t:ℝ => (Chebyshev.theta t-t)/(t*log t)) atTop (𝓝 0) := by
  have h := tendsto_log_atTop.const_div_atTop (log 4+1)
  apply squeeze_zero_norm' (a:=fun t : ℝ => (log 4+1)/log t) ?_ h
  filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
  have hp : 0<t := one_pos.trans ht
  have hl := log_pos ht
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos hp hl)]
  apply (div_le_div_iff₀ (mul_pos hp hl) hl).2
  have bh : |Chebyshev.theta t-t| ≤ (log 4+1)*t := by
    rw [abs_le]
    constructor
    · nlinarith [Chebyshev.theta_nonneg t, mul_nonneg (log_nonneg (by norm_num : (1:ℝ)≤4)) hp.le]
    · linarith [Chebyshev.theta_le_log4_mul_x hp.le]
  nlinarith [mul_le_mul_of_nonneg_right bh hl.le]

theorem reciprocal_eq {M x : ℝ} (hx : 2 ≤ x)
    (lim : Tendsto (fun y:ℝ => (∑ p ∈ Nat.primesLE ⌊y⌋₊, 1/(p:ℝ)) - log (log y))
      atTop (𝓝 M))
    (integr : IntegrableOn (fun t:ℝ => (Chebyshev.theta t-t)*((1/log t+1/log t^2)/t^2))
      (Set.Ioi x)) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1/(p:ℝ)) =
      log (log x)+M+(Chebyshev.theta x-x)/(x*log x) -
        ∫ t in Set.Ioi x, (Chebyshev.theta t-t)*((1/log t+1/log t^2)/t^2) := by
  have tail := intervalIntegral_tendsto_integral_Ioi x integr (tendsto_id : Tendsto (fun y : ℝ => y) atTop atTop)
  let P := (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1/(p:ℝ))-log (log x)
  let e := (Chebyshev.theta x-x)/(x*log x)
  have lhs := lim.sub (tendsto_const_nhds (x:=P))
  have rhs := (theta_endpoint.sub (tendsto_const_nhds (x:=e))).add tail
  have eq := tendsto_nhds_unique (f:=(fun y:ℝ =>
      ((∑ p ∈ Nat.primesLE ⌊y⌋₊, 1/(p:ℝ)) - log (log y)) - P)) lhs
      (rhs.congr' (by filter_upwards [eventually_ge_atTop x] with y hy using (reciprocal_finite hx hy).symm))
  dsimp [P,e] at eq
  linarith
end LagariasPartial

end
section
open MeasureTheory Set Real Filter

namespace LagariasComparison

/-- Kimihiro's Robin1984 formalization of Nicolas's argument bounds the integrable gap between
the two Chebyshev tails by four times the minus-three-halves power.
Here we use the gap directly, which also covers divergent individual Bochner integrals. -/
theorem theta_tail_le_psi_tail {x : ℝ} (hx : 3 ≤ x) :
    (∫ t in Ioi x, (Chebyshev.theta t-t) * ((1/log t+1/(log t)^2)/t^2)) ≤
      ∫ t in Ioi x, (Chebyshev.psi t-t) * ((1/log t+1/(log t)^2)/t^2) := by
  let K (t : ℝ) := (1/log t+1/(log t)^2)/t^2
  let A (t : ℝ) := (Chebyshev.theta t-t) * K t
  let B (t : ℝ) := (Chebyshev.psi t-t) * K t
  let D (t : ℝ) := (Chebyshev.psi t-Chebyshev.theta t) * K t
  change (∫ t in Ioi x, A t) ≤ ∫ t in Ioi x, B t
  have hg (t : ℝ) : A t + D t = B t := by dsimp [A, D, B]; ring
  have hK {t : ℝ} (ht : t ∈ Ioi x) : 0 ≤ K t := by
    have hl : 0 ≤ log t := log_nonneg (by have := hx.trans ht.le; linarith)
    dsimp [K]
    positivity
  have hD0 {t : ℝ} (ht : t ∈ Ioi x) : 0 ≤ D t :=
    mul_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi t)) (hK ht)
  have hD : IntegrableOn D (Ioi x) := by
    apply Integrable.mono' (g := fun t : ℝ => 4 * t ^ (-(3 / 2 : ℝ)))
    · exact (integrableOn_Ioi_rpow_of_lt (by norm_num) (by linarith)).const_mul 4
    · have hKm : Measurable K := by dsimp [K]; measurability
      exact ((Chebyshev.psi_mono.measurable.sub Chebyshev.theta_mono.measurable).mul
        hKm).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht3 : 3 < t := hx.trans_lt ht
      have htPos : 0 < t := by linarith
      have hLog : 1 < log t := (Real.lt_log_iff_exp_lt htPos).2 (Real.exp_one_lt_three.trans ht3)
      have hLogPos : 0 < log t := by linarith
      have hInvLog : 1 / log t ≤ 1 := (div_le_one hLogPos).2 hLog.le
      have hPower : sqrt t / t ^ 2 = t ^ (-(3 / 2 : ℝ)) := by
        rw [sqrt_eq_rpow, ← Real.rpow_natCast t 2, div_eq_mul_inv,
            ← Real.rpow_neg htPos.le, ← Real.rpow_add htPos]
        norm_num
      calc
        ‖D t‖ = D t := by rw [Real.norm_eq_abs, abs_of_nonneg (hD0 ht)]
        _ ≤ (2 * sqrt t * log t) * K t :=
          mul_le_mul_of_nonneg_right (Chebyshev.psi_sub_theta_le (by linarith)) (hK ht)
        _ = (2 * sqrt t / t ^ 2) * (1 + 1 / log t) := by
          dsimp [K]
          field_simp [htPos.ne', hLogPos.ne']
        _ ≤ (2 * sqrt t / t ^ 2) * 2 := by gcongr; linarith
        _ = 4 * t ^ (-(3 / 2 : ℝ)) := by
          rw [show 2 * sqrt t / t ^ 2 = 2 * (sqrt t / t ^ 2) by ring, hPower]
          ring
  by_cases hA : IntegrableOn A (Ioi x)
  · have hB : IntegrableOn B (Ioi x) :=
      (hA.add hD).congr_fun (fun t _ => hg t) measurableSet_Ioi
    exact setIntegral_mono_on hA hB measurableSet_Ioi
      (fun t ht => (le_add_of_nonneg_right (hD0 ht)).trans_eq (hg t))
  · have hB : ¬IntegrableOn B (Ioi x) := by
      intro hB
      apply hA
      apply (hB.sub hD).congr_fun _ measurableSet_Ioi
      intro t _
      change B t - D t = A t
      linarith [hg t]
    rw [integral_undef hA, integral_undef hB]

/-- Given the theta comparison, replace its tail by the psi tail of the public reduction. -/
theorem mertens_comparison_of_theta
    (h : ∀ᶠ x : ℝ in atTop,
      log (exp eulerMascheroniConstant * log (Chebyshev.theta x) *
        ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1-1/(p:ℝ))) ≤
      (∫ t in Ioi x, (Chebyshev.theta t-t) * ((1/log t+1/(log t)^2)/t^2))+4/x) :
    ∀ᶠ x : ℝ in atTop,
      log (exp eulerMascheroniConstant * log (Chebyshev.theta x) *
        ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1-1/(p:ℝ))) ≤
      (∫ t in Ioi x, (Chebyshev.psi t-t) * ((1/log t+1/(log t)^2)/t^2))+4/x := by
  filter_upwards [h, eventually_ge_atTop (3:ℝ)] with x bound hx
  exact bound.trans (add_le_add (theta_tail_le_psi_tail hx) le_rfl)

end LagariasComparison

end
namespace RobinConverse
open Real Filter MeasureTheory Set Asymptotics
open scoped Topology ArithmeticFunction.sigma
theorem rpow_neg_one_isLittleO_rpow_neg
    {b : Real} (hb : b < 1) :
    Asymptotics.IsLittleO atTop
      (fun x : Real => x ^ (-(1 : Real)))
      (fun x : Real => x ^ (-b)) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hDecay : Tendsto
      (fun x : Real => x ^ (-(1 - b))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hSmall : Filter.Eventually
      (fun x : Real => x ^ (-(1 - b)) < c) atTop :=
    hDecay.eventually_lt_const hc
  filter_upwards [hSmall, eventually_gt_atTop (0 : Real)] with x hxSmall hxPos
  have hRecipPos : 0 < x ^ (-(1 : Real)) :=
    Real.rpow_pos_of_pos hxPos _
  have hMainPos : 0 < x ^ (-b) := Real.rpow_pos_of_pos hxPos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hRecipPos,
    abs_of_pos hMainPos]
  have hFactor :
      x ^ (-(1 : Real)) = x ^ (-b) * x ^ (-(1 - b)) := by
    rw [<- Real.rpow_add hxPos]
    congr 1
    ring
  rw [hFactor]
  calc
    x ^ (-b) * x ^ (-(1 - b)) <= x ^ (-b) * c :=
      mul_le_mul_of_nonneg_left hxSmall.le hMainPos.le
    _ = c * x ^ (-b) := by ring


def LcmLoss : Prop := ∀ b : ℝ, 0<b → b<1/2 → ∀ ε : ℝ, 0<ε → ∀ᶠ x : ℝ in atTop,
  let n := Nat.lcmUpto ⌊x⌋₊;
  -(log (exp eulerMascheroniConstant * log (Chebyshev.theta x) *
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1-1/(p:ℝ)))) - ε*x^(-b) ≤
    log ((σ 1 n : ℝ)/n) - eulerMascheroniConstant - log (log (log n))

lemma height {P : ℕ} (hP : 40≤P) : (P:ℝ)/8 ≤ log (Nat.lcmUpto P) := by
  have P40 : (40:ℝ)≤P := by exact_mod_cast hP
  have Ppos : (0:ℝ)<P+1 := by positivity
  have hlog := log_le_sub_one_of_pos (show 0<((P:ℝ)+1)/4 by positivity)
  rw [log_div (by positivity) (by norm_num)] at hlog
  have hfour : log 4 < 2 := by
    rw [show (4:ℝ)=2*2 by norm_num,log_mul (by norm_num) (by norm_num)]
    linarith only [log_two_lt_d9]
  have hhalf : (1:ℝ)/2 < log 2 := by linarith only [log_two_gt_d9]
  have h := Chebyshev.psi_ge P
  rw [Chebyshev.psi_eq_log_lcmUpto] at h
  nlinarith [mul_le_mul_of_nonneg_left hhalf.le (show (0:ℝ)≤P by positivity)]


end RobinConverse


/- For the lcm of the integers up to N, the exponent of p is the integer
logarithm to base p of N. Separate the exact Euler factors from the tail
estimate: primes up to √N contribute O(√N/N), and larger primes contribute
O(∑_{k>√N} k⁻²). The change of height from theta to psi is absorbed below. -/
namespace RobinConverse.LossProof
open Real Filter Finset
open scoped ArithmeticFunction.sigma

def H1 : Prop := ∀ N : ℕ, 2 ≤ N →
  log ((σ 1 (Nat.lcmUpto N) : ℝ) / Nat.lcmUpto N) +
    log (∏ p ∈ Nat.primesLE N, (1-1/(p:ℝ))) =
    ∑ p ∈ Nat.primesLE N, log (1-1/(p:ℝ)^(p.log N + 1))

def H2 : Prop := ∃ K : ℝ, ∀ᶠ x : ℝ in atTop,
  -(∑ p ∈ Nat.primesLE ⌊x⌋₊, log (1-1/(p:ℝ)^(p.log ⌊x⌋₊ + 1))) ≤ K/sqrt x

lemma logs {u v : ℝ} (hu : exp 1 ≤ u) (hv : u ≤ v) :
    log (log v) - log (log u) ≤ (v-u)/u := by
  have up : 0 < u := (exp_pos _).trans_le hu
  have vp := up.trans_le hv
  have lu : 1 ≤ log u := (le_log_iff_exp_le up).mpr hu
  have lvp : 0 < log v := by linarith [log_le_log up hv]
  have lup : 0 < log u := by linarith
  have a := log_le_sub_one_of_pos (div_pos vp up)
  rw [log_div vp.ne' up.ne'] at a
  have b := log_le_sub_one_of_pos (div_pos lvp lup)
  rw [log_div lvp.ne' lup.ne'] at b
  have s : log v / log u - 1 = (log v-log u)/log u := by field_simp
  rw [s] at b
  have h := div_le_self (sub_nonneg.mpr (log_le_log up hv)) lu
  have e : v/u-1=(v-u)/u := by field_simp
  linarith

private lemma localFactor (p : ℝ) (hp : 1<p) (k : ℕ) :
    (∑ i ∈ range (k+1), p^i) / p^k * (1-1/p) = 1-1/p^(k+1) := by
  have h := geom_sum_mul p (k+1)
  have pn : p ≠ 0 := by linarith
  rw [pow_succ] at h ⊢
  field_simp
  nlinarith

private theorem exactFactors : H1 := by
  intro N _
  let S := Nat.primesLE N
  have prime (p : ℕ) (h : p ∈ S) : (1:ℝ)<p := by
    exact_mod_cast (Nat.prime_of_mem_primesLE h).one_lt
  have pos₁ (p : ℕ) (h : p ∈ S) : 0 < (1-1/(p:ℝ)) := by
    have hp := prime p h
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hp)
  have pos₂ (p : ℕ) (h : p ∈ S) : 0 < 1-1/(p:ℝ)^(p.log N+1) := by
    have hp := prime p h
    have a := one_lt_pow₀ hp (Nat.succ_ne_zero (p.log N))
    exact sub_pos.mpr ((div_lt_one (zero_lt_one.trans a)).mpr a)
  have sigma : (σ 1 (Nat.lcmUpto N) : ℝ) = ∏ p ∈ S, ∑ i ∈ range (p.log N+1), (p:ℝ)^i := by
    rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
      (Nat.lcmUpto_ne_zero N), Nat.primeFactors_lcmUpto]
    push_cast
    apply prod_congr rfl
    intro p hp
    simp [Nat.factorization_lcmUpto N (Nat.prime_of_mem_primesLE hp)]
  have lcm : (Nat.lcmUpto N : ℝ) = ∏ p ∈ S, (p:ℝ)^(p.log N) := by
    exact_mod_cast Nat.lcmUpto_eq_prod_pow_log N
  have ratio : 0 < (σ 1 (Nat.lcmUpto N) : ℝ) / Nat.lcmUpto N := by
    apply div_pos
    · exact_mod_cast ArithmeticFunction.sigma_pos 1 _ (Nat.lcmUpto_ne_zero N)
    · exact_mod_cast Nat.lcmUpto_pos N
  rw [← log_mul ratio.ne' (prod_pos pos₁).ne', ← log_prod (fun p h => (pos₂ p h).ne')]
  apply congrArg log
  rw [sigma,lcm,← prod_div_distrib,← prod_mul_distrib]
  exact prod_congr rfl fun p h => localFactor _ (prime _ h) _

private lemma logLoss {A : ℝ} (hA : 2 ≤ A) : -log (1-1/A) ≤ 2/A := by
  have pos : 0 < 1-1/A := by
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr (by linarith))
  have h := log_le_sub_one_of_pos (inv_pos.mpr pos)
  rw [log_inv] at h
  apply h.trans
  have e : (1-1/A)⁻¹ - 1 = 1/(A-1) := by
    have h₁ : A ≠ 0 := by linarith
    have h₂ : A-1 ≠ 0 := by linarith
    rw [show 1-1/A = (A-1)/A by field_simp, inv_div]
    field_simp
    ring
  rw [e,div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

private lemma telescope (m : ℝ) (n : ℕ) :
    ∑ i ∈ range n, (1/(m+i)-1/(m+i+1)) = 1/m-1/(m+n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ,ih];push_cast;ring_nf

private theorem tailEstimate : H2 := by
  refine ⟨24,?_⟩
  filter_upwards [eventually_ge_atTop (4:ℝ)] with x hx
  let m : ℝ := ⌊sqrt x⌋₊
  let N := ⌊x⌋₊
  have sq := sq_sqrt (by linarith : 0≤x)
  have sm := sqrt_nonneg x
  have ml : m ≤ sqrt x := Nat.floor_le sm
  have mu : sqrt x < m+1 := Nat.lt_floor_add_one _
  have mp : 0 < m := by nlinarith
  have nonneg (i : ℕ) : 0 ≤ 1/(m+i)-1/(m+i+1) := by
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  rw [← sum_neg_distrib]
  calc
    _ ≤ ∑ p ∈ Nat.primesLE N, 12 * (1/(m+p)-1/(m+p+1)) := by
      apply sum_le_sum
      intro p h
      have ph := Nat.prime_of_mem_primesLE h
      have p2 : (2:ℝ)≤p := by exact_mod_cast ph.two_le
      let A := (p:ℝ)^(p.log N+1)
      have nx := Nat.lt_pow_succ_log_self ph.one_lt N
      have nA : (N:ℝ)+1 ≤ A := by
        dsimp [A]
        exact_mod_cast (Nat.succ_le_of_lt nx)
      have xx : x < (N:ℝ)+1 := Nat.lt_floor_add_one _
      have kp : 0 < p.log N := Nat.log_pos_iff.mpr ⟨Nat.le_of_mem_primesLE h,ph.one_lt⟩
      have pA : (p:ℝ)^2 ≤ A := by
        dsimp only [A]
        exact pow_le_pow_right₀ (by linarith) (Nat.succ_le_succ kp)
      have den : (m+p)*(m+p+1) ≤ 6*A := by
        by_cases small : (p:ℝ) ≤ sqrt x
        · have a : m+p ≤ 2*sqrt x := by linarith
          have b : m+p+1 ≤ 3*sqrt x := by nlinarith
          nlinarith [mul_le_mul a b (by positivity) (by positivity)]
        · have a : m+p ≤ 2*p := by linarith
          have b : m+p+1 ≤ 3*p := by linarith
          nlinarith [mul_le_mul a b (by positivity) (by positivity)]
      apply (logLoss (A:=A) (by linarith)).trans
      have pos : 0 < m+(p:ℝ) := by positivity
      have pos' : 0 < m+(p:ℝ)+1 := by positivity
      have e : 12 * (1/(m+p)-1/(m+p+1)) = 12 / ((m+p)*(m+p+1)) := by field_simp;ring
      rw [e, div_le_div_iff₀ (by linarith) (mul_pos pos pos')]
      linarith
    _ ≤ ∑ p ∈ range (N+1), 12 * (1/(m+p)-1/(m+p+1)) := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact fun p h => mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_mem_primesLE h))
      · exact fun p _ _ => mul_nonneg (by norm_num) (nonneg p)
    _ ≤ 24 / sqrt x := by
      rw [← mul_sum,telescope]
      have h : 0 ≤ 1/(m+((N+1:ℕ):ℝ)) := by positivity
      have r : 12/m ≤ 24/sqrt x := by
        rw [div_le_div_iff₀ mp (sqrt_pos.2 (by linarith))]
        nlinarith
      apply le_trans _ r
      calc _ ≤ 12*(1/m) := mul_le_mul_of_nonneg_left (sub_le_self _ h) (by norm_num)
           _ = _ := by ring

theorem main : H1 → H2 → RobinConverse.LcmLoss := by
  rintro factors ⟨K,tail⟩ b hb bh ε he
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let D := 32*|C|+|K|+1
  have decay := (tendsto_rpow_atTop (show 0<(1/2:ℝ)-b by linarith)).eventually_ge_atTop (D/ε)
  have large := tendsto_sqrt_atTop.eventually_ge_atTop (32*|C|)
  filter_upwards [tail,decay,large,eventually_ge_atTop (128:ℝ)] with x ht hd hl hx
  let N := ⌊x⌋₊
  have xp : 0<x := by linarith
  have hp : 0<sqrt x := sqrt_pos.2 xp
  have sq := sq_sqrt xp.le
  have n40 : 40 ≤ N := Nat.le_floor (by push_cast; linarith)
  have psi : Chebyshev.psi x = log (Nat.lcmUpto N) := by
    rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.psi_eq_log_lcmUpto]
  have height := RobinConverse.height n40
  have xf := Nat.lt_floor_add_one x
  change x < (N:ℝ)+1 at xf
  have loss := hC x
  have small := mul_le_mul_of_nonneg_right hl hp.le
  have theta : x/32 ≤ Chebyshev.theta x := by
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self C) hp.le]
  have tp : 0 < Chebyshev.theta x := by linarith
  have te : exp 1 ≤ Chebyshev.theta x := by linarith [exp_one_lt_three]
  have cmp := logs te (Chebyshev.theta_le_psi x)
  have ratio : (Chebyshev.psi x-Chebyshev.theta x)/Chebyshev.theta x ≤ 32*|C|/sqrt x := by
    rw [div_le_div_iff₀ tp hp]
    calc _ ≤ C*sqrt x*sqrt x := mul_le_mul_of_nonneg_right loss hp.le
         _ ≤ |C| * x := by nlinarith [mul_le_mul_of_nonneg_right (le_abs_self C) xp.le, congrArg (C*·) sq]
         _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left theta (abs_nonneg C)]
  have poweq : x^(1/2-b:ℝ)=sqrt x*x^(-b) := by
    rw [sqrt_eq_rpow,←rpow_add xp]
    ring_nf
  change D/ε ≤ x^(1/2-b:ℝ) at hd
  rw [poweq,div_le_iff₀ he] at hd
  have allowed : (32*|C|+K)/sqrt x ≤ ε*x^(-b) := by
    rw [div_le_iff₀ hp]
    dsimp [D] at hd
    linarith [le_abs_self K]
  have Ppos : 0 < ∏ p ∈ Nat.primesLE N, (1-1/(p:ℝ)) := by
    apply prod_pos
    intro p h
    have p1 : (1:ℝ)<p := by exact_mod_cast (Nat.prime_of_mem_primesLE h).one_lt
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr p1)
  have F := factors N (by omega)
  change -log (exp eulerMascheroniConstant * log (Chebyshev.theta x) * _) - _ ≤ _
  rw [log_mul (mul_pos (exp_pos _) (log_pos (by linarith))).ne' Ppos.ne',
    log_mul (exp_pos _).ne' (log_pos (by linarith : 1 < Chebyshev.theta x)).ne',log_exp]
  have combined := cmp.trans ratio
  rw [psi] at combined
  rw [add_div] at allowed
  linarith

end RobinConverse.LossProof

theorem RobinConverse.arithmetic : RobinConverse.LcmLoss := RobinConverse.LossProof.main RobinConverse.LossProof.exactFactors RobinConverse.LossProof.tailEstimate
end

section
/- An elementary, finite-interval primitive for the weighted theta error,
using the finite Abel identity and Mertens's theorem. -/
namespace RobinConverse
open Filter Real Set MeasureTheory
open scoped Topology

noncomputable def compensatedTheta (x : ℝ) : ℝ :=
  Mertens.M - ((∑ p ∈ Nat.primesLE ⌊x⌋₊, 1/(p:ℝ)) - log (log x)) +
    (Chebyshev.theta x-x)/(x*log x)

theorem compensatedTheta_tendsto :
    Tendsto compensatedTheta atTop (𝓝 0) := by
  unfold compensatedTheta
  simpa only [sub_self,zero_add] using
    ((tendsto_const_nhds (x := Mertens.M)).sub LagariasComparison.prime_reciprocal_limit).add
      LagariasPartial.theta_endpoint

theorem compensatedTheta_sub {x y : ℝ} (hx : 2 ≤ x) (hy : x ≤ y) :
    compensatedTheta x - compensatedTheta y =
      ∫ t in x..y, (Chebyshev.theta t - t)*((1/log t+1/log t^2)/t^2) := by
  unfold compensatedTheta
  linarith only [LagariasPartial.reciprocal_finite hx hy]

theorem conditional_theta_tail {x : ℝ} (hx : 2 ≤ x) :
    Tendsto (fun y : ℝ => ∫ t in x..y, (Chebyshev.theta t - t)*((1/log t+1/log t^2)/t^2))
      atTop (𝓝 (compensatedTheta x)) := by
  have h := (tendsto_const_nhds (x := compensatedTheta x)).sub compensatedTheta_tendsto
  rw [sub_zero] at h
  exact h.congr' ((eventually_ge_atTop x).mono (fun y hy => compensatedTheta_sub hx hy))

theorem finite_product_compensated {x : ℝ} (hx : 3 ≤ x) :
    log (exp eulerMascheroniConstant * log (Chebyshev.theta x) *
      ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1-1/(p:ℝ))) ≤ compensatedTheta x + 4/x := by
  apply LagariasComparison.finite_product_bound hx
  unfold compensatedTheta
  ring

end RobinConverse

namespace RobinConverse
open MeasureTheory Real Set Filter
open scoped Topology

noncomputable def primePowerGap (t : ℝ) :=
  (Chebyshev.psi t - Chebyshev.theta t) * ((1/log t+1/log t^2)/t^2)

theorem primePowerGap_integrable {x : ℝ} (hx : 3 ≤ x) : IntegrableOn primePowerGap (Ioi x) := by
  let K (t : ℝ) := (1/log t+1/log t^2)/t^2
  let D (t : ℝ) := (Chebyshev.psi t-Chebyshev.theta t)*K t
  have hK {t : ℝ} (ht : t ∈ Ioi x) : 0 ≤ K t := by
    have hl : 0 ≤ log t := log_nonneg (by have := hx.trans ht.le; linarith)
    dsimp [K]
    positivity
  have hD0 {t : ℝ} (ht : t ∈ Ioi x) : 0 ≤ D t :=
    mul_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi t)) (hK ht)
  have hD : IntegrableOn D (Ioi x) := by
    apply Integrable.mono' (g := fun t : ℝ => 4 * t ^ (-(3 / 2 : ℝ)))
    · exact (integrableOn_Ioi_rpow_of_lt (by norm_num) (by linarith)).const_mul 4
    · have hKm : Measurable K := by dsimp [K]; measurability
      exact ((Chebyshev.psi_mono.measurable.sub Chebyshev.theta_mono.measurable).mul
        hKm).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht3 : 3 < t := hx.trans_lt ht
      have htPos : 0 < t := by linarith
      have hLog : 1 < log t := (Real.lt_log_iff_exp_lt htPos).2 (Real.exp_one_lt_three.trans ht3)
      have hLogPos : 0 < log t := by linarith
      have hInvLog : 1 / log t ≤ 1 := (div_le_one hLogPos).2 hLog.le
      have hPower : sqrt t / t ^ 2 = t ^ (-(3 / 2 : ℝ)) := by
        rw [sqrt_eq_rpow, ← Real.rpow_natCast t 2, div_eq_mul_inv,
            ← Real.rpow_neg htPos.le, ← Real.rpow_add htPos]
        norm_num
      calc
        ‖D t‖ = D t := by rw [Real.norm_eq_abs, abs_of_nonneg (hD0 ht)]
        _ ≤ (2 * sqrt t * log t) * K t :=
          mul_le_mul_of_nonneg_right (Chebyshev.psi_sub_theta_le (by linarith)) (hK ht)
        _ = (2 * sqrt t / t ^ 2) * (1 + 1 / log t) := by
          dsimp [K]
          field_simp [htPos.ne', hLogPos.ne']
        _ ≤ (2 * sqrt t / t ^ 2) * 2 := by gcongr; linarith
        _ = 4 * t ^ (-(3 / 2 : ℝ)) := by
          rw [show 2 * sqrt t / t ^ 2 = 2 * (sqrt t / t ^ 2) by ring, hPower]
          ring
  exact hD

noncomputable def compensatedPsi (x : ℝ) := compensatedTheta x + ∫ t in Ioi x, primePowerGap t

theorem compensatedPsi_tendsto : Tendsto compensatedPsi atTop (𝓝 0) := by
  unfold compensatedPsi
  simpa only [id_eq, zero_add] using compensatedTheta_tendsto.add
    (tendsto_integral_Ioi_zero (μ := volume) (f := primePowerGap) tendsto_id)

theorem compensatedTheta_le_psi {x : ℝ} (hx : 3 ≤ x) :
    compensatedTheta x ≤ compensatedPsi x := by
  apply le_add_of_nonneg_right
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  have hl : 0 ≤ log t := log_nonneg (by have := hx.trans ht.le; linarith)
  have hg := Chebyshev.theta_le_psi t
  unfold primePowerGap
  positivity

theorem compensatedPsi_sub {x y : ℝ} (hx : 3 ≤ x) (hy : x ≤ y) :
    compensatedPsi x - compensatedPsi y =
      ∫ t in x..y, (Chebyshev.psi t - t)*((1/log t+1/log t^2)/t^2) := by
  let A (t : ℝ) := (Chebyshev.theta t-t)*((1/log t+1/log t^2)/t^2)
  have hA : IntervalIntegrable A volume x y := by
    apply (Chebyshev.theta_mono.intervalIntegrable.sub (continuous_id.intervalIntegrable x y)).mul_continuousOn
    refine fun t ht => ContinuousAt.continuousWithinAt ?_
    rw [uIcc_of_le hy] at ht
    have hpos : 0 < t := by linarith [ht.1]
    have hlog : 0 < log t := log_pos (by linarith [ht.1])
    fun_prop (disch := positivity)
  have hD := primePowerGap_integrable hx
  have hDi : IntervalIntegrable primePowerGap volume x y :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).2 (hD.mono_set Ioc_subset_Ioi_self)
  unfold compensatedPsi
  rw [add_sub_add_comm, compensatedTheta_sub (by linarith) hy, intervalIntegral.integral_Ioi_sub_Ioi hD hy]
  change (∫ t in x..y, A t) + (∫ t in x..y, primePowerGap t) = _
  rw [← intervalIntegral.integral_add hA hDi]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [A,primePowerGap]
  ring

theorem conditional_psi_tail {x : ℝ} (hx : 3 ≤ x) :
    Tendsto (fun y : ℝ => ∫ t in x..y, (Chebyshev.psi t - t)*((1/log t+1/log t^2)/t^2))
      atTop (𝓝 (compensatedPsi x)) := by
  have h := (tendsto_const_nhds (x := compensatedPsi x)).sub compensatedPsi_tendsto
  rw [sub_zero] at h
  exact h.congr' ((eventually_ge_atTop x).mono (fun y hy => compensatedPsi_sub hx hy))

theorem finite_product_compensatedPsi {x : ℝ} (hx : 3 ≤ x) :
    log (exp eulerMascheroniConstant * log (Chebyshev.theta x) *
      ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1-1/(p:ℝ))) ≤ compensatedPsi x + 4/x :=
  (finite_product_compensated hx).trans (add_le_add_left (compensatedTheta_le_psi hx) _)

end RobinConverse
end

section
/- Singular-ray continuation from Jonas Whidden's Robin1984, Apache-2.0, e3697139babfe0f6cc7a76a08bf41a92aa7a2978. Extracted from the public Lagarias singular witness. -/
section

namespace ProbabilityTheory

open Filter MeasureTheory Set

open scoped ENNReal Topology

noncomputable section

theorem mem_interior_integrableExpSet_of_two_sided
    {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega -> Real} {mu : Measure Omega}
    {l a r : Real}
    (hl : Membership.mem (integrableExpSet X mu) l)
    (hr : Membership.mem (integrableExpSet X mu) r)
    (hla : l < a) (har : a < r) :
    Membership.mem (interior (integrableExpSet X mu)) a := by
  rw [mem_interior_iff_mem_nhds]
  let eps : Real := min (a - l) (r - a) / 2
  have hMinPos : 0 < min (a - l) (r - a) :=
    lt_min (sub_pos.mpr hla) (sub_pos.mpr har)
  have hEpsPos : 0 < eps := by
    dsimp [eps]
    positivity
  apply mem_of_superset (Metric.ball_mem_nhds a hEpsPos)
  intro y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have hEpsLeft : eps <= a - l := by
    dsimp [eps]
    have hMinLe := min_le_left (a - l) (r - a)
    linarith
  have hEpsRight : eps <= r - a := by
    dsimp [eps]
    have hMinLe := min_le_right (a - l) (r - a)
    linarith
  have hyLeft : l <= y := by
    have hyLower := (abs_lt.mp hy).1
    linarith
  have hyRight : y <= r := by
    have hyUpper := (abs_lt.mp hy).2
    linarith
  exact convex_integrableExpSet.ordConnected.out hl hr
    (And.intro hyLeft hyRight)

end

end ProbabilityTheory

end
section

namespace RiemannZeta

open Filter MeasureTheory ProbabilityTheory Set

noncomputable section

def regularPart (s : Complex) : Complex :=
  Function.update
    (fun w : Complex => riemannZeta w - 1 / (w - 1)) 1
    (limUnder (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (fun w : Complex => riemannZeta w - 1 / (w - 1))) s

theorem regularPart_eq_of_ne_one
    {s : Complex} (hs : Not (s = 1)) :
    regularPart s = riemannZeta s - 1 / (s - 1) := by
  simp [regularPart, hs]

theorem regularPart_differentiable :
    Differentiable Complex regularPart := by
  intro s
  let f : Complex -> Complex := fun w => riemannZeta w - 1 / (w - 1)
  by_cases hs : s = 1
  . subst s
    have hDiffAway : DifferentiableOn Complex f
        (Set.univ \ {1}) := by
      intro w hw
      have hwOne : Not (w = 1) := by
        exact Set.mem_compl_singleton_iff.mp hw.2
      have hNumerator : DifferentiableAt Complex
          (fun _ : Complex => (1 : Complex)) w := by fun_prop
      have hDenominator : DifferentiableAt Complex
          (fun z : Complex => z - 1) w := by fun_prop
      dsimp [f]
      exact ((differentiableAt_riemannZeta hwOne).sub
        (hNumerator.div hDenominator (sub_ne_zero.mpr hwOne))).differentiableWithinAt
    have hLittleO : (fun w : Complex => f w - f 1) =o[
        nhdsWithin 1 (Set.compl {(1 : Complex)})]
        (fun w : Complex => Inv.inv (w - 1)) := by
      refine Asymptotics.isLittleO_of_tendsto' ?_ ?_
      . filter_upwards [self_mem_nhdsWithin] with w hw hwInv
        rw [inv_eq_zero, sub_eq_zero] at hwInv
        tauto
      . simp_rw [div_eq_mul_inv, inv_inv, sub_mul,
          (by ring_nf : nhds (0 : Complex) =
            nhds ((1 - 1) - f 1 * (1 - 1)))]
        apply Tendsto.sub
        . simp_rw [mul_comm (f _), f, mul_sub]
          apply riemannZeta_residue_one.sub
          refine Tendsto.congr' ?_
            (tendsto_const_nhds.mono_left nhdsWithin_le_nhds)
          filter_upwards [self_mem_nhdsWithin] with w hw
          field_simp [sub_ne_zero.mpr
            (Set.mem_compl_singleton_iff.mp hw)]
        . exact ((tendsto_id.sub tendsto_const_nhds).mono_left
            nhdsWithin_le_nhds).const_mul _
    have hFilled := Complex.differentiableOn_update_limUnder_of_isLittleO
      (s := Set.univ) (c := (1 : Complex)) univ_mem hDiffAway hLittleO
    change DifferentiableAt Complex
      (Function.update f 1
        (limUnder (nhdsWithin 1 (Set.compl {(1 : Complex)})) f)) 1
    exact (hFilled 1 (Set.mem_univ 1)).differentiableAt Filter.univ_mem
  . have hBase : DifferentiableAt Complex f s := by
      have hNumerator : DifferentiableAt Complex
          (fun _ : Complex => (1 : Complex)) s := by fun_prop
      have hDenominator : DifferentiableAt Complex
          (fun z : Complex => z - 1) s := by fun_prop
      dsimp [f]
      exact (differentiableAt_riemannZeta hs).sub
        (hNumerator.div hDenominator (sub_ne_zero.mpr hs))
    change DifferentiableAt Complex
      (Function.update f 1
        (limUnder (nhdsWithin 1 (Set.compl {(1 : Complex)})) f)) s
    apply hBase.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with w hw
    simp [Function.update_of_ne
      (Set.mem_compl_singleton_iff.mp hw)]

def poleFactor (s : Complex) : Complex :=
  1 + (s - 1) * regularPart s

theorem poleFactor_differentiable :
    Differentiable Complex poleFactor := by
  intro s
  unfold poleFactor
  have hConst : DifferentiableAt Complex
      (fun _ : Complex => (1 : Complex)) s := by fun_prop
  have hDifference : DifferentiableAt Complex
      (fun w : Complex => w - 1) s := by fun_prop
  exact hConst.add
    (hDifference.mul (regularPart_differentiable s))

@[simp] theorem poleFactor_one :
    poleFactor 1 = 1 := by
  unfold poleFactor
  ring

theorem eq_poleFactor_div
    {s : Complex} (hs : Not (s = 1)) :
    riemannZeta s = poleFactor s / (s - 1) := by
  unfold poleFactor
  rw [regularPart_eq_of_ne_one hs]
  field_simp [sub_ne_zero.mpr hs]
  ring

theorem poleFactor_ne_zero_of_riemannZeta_ne_zero
    {s : Complex} (hsOne : Not (s = 1))
    (hZeta : Not (riemannZeta s = 0)) :
    Not (poleFactor s = 0) := by
  intro hFactor
  have hIdentity := eq_poleFactor_div hsOne
  rw [hFactor, zero_div] at hIdentity
  exact hZeta hIdentity

def eulerSaw (x : Real) : Real :=
  x + 1 - (Int.ceil x : Real)

theorem eulerSaw_pos (x : Real) :
    0 < eulerSaw x := by
  unfold eulerSaw
  have h := Int.ceil_lt_add_one x
  linarith

theorem eulerSaw_le_one (x : Real) :
    eulerSaw x <= 1 := by
  unfold eulerSaw
  have h := Int.le_ceil x
  linarith

theorem eulerSaw_eq_sub_nat_on_cell
    (n : Nat) {x : Real}
    (hx : Membership.mem (Ioc ((n : Real) + 1) ((n : Real) + 2)) x) :
    eulerSaw x = x - ((n : Real) + 1) := by
  have hCeil : Int.ceil x = (n : Int) + 2 := by
    apply Int.ceil_eq_iff.mpr
    constructor
    case left =>
      push_cast
      linarith [hx.1]
    case right =>
      push_cast
      linarith [hx.2]
  unfold eulerSaw
  rw [hCeil]
  push_cast
  ring

theorem iUnion_eulerCells :
    (iUnion fun n : Nat =>
      Ioc ((n : Real) + 1) ((n : Real) + 2)) = Ioi (1 : Real) := by
  apply Set.ext
  intro x
  constructor
  case mp =>
    intro hx
    rw [mem_iUnion] at hx
    choose n hn using hx
    have hnNonneg : (0 : Real) <= (n : Real) := Nat.cast_nonneg n
    have hOneLe : (1 : Real) <= (n : Real) + 1 := by linarith
    exact hOneLe.trans_lt hn.1
  case mpr =>
    intro hx
    change 1 < x at hx
    have hxNonneg : 0 <= x := le_trans (by norm_num) hx.le
    let m : Nat := Nat.ceil x
    have hUpper : x <= (m : Real) := by
      exact Nat.le_ceil x
    have hLower : (m : Real) - 1 < x := by
      have h := Nat.ceil_lt_add_one hxNonneg
      dsimp [m] at hUpper h
      linarith
    have hmTwo : 2 <= m := by
      by_contra hm
      have hmLe : m <= 1 := by omega
      have hmCast : (m : Real) <= 1 := by exact_mod_cast hmLe
      exact (not_lt_of_ge (hUpper.trans hmCast)) hx
    let n : Nat := m - 2
    rw [mem_iUnion]
    refine Exists.intro n ?_
    have hnOne : n + 1 = m - 1 := by
      dsimp [n]
      omega
    have hnTwo : n + 2 = m := by
      dsimp [n]
      omega
    have hmOne : 1 <= m := le_trans (by norm_num) hmTwo
    constructor
    case left =>
      calc
        (n : Real) + 1 = ((n + 1 : Nat) : Real) := by push_cast; rfl
        _ = ((m - 1 : Nat) : Real) := congrArg Nat.cast hnOne
        _ = (m : Real) - 1 := by rw [Nat.cast_sub hmOne]; norm_num
        _ < x := hLower
    case right =>
      calc
        x <= (m : Real) := hUpper
        _ = ((n + 2 : Nat) : Real) := congrArg Nat.cast hnTwo.symm
        _ = (n : Real) + 2 := by push_cast; rfl

theorem pairwise_disjoint_eulerCells :
    Pairwise (Function.onFun Disjoint fun n : Nat =>
      Ioc ((n : Real) + 1) ((n : Real) + 2)) := by
  intro i j hij
  obtain hijLt | hjiLt := lt_or_gt_of_ne hij
  case inl =>
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hCast : (i : Real) + 2 <= (j : Real) + 1 := by
      have hNat : i + 2 <= j + 1 := by omega
      exact_mod_cast hNat
    linarith [hxi.2, hxj.1]
  case inr =>
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hCast : (j : Real) + 2 <= (i : Real) + 1 := by
      have hNat : j + 2 <= i + 1 := by omega
      exact_mod_cast hNat
    linarith [hxj.2, hxi.1]

def eulerRemainderIntegrand (s x : Real) : Real :=
  eulerSaw x / x ^ (s + 1)

def eulerRemainder (s : Real) : Real :=
  integral (volume.restrict (Ioi 1))
    (fun x : Real => eulerRemainderIntegrand s x)

theorem eulerRemainderIntegrable
    {s : Real} (hs : 0 < s) :
    IntegrableOn (eulerRemainderIntegrand s) (Ioi 1) := by
  have hMajorant : IntegrableOn (fun x : Real => x ^ (-(s + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  apply hMajorant.mono'
  case hf =>
    apply Measurable.aestronglyMeasurable
    unfold eulerRemainderIntegrand eulerSaw
    measurability
  case h =>
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hxPos : 0 < x := lt_trans (by norm_num) hx
    have hDenomNonneg : 0 <= x ^ (s + 1) :=
      Real.rpow_nonneg hxPos.le _
    have hValueNonneg : 0 <= eulerRemainderIntegrand s x := by
      unfold eulerRemainderIntegrand
      exact div_nonneg (eulerSaw_pos x).le hDenomNonneg
    calc
      norm (eulerRemainderIntegrand s x) =
          eulerRemainderIntegrand s x := abs_of_nonneg hValueNonneg
      _ <= 1 / x ^ (s + 1) := by
        unfold eulerRemainderIntegrand
        exact div_le_div_of_nonneg_right (eulerSaw_le_one x) hDenomNonneg
      _ = x ^ (-(s + 1)) := by
        rw [Real.rpow_neg hxPos.le]
        simp only [one_div]

theorem integral_eulerCell_eq_term
    (n : Nat) (s : Real) :
    integral (volume.restrict (Ioc ((n : Real) + 1) ((n : Real) + 2)))
        (fun x : Real => eulerRemainderIntegrand s x) =
      ZetaAsymptotics.term (n + 1) s := by
  unfold ZetaAsymptotics.term
  rw [intervalIntegral.integral_of_le (by linarith :
    ((n + 1 : Nat) : Real) <= ((n + 1 : Nat) : Real) + 1)]
  push_cast
  ring_nf
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have hxCell : Membership.mem
      (Ioc ((n : Real) + 1) ((n : Real) + 2)) x := by
    simpa [add_comm] using hx
  unfold eulerRemainderIntegrand
  rw [eulerSaw_eq_sub_nat_on_cell n hxCell]
  push_cast
  ring

theorem eulerRemainder_eq_termTSum
    {s : Real} (hs : 0 < s) :
    eulerRemainder s = ZetaAsymptotics.termTSum s := by
  unfold eulerRemainder ZetaAsymptotics.termTSum
  rw [iUnion_eulerCells.symm]
  rw [MeasureTheory.integral_iUnion
    (fun _ => measurableSet_Ioc)
    pairwise_disjoint_eulerCells
    (by simpa [iUnion_eulerCells] using
      eulerRemainderIntegrable hs)]
  apply tsum_congr
  intro n
  exact integral_eulerCell_eq_term n s

def eulerDensity (x : Real) : NNReal :=
  Real.toNNReal (eulerSaw x / x)

theorem measurable_eulerDensity :
    Measurable eulerDensity := by
  unfold eulerDensity eulerSaw
  measurability

def eulerMeasure : Measure Real :=
  (volume.restrict (Ioi 1)).withDensity
    (fun x : Real => eulerDensity x)

theorem eulerDensity_coe
    {x : Real} (hx : 1 < x) :
    (eulerDensity x : Real) = eulerSaw x / x := by
  unfold eulerDensity
  rw [Real.coe_toNNReal]
  exact div_nonneg (eulerSaw_pos x).le (le_trans (by norm_num) hx.le)

theorem eulerDensity_mul_exp_eq_integrand
    {t x : Real} (hx : 1 < x) :
    (eulerDensity x : Real) * Real.exp (t * Real.log x) =
      eulerRemainderIntegrand (-t) x := by
  have hxPos : 0 < x := lt_trans (by norm_num) hx
  rw [eulerDensity_coe hx]
  unfold eulerRemainderIntegrand
  rw [Real.rpow_def_of_pos hxPos]
  have hExp : Real.exp (t * Real.log x) *
      Real.exp (Real.log x * (-t + 1)) = x := by
    calc
      Real.exp (t * Real.log x) * Real.exp (Real.log x * (-t + 1)) =
          Real.exp (t * Real.log x + Real.log x * (-t + 1)) :=
        (Real.exp_add _ _).symm
      _ = Real.exp (Real.log x) := by congr 1; ring
      _ = x := Real.exp_log hxPos
  field_simp [Real.exp_ne_zero, hxPos.ne']
  calc
    eulerSaw x * Real.exp (t * Real.log x) *
        Real.exp (Real.log x * (-t + 1)) =
      eulerSaw x *
        (Real.exp (t * Real.log x) *
          Real.exp (Real.log x * (-t + 1))) := by ring
    _ = eulerSaw x * x := by rw [hExp]

theorem mgf_eulerMeasure_neg_eq_remainder
    {s : Real} (_hs : 0 < s) :
    ProbabilityTheory.mgf Real.log eulerMeasure (-s) =
      eulerRemainder s := by
  unfold ProbabilityTheory.mgf eulerMeasure eulerRemainder
  rw [integral_withDensity_eq_integral_smul measurable_eulerDensity]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  change (eulerDensity x : Real) * Real.exp (-s * Real.log x) =
    eulerRemainderIntegrand s x
  simpa using eulerDensity_mul_exp_eq_integrand (t := -s) hx

theorem integrable_exp_log_eulerMeasure_of_neg
    {t : Real} (ht : t < 0) :
    Integrable (fun x : Real => Real.exp (t * Real.log x))
      eulerMeasure := by
  unfold eulerMeasure
  rw [integrable_withDensity_iff_integrable_smul measurable_eulerDensity]
  apply (eulerRemainderIntegrable (neg_pos.mpr ht)).congr_fun
  case hst =>
    intro x hx
    change eulerRemainderIntegrand (-t) x =
      (eulerDensity x : Real) * Real.exp (t * Real.log x)
    exact (eulerDensity_mul_exp_eq_integrand (t := t) hx).symm
  case hs =>
    exact measurableSet_Ioi

theorem neg_mem_eulerIntegrableExpSet
    {t : Real} (ht : t < 0) :
    Membership.mem
      (ProbabilityTheory.integrableExpSet Real.log eulerMeasure) t :=
  integrable_exp_log_eulerMeasure_of_neg ht

theorem termTSum_analyticAt_of_pos
    {s : Real} (hs : 0 < s) :
    AnalyticAt Real ZetaAsymptotics.termTSum s := by
  have hLeft := neg_mem_eulerIntegrableExpSet
    (t := -2 * s) (by linarith)
  have hRight := neg_mem_eulerIntegrableExpSet
    (t := -s / 2) (by linarith)
  have hInterior := mem_interior_integrableExpSet_of_two_sided
    hLeft hRight (by linarith : -2 * s < -s) (by linarith : -s < -s / 2)
  have hMgf : AnalyticAt Real
      (ProbabilityTheory.mgf Real.log eulerMeasure) (-s) :=
    ProbabilityTheory.analyticAt_mgf hInterior
  have hComp : AnalyticAt Real
      (fun u : Real =>
        ProbabilityTheory.mgf Real.log eulerMeasure (-u)) s := by
    simpa [Function.comp_def] using hMgf.comp (analyticAt_id.neg)
  have hEq : Filter.EventuallyEq (nhds s)
      (fun u : Real =>
        ProbabilityTheory.mgf Real.log eulerMeasure (-u))
      ZetaAsymptotics.termTSum := by
    filter_upwards [Ioi_mem_nhds hs] with u hu
    rw [mgf_eulerMeasure_neg_eq_remainder hu]
    exact eulerRemainder_eq_termTSum hu
  exact (analyticAt_congr hEq).mp hComp

theorem termTSum_nonneg
    {s : Real} (_hs : 0 < s) :
    0 <= ZetaAsymptotics.termTSum s := by
  unfold ZetaAsymptotics.termTSum
  exact tsum_nonneg (fun n => ZetaAsymptotics.term_nonneg (n + 1) s)

theorem poleFactor_eq_termTSum_of_one_lt
    {s : Real} (hs : 1 < s) :
    poleFactor (s : Complex) =
      (s * (1 - (s - 1) * ZetaAsymptotics.termTSum s) : Real) := by
  let Z : Real := tsum fun n : Nat =>
    1 / ((n : Real) + 1) ^ s
  let T : Real := ZetaAsymptotics.termTSum s
  change poleFactor (s : Complex) =
    ((s * (1 - (s - 1) * T) : Real) : Complex)
  have hRealSummable : Summable (fun n : Nat =>
      1 / ((n : Real) + 1) ^ s) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_rpow.mpr hs))
  have hCast : (Z : Complex) = tsum fun n : Nat =>
      1 / ((n : Complex) + 1) ^ (s : Complex) := by
    dsimp [Z]
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [Complex.ofReal_div, Complex.ofReal_one]
    rw [Complex.ofReal_cpow (by positivity : 0 <= (n : Real) + 1) s]
    push_cast
    rfl
  have hZeta : riemannZeta (s : Complex) = (Z : Complex) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)]
    exact hCast.symm
  have hLimit := ZetaAsymptotics.zeta_limit_aux1 hs
  change Z - 1 / (s - 1) =
    1 - s * T at hLimit
  have hsOne : Not ((s : Complex) = 1) := by
    exact Complex.ofReal_ne_one.mpr (ne_of_gt hs)
  have hPole := eq_poleFactor_div hsOne
  rw [hZeta] at hPole
  have hsSub : Not (s - 1 = 0) := sub_ne_zero.mpr (ne_of_gt hs)
  have hPoleMul : poleFactor (s : Complex) =
      (Z : Complex) * ((s : Complex) - 1) := by
    exact (div_eq_iff (sub_ne_zero.mpr hsOne)).mp hPole.symm
  have hReal : Z * (s - 1) =
      s * (1 - (s - 1) * T) := by
    have hZ : Z = 1 / (s - 1) +
        (1 - s * T) := by
      linarith [hLimit]
    calc
      Z * (s - 1) =
          (1 / (s - 1) +
            (1 - s * T)) * (s - 1) := by
        rw [hZ]
      _ = 1 + (1 - s * T) * (s - 1) := by
        rw [add_mul]
        simp [hsSub]
      _ = s * (1 - (s - 1) * T) := by
        ring
  calc
    poleFactor (s : Complex) =
        (Z : Complex) * ((s : Complex) - 1) := hPoleMul
    _ = ((Z * (s - 1) : Real) : Complex) := by push_cast; rfl
    _ = ((s * (1 - (s - 1) * T) : Real) : Complex) :=
      congrArg Complex.ofReal hReal

theorem poleFactor_re_eq_termTSum_of_pos
    {s : Real} (hs : 0 < s) :
    (poleFactor (s : Complex)).re =
      s * (1 - (s - 1) * ZetaAsymptotics.termTSum s) := by
  let F : Real -> Real := fun u => (poleFactor (u : Complex)).re
  let G : Real -> Real := fun u =>
    u * (1 - (u - 1) * ZetaAsymptotics.termTSum u)
  have hF : AnalyticOnNhd Real F (Ioi 0) := by
    intro u hu
    exact poleFactor_differentiable.analyticAt (u : Complex) |>.re_ofReal
  have hG : AnalyticOnNhd Real G (Ioi 0) := by
    intro u hu
    have hTerm := termTSum_analyticAt_of_pos hu
    have hSub : AnalyticAt Real (fun v : Real => v - 1) u :=
      analyticAt_id.sub analyticAt_const
    have hProduct : AnalyticAt Real
        (fun v : Real => (v - 1) * ZetaAsymptotics.termTSum v) u :=
      hSub.mul hTerm
    have hBracket : AnalyticAt Real
        (fun v : Real => 1 -
          (v - 1) * ZetaAsymptotics.termTSum v) u :=
      analyticAt_const.sub hProduct
    have hReal : AnalyticAt Real
        (fun v : Real => v *
          (1 - (v - 1) * ZetaAsymptotics.termTSum v)) u :=
      analyticAt_id.mul hBracket
    exact hReal
  have hEqNhd : Filter.EventuallyEq (nhds (2 : Real)) F G := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (1 : Real) < 2)] with u hu
    have hIdentity := poleFactor_eq_termTSum_of_one_lt hu
    simpa [F, G] using congrArg Complex.re hIdentity
  have hEqOn : EqOn F G (Ioi 0) :=
    hF.eqOn_of_preconnected_of_eventuallyEq
      hG (convex_Ioi (0 : Real)).isPreconnected (by norm_num) hEqNhd
  exact hEqOn hs

theorem poleFactor_ne_zero_of_mem_Ioo_zero_one
    {s : Real} (hs : Membership.mem (Ioo (0 : Real) 1) s) :
    Not (poleFactor (s : Complex) = 0) := by
  have hIdentity := poleFactor_re_eq_termTSum_of_pos hs.1
  have hTermNonneg := termTSum_nonneg hs.1
  have hCoefficientNonpos :
      (s - 1) * ZetaAsymptotics.termTSum s <= 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs.2.le) hTermNonneg
  have hRealPos :
      0 < s * (1 - (s - 1) * ZetaAsymptotics.termTSum s) := by
    apply mul_pos hs.1
    linarith
  intro hZero
  have hReZero : (poleFactor (s : Complex)).re = 0 := by
    rw [hZero]
    exact Complex.zero_re
  rw [hIdentity] at hReZero
  linarith

theorem real_ne_zero_of_mem_Ioo_zero_one
    {s : Real} (hs : Membership.mem (Ioo (0 : Real) 1) s) :
    Not (riemannZeta (s : Complex) = 0) := by
  have hsOne : Not ((s : Complex) = 1) := by
    exact Complex.ofReal_ne_one.mpr (ne_of_lt hs.2)
  rw [eq_poleFactor_div hsOne]
  exact div_ne_zero
    (poleFactor_ne_zero_of_mem_Ioo_zero_one hs)
    (sub_ne_zero.mpr hsOne)

theorem poleFactor_ne_zero_of_pos_real
    {s : Real} (hs : 0 < s) :
    Not (poleFactor (s : Complex) = 0) := by
  by_cases hsLt : s < 1
  case pos =>
    exact poleFactor_ne_zero_of_mem_Ioo_zero_one
      (And.intro hs hsLt)
  case neg =>
    by_cases hsEq : s = 1
    case pos =>
      subst s
      simp
    case neg =>
      have hsGt : 1 < s := lt_of_le_of_ne (not_lt.mp hsLt) (Ne.symm hsEq)
      have hsOne : Not ((s : Complex) = 1) :=
        Complex.ofReal_ne_one.mpr (ne_of_gt hsGt)
      have hZeta : Not (riemannZeta (s : Complex) = 0) :=
        riemannZeta_ne_zero_of_one_lt_re (by simpa using hsGt)
      exact poleFactor_ne_zero_of_riemannZeta_ne_zero hsOne hZeta

end

end RiemannZeta

end
section

namespace Robin1984

open Asymptotics Filter MeasureTheory Set

noncomputable section

def nicolasPsiError (x : Real) : Real :=
  Chebyshev.psi x - x

def nicolasTailKernel (t : Real) : Real :=
  (1 / Real.log t + 1 / (Real.log t) ^ 2) / t ^ 2

theorem nicolasTailKernel_nonneg {t : Real} (ht : 1 <= t) :
    0 <= nicolasTailKernel t := by
  unfold nicolasTailKernel
  have hLog : 0 <= Real.log t := Real.log_nonneg ht
  positivity

end

end Robin1984

end
section

namespace Robin1984

open Asymptotics Filter MeasureTheory Set

noncomputable section

theorem nicolasVonMangoldtPartialSums_isBigO :
    (fun n : Nat =>
      Finset.sum (Finset.Icc 1 n)
        (fun k => ArithmeticFunction.vonMangoldt k)) =O[atTop]
      (fun n : Nat => (n : Real) ^ (1 : Real)) := by
  apply (IsBigOWith.of_bound
    (c := Real.log 4 + 4) (Eventually.of_forall fun n => ?_)).isBigO
  have hSum :
      Finset.sum (Finset.Icc 1 n)
          (fun k => ArithmeticFunction.vonMangoldt k) =
        Chebyshev.psi (n : Real) := by
    rw [Chebyshev.psi_eq_sum_Icc]
    rw [Nat.floor_natCast]
    symm
    rw [<- Finset.insert_Icc_add_one_left_eq_Icc n.zero_le,
      Finset.sum_insert (by aesop)]
    simp
  rw [hSum, Real.norm_eq_abs,
    abs_of_nonneg (Chebyshev.psi_nonneg (n : Real)), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) 1), Real.rpow_one]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)

theorem nicolasLogDeriv_eq_psiMellin
    {s : Complex} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      s * integral (volume.restrict (Ioi (1 : Real)))
        (fun t => (Chebyshev.psi t : Complex) *
          (t : Complex) ^ (-(s + 1))) := by
  have hAbel := LSeries_eq_mul_integral_of_nonneg
    (fun n : Nat => ArithmeticFunction.vonMangoldt n)
    (r := (1 : Real)) (by norm_num) hs
    nicolasVonMangoldtPartialSums_isBigO
    (fun n => ArithmeticFunction.vonMangoldt_nonneg)
  calc
    -deriv riemannZeta s / riemannZeta s =
        LSeries (fun n : Nat =>
          (ArithmeticFunction.vonMangoldt n : Complex)) s := by
      symm
      exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
    _ = s * integral (volume.restrict (Ioi (1 : Real)))
        (fun t => (Finset.sum (Finset.Icc 1 (Nat.floor t))
          (fun k => (ArithmeticFunction.vonMangoldt k : Complex))) *
          (t : Complex) ^ (-(s + 1))) := hAbel
    _ = s * integral (volume.restrict (Ioi (1 : Real)))
        (fun t => (Chebyshev.psi t : Complex) *
          (t : Complex) ^ (-(s + 1))) := by
      have hIntegral :
          integral (volume.restrict (Ioi (1 : Real)))
              (fun t => (Finset.sum (Finset.Icc 1 (Nat.floor t))
                (fun k => (ArithmeticFunction.vonMangoldt k : Complex))) *
                (t : Complex) ^ (-(s + 1))) =
            integral (volume.restrict (Ioi (1 : Real)))
              (fun t => (Chebyshev.psi t : Complex) *
                (t : Complex) ^ (-(s + 1))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change
          (Finset.sum (Finset.Icc 1 (Nat.floor t))
              (fun k => (ArithmeticFunction.vonMangoldt k : Complex))) *
              (t : Complex) ^ (-(s + 1)) =
            (Chebyshev.psi t : Complex) *
              (t : Complex) ^ (-(s + 1))
        congr 1
        rw [Chebyshev.psi_eq_sum_Icc]
        push_cast
        symm
        rw [<- Finset.insert_Icc_add_one_left_eq_Icc
            (Nat.zero_le (Nat.floor t)),
          Finset.sum_insert (by aesop)]
        simp
      rw [hIntegral]

theorem nicolasPsiMellin_integrable
    {s : Complex} (hs : 1 < s.re) :
    IntegrableOn
      (fun t : Real => (Chebyshev.psi t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioi 1) := by
  let c : Real := Real.log 4 + 4
  have hcPos : 0 < c := by
    dsimp [c]
    positivity
  have hPower : IntegrableOn
      (fun t : Real => (c : Complex) * (t : Complex) ^ (-s)) (Ioi 1) := by
    exact (integrableOn_Ioi_cpow_of_lt
      (by simp only [Complex.neg_re]; linarith) (by norm_num)).const_mul (c : Complex)
  apply Integrable.mono
    (g := fun t : Real => (c : Complex) * (t : Complex) ^ (-s)) hPower
  . have hCpow : ContinuousOn
        (fun t : Real => (t : Complex) ^ (-(s + 1))) (Ioi 1) :=
      continuousOn_of_forall_continuousAt fun t ht =>
        Complex.continuousAt_ofReal_cpow_const t (-(s + 1))
          (Or.inr (ne_of_gt (lt_trans (by norm_num) ht)))
    exact ((Complex.measurable_ofReal.comp
      Chebyshev.psi_mono.measurable).aestronglyMeasurable.mul
        (hCpow.aestronglyMeasurable measurableSet_Ioi))
  . filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htPos : 0 < t := lt_trans (by norm_num) ht
    have hPsi := Chebyshev.psi_le_const_mul_self htPos.le
    have hPowNonneg : 0 <= t ^ (-(s + 1)).re :=
      Real.rpow_nonneg htPos.le _
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Chebyshev.psi_nonneg t), abs_of_pos hcPos,
      Complex.norm_cpow_eq_rpow_re_of_pos htPos]
    calc
      Chebyshev.psi t * t ^ (-(s + 1)).re <=
          (c * t) * t ^ (-(s + 1)).re :=
        mul_le_mul_of_nonneg_right hPsi hPowNonneg
      _ = c * t ^ (-s).re := by
        calc
          (c * t) * t ^ (-(s + 1)).re =
              c * (t ^ (1 : Real) * t ^ (-(s + 1)).re) := by
            rw [Real.rpow_one]
            ring
          _ = c * t ^ ((1 : Real) + (-(s + 1)).re) := by
            rw [Real.rpow_add htPos]
          _ = c * t ^ (-s).re := by
            congr 2
            simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
            ring

theorem nicolasLinearMellin_integrable
    {s : Complex} (hs : 1 < s.re) :
    IntegrableOn
      (fun t : Real => (t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioi 1) := by
  have hPower : IntegrableOn
      (fun t : Real => (t : Complex) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt
      (by simp only [Complex.neg_re]; linarith) (by norm_num)
  apply hPower.congr_fun
  . intro t ht
    have htZero : Not ((t : Complex) = 0) := by
      exact Complex.ofReal_ne_zero.mpr
        (ne_of_gt (lt_trans (by norm_num) ht))
    change (t : Complex) ^ (-s) =
      (t : Complex) * (t : Complex) ^ (-(s + 1))
    symm
    calc
      (t : Complex) * (t : Complex) ^ (-(s + 1)) =
          (t : Complex) ^ (1 : Complex) *
            (t : Complex) ^ (-(s + 1)) := by
        rw [Complex.cpow_one]
      _ = (t : Complex) ^ ((1 : Complex) + -(s + 1)) := by
        rw [Complex.cpow_add _ _ htZero]
      _ = (t : Complex) ^ (-s) := by
        congr 1
        ring
  . exact measurableSet_Ioi

theorem nicolasPsiErrorMellin_eq_logDeriv
    {s : Complex} (hs : 1 < s.re) :
    integral (volume.restrict (Ioi (1 : Real)))
        (fun t => (nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1))) =
      (-deriv riemannZeta s / riemannZeta s) / s -
        1 / (s - 1) := by
  have hsZero : Not (s = 0) := by
    intro hZero
    subst s
    norm_num at hs
  have hsOne : Not (s = 1) := by
    intro hOne
    subst s
    norm_num at hs
  have hLinear :
      integral (volume.restrict (Ioi (1 : Real)))
          (fun t => (t : Complex) * (t : Complex) ^ (-(s + 1))) =
        1 / (s - 1) := by
    calc
      integral (volume.restrict (Ioi (1 : Real)))
          (fun t => (t : Complex) * (t : Complex) ^ (-(s + 1))) =
          integral (volume.restrict (Ioi (1 : Real)))
            (fun t => (t : Complex) ^ (-s)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have htZero : Not ((t : Complex) = 0) := by
          exact Complex.ofReal_ne_zero.mpr
            (ne_of_gt (lt_trans (by norm_num) ht))
        change (t : Complex) * (t : Complex) ^ (-(s + 1)) =
          (t : Complex) ^ (-s)
        calc
          (t : Complex) * (t : Complex) ^ (-(s + 1)) =
              (t : Complex) ^ (1 : Complex) *
                (t : Complex) ^ (-(s + 1)) := by
            rw [Complex.cpow_one]
          _ = (t : Complex) ^ ((1 : Complex) + -(s + 1)) := by
            rw [Complex.cpow_add _ _ htZero]
          _ = (t : Complex) ^ (-s) := by
            congr 1
            ring
      _ = 1 / (s - 1) := by
        rw [integral_Ioi_cpow_of_lt
          (by simp only [Complex.neg_re]; linarith) (by norm_num)]
        rw [Complex.ofReal_one, Complex.one_cpow]
        rw [show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]
  rw [show (fun t : Real => (nicolasPsiError t : Complex) *
      (t : Complex) ^ (-(s + 1))) =
      (fun t : Real =>
        (Chebyshev.psi t : Complex) * (t : Complex) ^ (-(s + 1)) -
        (t : Complex) * (t : Complex) ^ (-(s + 1))) by
      funext t
      unfold nicolasPsiError
      push_cast
      ring]
  rw [integral_sub (nicolasPsiMellin_integrable hs)
    (nicolasLinearMellin_integrable hs), hLinear]
  have hLog := nicolasLogDeriv_eq_psiMellin hs
  congr 1
  symm
  apply (div_eq_iff hsZero).2
  rw [hLog]
  ring

theorem nicolasPsiErrorMellin_integrable
    {s : Complex} (hs : 1 < s.re) :
    IntegrableOn
      (fun t : Real => (nicolasPsiError t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioi 1) := by
  have hSub := (nicolasPsiMellin_integrable hs).sub
    (nicolasLinearMellin_integrable hs)
  apply hSub.congr_fun
  . intro t ht
    change
      (Chebyshev.psi t : Complex) * (t : Complex) ^ (-(s + 1)) -
          (t : Complex) * (t : Complex) ^ (-(s + 1)) =
        (nicolasPsiError t : Complex) * (t : Complex) ^ (-(s + 1))
    unfold nicolasPsiError
    push_cast
    ring
  . exact measurableSet_Ioi

def nicolasPsiMellinContinuation (s : Complex) : Complex :=
  (-deriv riemannZeta s / riemannZeta s) / s - 1 / (s - 1)

def nicolasPsiMellinStartup (x : Real) (s : Complex) : Complex :=
  integral (volume.restrict (Ioc (1 : Real) x))
    (fun t : Real => (nicolasPsiError t : Complex) *
      (t : Complex) ^ (-(s + 1)))

def nicolasPsiMellinTailContinuation (x : Real) (s : Complex) : Complex :=
  nicolasPsiMellinContinuation s - nicolasPsiMellinStartup x s

theorem nicolasPsiErrorTailMellin_eq_continuation
    {x : Real} (hx : 1 <= x) {s : Complex} (hs : 1 < s.re) :
    integral (volume.restrict (Ioi x))
        (fun t : Real => (nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1))) =
      nicolasPsiMellinTailContinuation x s := by
  have hFull := nicolasPsiErrorMellin_integrable hs
  have hStartup : IntegrableOn
      (fun t : Real => (nicolasPsiError t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioc 1 x) :=
    hFull.mono_set Ioc_subset_Ioi_self
  have hTail : IntegrableOn
      (fun t : Real => (nicolasPsiError t : Complex) *
        (t : Complex) ^ (-(s + 1))) (Ioi x) :=
    hFull.mono_set (Ioi_subset_Ioi hx)
  have hSplit :
      integral (volume.restrict (Ioi (1 : Real)))
          (fun t : Real => (nicolasPsiError t : Complex) *
            (t : Complex) ^ (-(s + 1))) =
        integral (volume.restrict (Ioc (1 : Real) x))
            (fun t : Real => (nicolasPsiError t : Complex) *
              (t : Complex) ^ (-(s + 1))) +
          integral (volume.restrict (Ioi x))
            (fun t : Real => (nicolasPsiError t : Complex) *
              (t : Complex) ^ (-(s + 1))) := by
    rw [<- Ioc_union_Ioi_eq_Ioi hx,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
    . exact hStartup
    . exact hTail
  unfold nicolasPsiMellinTailContinuation nicolasPsiMellinContinuation
    nicolasPsiMellinStartup
  rw [<- nicolasPsiErrorMellin_eq_logDeriv hs]
  rw [hSplit]
  ring

theorem integrableOn_mul_exp_neg_mul_Ioi_zero
    {r : Real} (hr : 0 < r) :
    IntegrableOn (fun u : Real => u * Real.exp (-(r * u))) (Ioi 0) := by
  have hGamma : IntegrableOn
      (fun u : Real => Real.exp (-u) * u ^ ((2 : Real) - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by norm_num)
  have hScaled : IntegrableOn
      (fun u : Real =>
        Real.exp (-(r * u)) * (r * u) ^ ((2 : Real) - 1)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun u : Real => Real.exp (-u) * u ^ ((2 : Real) - 1)) 0 hr).2
    simpa using hGamma
  have hDiv := hScaled.const_mul (1 / r)
  change Integrable (fun u : Real => u * Real.exp (-(r * u)))
    (volume.restrict (Ioi 0))
  apply hDiv.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  calc
    (1 / r) *
        (Real.exp (-(r * u)) * (r * u) ^ ((2 : Real) - 1)) =
        (1 / r) * (Real.exp (-(r * u)) * (r * u)) := by
      rw [show (2 : Real) - 1 = 1 by norm_num, Real.rpow_one]
    _ = u * Real.exp (-(r * u)) := by
      field_simp [hr.ne']

theorem integral_exp_neg_mul_Ioi_zero
    {r : Real} (hr : 0 < r) :
    integral (volume.restrict (Ioi (0 : Real)))
        (fun u : Real => Real.exp (-(r * u))) =
      1 / r := by
  have hValue := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (1 : Real)) (r := r) (by norm_num) hr
  simpa using hValue

theorem integral_mul_exp_neg_mul_Ioi_zero
    {r : Real} (hr : 0 < r) :
    integral (volume.restrict (Ioi (0 : Real)))
        (fun u : Real => u * Real.exp (-(r * u))) =
      1 / r ^ 2 := by
  have hValue := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : Real)) (r := r) (by norm_num) hr
  convert hValue using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  change u * Real.exp (-(r * u)) =
    u ^ ((2 : Real) - 1) * Real.exp (-(r * u))
  rw [show (2 : Real) - 1 = 1 by norm_num, Real.rpow_one]
  norm_num [Real.Gamma_ofNat_eq_factorial, div_pow]

theorem nicolasTailKernel_eq_frullani
    {t : Real} (ht : 1 < t) :
    nicolasTailKernel t =
      integral (volume.restrict (Ioi (0 : Real)))
        (fun u : Real => (u + 1) * t ^ (-(u + 2))) := by
  have htPos : 0 < t := lt_trans (by norm_num) ht
  have hLog : 0 < Real.log t := Real.log_pos ht
  have hPoint : forall u : Real,
      (u + 1) * t ^ (-(u + 2)) =
        t ^ (-(2 : Real)) *
          (u * Real.exp (-(Real.log t * u)) +
            Real.exp (-(Real.log t * u))) := by
    intro u
    have hPower : t ^ (-(u + 2)) =
        t ^ (-(2 : Real)) * Real.exp (-(Real.log t * u)) := by
      rw [Real.rpow_def_of_pos htPos, Real.rpow_def_of_pos htPos]
      rw [<- Real.exp_add]
      congr 1
      ring
    rw [hPower]
    ring
  have hExpInt : IntegrableOn
      (fun u : Real => Real.exp (-(Real.log t * u))) (Ioi 0) := by
    have hBase := integrableOn_exp_mul_Ioi
      (a := -Real.log t) (by linarith) 0
    apply hBase.congr_fun
    . intro u hu
      simp [neg_mul]
    . exact measurableSet_Ioi
  have hMulInt := integrableOn_mul_exp_neg_mul_Ioi_zero hLog
  calc
    nicolasTailKernel t =
        t ^ (-(2 : Real)) *
          (1 / (Real.log t) ^ 2 + 1 / Real.log t) := by
      unfold nicolasTailKernel
      rw [Real.rpow_neg htPos.le, Real.rpow_two]
      field_simp [htPos.ne', hLog.ne']
      ring
    _ = t ^ (-(2 : Real)) *
        (integral (volume.restrict (Ioi (0 : Real)))
            (fun u : Real => u * Real.exp (-(Real.log t * u))) +
          integral (volume.restrict (Ioi (0 : Real)))
            (fun u : Real => Real.exp (-(Real.log t * u)))) := by
      rw [integral_mul_exp_neg_mul_Ioi_zero hLog,
        integral_exp_neg_mul_Ioi_zero hLog]
    _ = integral (volume.restrict (Ioi (0 : Real)))
        (fun u : Real => (u + 1) * t ^ (-(u + 2))) := by
      rw [<- integral_add hMulInt hExpInt, <- integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      symm
      exact hPoint u

theorem nicolasFrullaniKernel_integrable
    {t : Real} (ht : 1 < t) :
    IntegrableOn (fun u : Real => (u + 1) * t ^ (-(u + 2))) (Ioi 0) := by
  have htPos : 0 < t := lt_trans (by norm_num) ht
  have hLog : 0 < Real.log t := Real.log_pos ht
  have hExpInt : IntegrableOn
      (fun u : Real => Real.exp (-(Real.log t * u))) (Ioi 0) := by
    have hBase := integrableOn_exp_mul_Ioi
      (a := -Real.log t) (by linarith) 0
    apply hBase.congr_fun
    . intro u hu
      simp [neg_mul]
    . exact measurableSet_Ioi
  have hMulInt := integrableOn_mul_exp_neg_mul_Ioi_zero hLog
  have hSumInt := hMulInt.add hExpInt
  have hScaled := hSumInt.const_mul (t ^ (-(2 : Real)))
  change Integrable (fun u : Real => (u + 1) * t ^ (-(u + 2)))
    (volume.restrict (Ioi 0))
  apply hScaled.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hPower : t ^ (-(u + 2)) =
      t ^ (-(2 : Real)) * Real.exp (-(Real.log t * u)) := by
    rw [Real.rpow_def_of_pos htPos, Real.rpow_def_of_pos htPos]
    rw [<- Real.exp_add]
    congr 1
    ring
  calc
    t ^ (-(2 : Real)) *
        (u * Real.exp (-(Real.log t * u)) +
          Real.exp (-(Real.log t * u))) =
        (u + 1) * t ^ (-(u + 2)) := by
      rw [hPower]
      ring

theorem nicolasRiemannZetaLogDeriv_order_eq_neg_one
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hOne : Not (rho = 1)) :
    meromorphicOrderAt (logDeriv riemannZeta) rho = -1 := by
  have hAnalyticRho : AnalyticAt Complex riemannZeta rho :=
    analyticOn_riemannZeta rho (by simpa using hOne)
  have hMeromorphicRho : MeromorphicAt riemannZeta rho :=
    hAnalyticRho.meromorphicAt
  have hTendstoZero : Tendsto riemannZeta
      (nhdsWithin rho (Set.compl {rho})) (nhds 0) := by
    have hCont : Tendsto riemannZeta
        (nhdsWithin rho (Set.compl {rho})) (nhds (riemannZeta rho)) :=
      hAnalyticRho.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa [hZero] using hCont
  have hOrderPos : 0 < meromorphicOrderAt riemannZeta rho :=
    (tendsto_zero_iff_meromorphicOrderAt_pos hMeromorphicRho).1 hTendstoZero
  have hAnalyticTwo : AnalyticAt Complex riemannZeta 2 :=
    analyticOn_riemannZeta 2 (by norm_num)
  have hMeromorphicTwo : MeromorphicAt riemannZeta 2 :=
    hAnalyticTwo.meromorphicAt
  have hZetaTwo : Not (riemannZeta 2 = 0) :=
    riemannZeta_ne_zero_of_one_le_re (by norm_num)
  have hTendstoTwo : Tendsto riemannZeta
      (nhdsWithin (2 : Complex) (Set.compl {(2 : Complex)}))
      (nhds (riemannZeta 2)) :=
    hAnalyticTwo.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hOrderTwo : meromorphicOrderAt riemannZeta 2 = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hMeromorphicTwo).1
      (Exists.intro (riemannZeta 2)
        (And.intro hZetaTwo hTendstoTwo))
  have hMeromorphicOn : MeromorphicOn riemannZeta (Set.compl {1}) :=
    analyticOn_riemannZeta.meromorphicOn
  apply meromorphicOrderAt_logDeriv_eq_neg_one hMeromorphicRho
    (ne_of_gt hOrderPos)
  apply hMeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    (x := (2 : Complex))
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  . exact Set.mem_compl_singleton_iff.mpr (by norm_num)
  . exact Set.mem_compl_singleton_iff.mpr hOne
  . rw [hOrderTwo]
    simp

theorem nicolasPsiMellinContinuation_order_eq_neg_one
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hRhoZero : Not (rho = 0)) (hOne : Not (rho = 1)) :
    meromorphicOrderAt nicolasPsiMellinContinuation rho = -1 := by
  let logF : Complex -> Complex := fun w => logDeriv riemannZeta w
  let negLogF : Complex -> Complex := fun w => -logF w
  let idF : Complex -> Complex := fun w => w
  let first : Complex -> Complex := fun w => negLogF w / idF w
  let regular : Complex -> Complex := fun w => -(Inv.inv (w - 1))
  have hZetaMeromorphic : MeromorphicAt riemannZeta rho :=
    (analyticOn_riemannZeta rho
      (Set.mem_compl_singleton_iff.mpr hOne)).meromorphicAt
  have hLogMeromorphic : MeromorphicAt logF rho := by
    dsimp [logF]
    exact hZetaMeromorphic.logDeriv
  have hNegLogMeromorphic : MeromorphicAt negLogF rho := by
    dsimp [negLogF]
    exact hLogMeromorphic.neg
  have hIdMeromorphic : MeromorphicAt idF rho := by
    dsimp [idF]
    fun_prop
  have hFirstMeromorphic : MeromorphicAt first rho := by
    dsimp [first]
    exact hNegLogMeromorphic.div hIdMeromorphic
  have hDen : Not (rho - 1 = 0) := sub_ne_zero.mpr hOne
  have hRegularAnalytic : AnalyticAt Complex regular rho := by
    dsimp [regular]
    have hOneAnalytic : AnalyticAt Complex
        (fun _ : Complex => (1 : Complex)) rho := analyticAt_const
    exact ((analyticAt_id.sub hOneAnalytic).inv hDen).neg
  have hRegularMeromorphic : MeromorphicAt regular rho :=
    hRegularAnalytic.meromorphicAt
  have hLogOrder : meromorphicOrderAt logF rho = -1 := by
    dsimp [logF]
    exact nicolasRiemannZetaLogDeriv_order_eq_neg_one hZero hOne
  have hNegLogOrder : meromorphicOrderAt negLogF rho = -1 := by
    dsimp [negLogF]
    rw [<- meromorphicOrderAt_fun_neg]
    exact hLogOrder
  have hIdTendsto : Tendsto idF
      (nhdsWithin rho (Set.compl {rho})) (nhds rho) := by
    dsimp [idF]
    exact tendsto_id.mono_left nhdsWithin_le_nhds
  have hIdOrder : meromorphicOrderAt idF rho = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hIdMeromorphic).1
      (Exists.intro rho (And.intro hRhoZero hIdTendsto))
  have hFirstOrder : meromorphicOrderAt first rho = -1 := by
    change meromorphicOrderAt (negLogF / idF) rho = -1
    rw [meromorphicOrderAt_div hNegLogMeromorphic hIdMeromorphic,
      hNegLogOrder, hIdOrder]
    norm_num
  have hRegularNonneg : 0 <= meromorphicOrderAt regular rho :=
    hRegularAnalytic.meromorphicOrderAt_nonneg
  have hOrdersNe : Not (meromorphicOrderAt first rho =
      meromorphicOrderAt regular rho) := by
    intro hEq
    rw [hFirstOrder] at hEq
    rw [<- hEq] at hRegularNonneg
    have hNegOne : ((-1 : Int) : WithTop Int) <
        ((0 : Int) : WithTop Int) := WithTop.coe_lt_coe.mpr (by norm_num)
    exact (not_lt_of_ge hRegularNonneg) hNegOne
  have hSumOrder : meromorphicOrderAt (first + regular) rho = -1 := by
    rw [meromorphicOrderAt_add_of_ne hFirstMeromorphic
      hRegularMeromorphic hOrdersNe, hFirstOrder]
    rw [min_eq_left]
    have hNegOne : ((-1 : Int) : WithTop Int) <
        ((0 : Int) : WithTop Int) := WithTop.coe_lt_coe.mpr (by norm_num)
    exact le_of_lt (lt_of_lt_of_le hNegOne hRegularNonneg)
  have hOrderCongr :
      meromorphicOrderAt nicolasPsiMellinContinuation rho =
        meromorphicOrderAt (first + regular) rho := by
    apply meromorphicOrderAt_congr
    exact Filter.Eventually.of_forall fun w => by
      unfold nicolasPsiMellinContinuation
      dsimp [first, regular, negLogF, logF, idF]
      rw [logDeriv_apply]
      ring
  exact hOrderCongr.trans hSumOrder

theorem nicolasPsiMellinStartup_three_continuousAt (s0 : Complex) :
    ContinuousAt (nicolasPsiMellinStartup 3) s0 := by
  let base : Real -> Complex := fun t =>
    (nicolasPsiError t : Complex) * (t : Complex) ^ (-3 : Complex)
  let ratio : Complex -> Real -> Complex := fun s t =>
    (t : Complex) ^ ((2 : Complex) - s)
  let majorant : Real -> Real := fun t =>
    norm (base t) * (3 : Real) ^ (abs s0.re + 4)
  have hBaseIntegrable : Integrable base
      (volume.restrict (Ioc (1 : Real) 3)) := by
    dsimp [base]
    change IntegrableOn
      (fun t : Real => (nicolasPsiError t : Complex) *
        (t : Complex) ^ (-3 : Complex)) (Ioc (1 : Real) 3)
    have h :=
      (nicolasPsiErrorMellin_integrable (s := (2 : Complex)) (by norm_num)).mono_set
        (show Ioc (1 : Real) 3 <= Ioi 1 from Ioc_subset_Ioi_self)
    apply h.congr_fun
    . intro t ht
      norm_num
    . exact measurableSet_Ioc
  have hMajorantIntegrable : Integrable majorant
      (volume.restrict (Ioc (1 : Real) 3)) := by
    have h := hBaseIntegrable.norm.const_mul
      ((3 : Real) ^ (abs s0.re + 4))
    simpa [majorant, mul_comm] using h
  have hMeasurable : forall s : Complex, AEStronglyMeasurable
      (fun t : Real => (nicolasPsiError t : Complex) *
        (t : Complex) ^ (-(s + 1)))
      (volume.restrict (Ioc (1 : Real) 3)) := by
    intro s
    have hRatioContinuous : ContinuousOn (ratio s) (Ioc (1 : Real) 3) := by
      apply continuousOn_of_forall_continuousAt
      intro t ht
      dsimp [ratio]
      have htPos : 0 < t := lt_trans zero_lt_one ht.1
      exact (continuousAt_cpow_const
        (Complex.ofReal_mem_slitPlane.2 htPos)).comp
          Complex.continuous_ofReal.continuousAt
    have hProduct := hBaseIntegrable.aestronglyMeasurable.mul
      (hRatioContinuous.aestronglyMeasurable measurableSet_Ioc)
    apply hProduct.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one ht.1))
    dsimp [base, ratio]
    rw [mul_assoc, <- Complex.cpow_add _ _ htZero]
    congr 2
    ring
  have hBound : forall s : Complex, dist s s0 < 1 ->
      forall t : Real, 1 < t -> t <= 3 ->
        norm ((nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1))) <= majorant t := by
    intro s hs t htOneStrict htThree
    have hDist : norm (s - s0) < 1 := by
      simpa [dist_eq_norm] using hs
    have hReAbs : abs (s.re - s0.re) <= norm (s - s0) := by
      simpa using Complex.abs_re_le_norm (s - s0)
    have hReLower : s0.re - 1 < s.re := by
      have hAbsLt : abs (s.re - s0.re) < 1 := lt_of_le_of_lt hReAbs hDist
      linarith [(abs_lt.mp hAbsLt).1]
    have htPos : 0 < t := lt_trans zero_lt_one htOneStrict
    have htOne : 1 <= t := le_of_lt htOneStrict
    have hExponent : 2 - s.re <= abs s0.re + 4 := by
      have hNeg : -s0.re <= abs s0.re := neg_le_abs s0.re
      linarith
    have hExponentNonneg : 0 <= abs s0.re + 4 := by positivity
    have hRatioBound : norm (ratio s t) <=
        (3 : Real) ^ (abs s0.re + 4) := by
      dsimp [ratio]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos htPos]
      calc
        t ^ (2 - s.re) <= t ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow_of_exponent_le htOne hExponent
        _ <= (3 : Real) ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow (le_of_lt htPos) htThree hExponentNonneg
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt htPos)
    rw [show -(s + 1) = (-3 : Complex) + ((2 : Complex) - s) by ring,
      Complex.cpow_add _ _ htZero, norm_mul]
    dsimp [majorant, base]
    simp only [norm_mul]
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hRatioBound
        (mul_nonneg (norm_nonneg
          ((nicolasPsiError t : Complex)))
          (norm_nonneg ((t : Complex) ^ (-3 : Complex)))))
  unfold nicolasPsiMellinStartup
  apply continuousAt_of_dominated
      (F := fun s : Complex => fun t : Real =>
        (nicolasPsiError t : Complex) * (t : Complex) ^ (-(s + 1)))
      (bound := majorant)
  . exact Eventually.of_forall hMeasurable
  . filter_upwards [Metric.ball_mem_nhds s0 zero_lt_one] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hBound s (by simpa [Metric.mem_ball] using hs) t ht.1 ht.2
  . exact hMajorantIntegrable
  . filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr
        (ne_of_gt (lt_trans zero_lt_one ht.1))
    have hExponent : ContinuousAt (fun s : Complex => -(s + 1)) s0 := by
      fun_prop
    exact continuousAt_const.mul
      ((continuousAt_const_cpow htZero).comp hExponent)

theorem nicolasPsiMellinTailContinuation_three_simplePoleLimit
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hRhoZero : Not (rho = 0)) (hOne : Not (rho = 1)) :
    Exists fun c : Complex => And (Not (c = 0))
      (Tendsto
        (fun s : Complex => (s - rho) *
          nicolasPsiMellinTailContinuation 3 s)
        (nhdsWithin rho (Set.compl {rho})) (nhds c)) := by
  have hOrder : meromorphicOrderAt nicolasPsiMellinContinuation rho = -1 :=
    nicolasPsiMellinContinuation_order_eq_neg_one hZero hRhoZero hOne
  have hOrderNeg : meromorphicOrderAt nicolasPsiMellinContinuation rho < 0 := by
    rw [hOrder]
    exact WithTop.coe_lt_coe.mpr (by norm_num)
  have hMeromorphic : MeromorphicAt nicolasPsiMellinContinuation rho :=
    meromorphicAt_of_meromorphicOrderAt_ne_zero hOrderNeg.ne
  choose g hgAnalytic hgZero hgFactor using
    (meromorphicOrderAt_eq_int_iff hMeromorphic).1 hOrder
  have hFullScaled : Tendsto
      (fun s : Complex => (s - rho) * nicolasPsiMellinContinuation s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (g rho)) := by
    apply hgAnalytic.continuousAt.continuousWithinAt.tendsto.congr'
    filter_upwards [hgFactor, self_mem_nhdsWithin] with s hs hsrho
    have hsNe : Not (s - rho = 0) := by
      exact sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hsrho)
    rw [hs]
    simp [hsNe]
  have hDifference : Tendsto (fun s : Complex => s - rho)
      (nhdsWithin rho (Set.compl {rho})) (nhds 0) := by
    have hContinuous : ContinuousAt (fun s : Complex => s - rho) rho := by
      fun_prop
    simpa using hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hStartup : Tendsto (nicolasPsiMellinStartup 3)
      (nhdsWithin rho (Set.compl {rho}))
      (nhds (nicolasPsiMellinStartup 3 rho)) :=
    (nicolasPsiMellinStartup_three_continuousAt rho).tendsto.mono_left
      nhdsWithin_le_nhds
  have hStartupScaled : Tendsto
      (fun s : Complex => (s - rho) * nicolasPsiMellinStartup 3 s)
      (nhdsWithin rho (Set.compl {rho})) (nhds 0) := by
    simpa using hDifference.mul hStartup
  refine Exists.intro (g rho) (And.intro hgZero ?_)
  have hTail := hFullScaled.sub hStartupScaled
  convert hTail using 1
  . funext s
    unfold nicolasPsiMellinTailContinuation
    ring
  . ring

theorem nicolasPsiMellinTailContinuation_three_simplePoleLimit_Ioi
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hRhoZero : Not (rho = 0)) (hOne : Not (rho = 1)) :
    Exists fun c : Complex => And (Not (c = 0))
      (Tendsto
        (fun u : Real => (u : Complex) *
          nicolasPsiMellinTailContinuation 3 (rho + (u : Complex)))
        (nhdsWithin 0 (Ioi 0)) (nhds c)) := by
  choose c hc hLimit using
    nicolasPsiMellinTailContinuation_three_simplePoleLimit
      hZero hRhoZero hOne
  have hRay : Tendsto (fun u : Real => rho + (u : Complex))
      (nhdsWithin 0 (Ioi 0))
      (nhdsWithin rho (Set.compl {rho})) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    . have hContinuous : ContinuousAt
          (fun u : Real => rho + (u : Complex)) 0 := by
        fun_prop
      simpa using hContinuous.tendsto.mono_left nhdsWithin_le_nhds
    . filter_upwards [self_mem_nhdsWithin] with u hu
      apply Set.mem_compl_singleton_iff.mpr
      intro hEq
      have huZero : ((u : Real) : Complex) = 0 := by
        apply add_left_cancel (a := rho)
        simpa using hEq
      exact (Complex.ofReal_ne_zero.mpr (ne_of_gt hu)) huZero
  refine Exists.intro c (And.intro hc ?_)
  simpa [Function.comp_def] using hLimit.comp hRay

noncomputable abbrev nicolasZetaPoleFactor : Complex -> Complex :=
  RiemannZeta.poleFactor

theorem nicolasZetaPoleFactor_differentiable :
    Differentiable Complex nicolasZetaPoleFactor :=
  RiemannZeta.poleFactor_differentiable

@[simp] theorem nicolasZetaPoleFactor_one :
    nicolasZetaPoleFactor 1 = 1 :=
  RiemannZeta.poleFactor_one

theorem riemannZeta_eq_nicolasZetaPoleFactor_div
    {s : Complex} (hs : Not (s = 1)) :
    riemannZeta s = nicolasZetaPoleFactor s / (s - 1) :=
  RiemannZeta.eq_poleFactor_div hs

theorem logDeriv_riemannZeta_eq_poleFactor_sub
    {s : Complex} (hs : Not (s = 1))
    (hZeta : Not (riemannZeta s = 0)) :
    logDeriv riemannZeta s =
      logDeriv nicolasZetaPoleFactor s - 1 / (s - 1) := by
  have hLocal : Filter.EventuallyEq (nhds s) riemannZeta
      (fun w : Complex => nicolasZetaPoleFactor w / (w - 1)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with w hw
    exact riemannZeta_eq_nicolasZetaPoleFactor_div
      (Set.mem_compl_singleton_iff.mp hw)
  have hLogCongr := logDeriv_congr_nhds hLocal
  have hLogAt : logDeriv riemannZeta s =
      logDeriv (fun w : Complex => nicolasZetaPoleFactor w / (w - 1)) s :=
    hLogCongr.self_of_nhds
  have hFactor : Not (nicolasZetaPoleFactor s = 0) := by
    intro hFactorZero
    have hIdentity := riemannZeta_eq_nicolasZetaPoleFactor_div hs
    rw [hFactorZero, zero_div] at hIdentity
    exact hZeta hIdentity
  calc
    logDeriv riemannZeta s =
        logDeriv (fun w : Complex =>
          nicolasZetaPoleFactor w / (w - 1)) s := hLogAt
    _ = logDeriv nicolasZetaPoleFactor s -
        logDeriv (fun w : Complex => w - 1) s :=
      logDeriv_div s hFactor (sub_ne_zero.mpr hs)
        (nicolasZetaPoleFactor_differentiable s) (by fun_prop)
    _ = logDeriv nicolasZetaPoleFactor s - 1 / (s - 1) := by
      congr 1
      simp [logDeriv_apply]

theorem nicolasPsiMellinContinuation_eq_poleFactor
    {s : Complex} (hsZero : Not (s = 0)) (hsOne : Not (s = 1))
    (hZeta : Not (riemannZeta s = 0)) :
    nicolasPsiMellinContinuation s =
      -(logDeriv nicolasZetaPoleFactor s + 1) / s := by
  unfold nicolasPsiMellinContinuation
  have hLog := logDeriv_riemannZeta_eq_poleFactor_sub hsOne hZeta
  rw [show -deriv riemannZeta s / riemannZeta s =
      -(logDeriv riemannZeta s) by
        rw [logDeriv_apply]
        ring,
    hLog]
  field_simp [hsZero, sub_ne_zero.mpr hsOne]
  ring

theorem logDeriv_nicolasZetaPoleFactor_continuousAt_one :
    ContinuousAt (logDeriv nicolasZetaPoleFactor) 1 := by
  rw [show logDeriv nicolasZetaPoleFactor =
      (fun s : Complex => deriv nicolasZetaPoleFactor s /
        nicolasZetaPoleFactor s) by rfl]
  exact (nicolasZetaPoleFactor_differentiable.deriv 1).continuousAt.div
    (nicolasZetaPoleFactor_differentiable 1).continuousAt (by simp)

theorem nicolasPsiMellinContinuation_tendsto_one :
    Tendsto nicolasPsiMellinContinuation
      (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (nhds (-(logDeriv nicolasZetaPoleFactor 1 + 1))) := by
  have hRegular : Tendsto
      (fun s : Complex => -(logDeriv nicolasZetaPoleFactor s + 1) / s)
      (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (nhds (-(logDeriv nicolasZetaPoleFactor 1 + 1))) := by
    have hContinuous : ContinuousAt
        (fun s : Complex => -(logDeriv nicolasZetaPoleFactor s + 1) / s) 1 :=
      (logDeriv_nicolasZetaPoleFactor_continuousAt_one.add
        continuousAt_const).neg.div continuousAt_id (by norm_num)
    simpa using hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hZeroNeighborhood :
      Membership.mem (nhds (1 : Complex)) (Set.compl {(0 : Complex)}) :=
    isOpen_compl_singleton.mem_nhds
      (Set.mem_compl_singleton_iff.mpr (by norm_num))
  have hZeroWithin : Membership.mem
      (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (Set.compl {(0 : Complex)}) :=
    nhdsWithin_le_nhds hZeroNeighborhood
  apply hRegular.congr'
  filter_upwards
      [riemannZeta_eventually_ne_zero_nhds_one.filter_mono
        nhdsWithin_le_nhds,
      hZeroWithin,
      self_mem_nhdsWithin] with s hZeta hsZeroMem hs
  have hsOne : Not (s = 1) := Set.mem_compl_singleton_iff.mp hs
  have hsZero : Not (s = 0) :=
    Set.mem_compl_singleton_iff.mp hsZeroMem
  exact (nicolasPsiMellinContinuation_eq_poleFactor
    hsZero hsOne hZeta).symm

theorem nicolasPsiMellinTailContinuation_three_tendsto_one :
    Tendsto (nicolasPsiMellinTailContinuation 3)
      (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (nhds (-(logDeriv nicolasZetaPoleFactor 1 + 1) -
        nicolasPsiMellinStartup 3 1)) := by
  have hStartup : Tendsto (nicolasPsiMellinStartup 3)
      (nhdsWithin 1 (Set.compl {(1 : Complex)}))
      (nhds (nicolasPsiMellinStartup 3 1)) :=
    (nicolasPsiMellinStartup_three_continuousAt 1).tendsto.mono_left
      nhdsWithin_le_nhds
  have hDifference := nicolasPsiMellinContinuation_tendsto_one.sub hStartup
  convert hDifference using 1
  . rfl

def nicolasJMellinShiftIntegrand (z : Complex) (u : Real) : Complex :=
  ((u + 1 : Real) : Complex) *
    ((nicolasPsiMellinTailContinuation 3
          (((u + 1 : Real) : Complex) - z) -
        (3 : Complex) ^ z * nicolasPsiMellinTailContinuation 3
          ((u + 1 : Real) : Complex)) / z)

end

end Robin1984

end
section

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal Topology

noncomputable section

def nicolasPsiMellinContinuationFilled (s : Complex) : Complex :=
  -(logDeriv nicolasZetaPoleFactor s + 1) / s

theorem nicolasPsiMellinContinuationFilled_analyticAt_one :
    AnalyticAt Complex nicolasPsiMellinContinuationFilled 1 := by
  have hFactor : AnalyticAt Complex nicolasZetaPoleFactor 1 :=
    nicolasZetaPoleFactor_differentiable.analyticAt 1
  have hFactorDeriv : AnalyticAt Complex
      (deriv nicolasZetaPoleFactor) 1 :=
    nicolasZetaPoleFactor_differentiable.deriv.analyticAt 1
  have hLogDeriv : AnalyticAt Complex
      (logDeriv nicolasZetaPoleFactor) 1 := by
    unfold logDeriv
    exact hFactorDeriv.div hFactor (by simp)
  unfold nicolasPsiMellinContinuationFilled
  have hOne : AnalyticAt Complex (fun _ : Complex => (1 : Complex)) 1 :=
    analyticAt_const
  have hNumerator : AnalyticAt Complex
      (fun s : Complex => -(logDeriv nicolasZetaPoleFactor s + 1)) 1 :=
    (hLogDeriv.add hOne).neg
  exact hNumerator.div analyticAt_id (by norm_num)

theorem nicolasPsiMellinContinuationFilled_eq_raw
    {s : Complex} (hsZero : Not (s = 0)) (hsOne : Not (s = 1))
    (hZeta : Not (riemannZeta s = 0)) :
    nicolasPsiMellinContinuationFilled s =
      nicolasPsiMellinContinuation s := by
  exact (nicolasPsiMellinContinuation_eq_poleFactor
    hsZero hsOne hZeta).symm

theorem nicolasPsiMellinStartup_three_differentiableAt (s0 : Complex) :
    DifferentiableAt Complex (nicolasPsiMellinStartup 3) s0 := by
  let _ : AddCommGroup Complex := Complex.addCommGroup
  let _ : Module Complex Complex := Semiring.toModule
  let F : Complex -> Real -> Complex := fun s t =>
    (nicolasPsiError t : Complex) * (t : Complex) ^ (-(s + 1))
  let F' : Complex -> Real -> Complex := fun s t =>
    -((Real.log t : Real) : Complex) * F s t
  let base : Real -> Complex := fun t =>
    (nicolasPsiError t : Complex) * (t : Complex) ^ (-3 : Complex)
  let ratio : Complex -> Real -> Complex := fun s t =>
    (t : Complex) ^ ((2 : Complex) - s)
  let majorant : Real -> Real := fun t =>
    norm (base t) * (3 : Real) ^ (abs s0.re + 4)
  have hBaseIntegrable : Integrable base
      (volume.restrict (Ioc (1 : Real) 3)) := by
    dsimp [base]
    change IntegrableOn
      (fun t : Real => (nicolasPsiError t : Complex) *
        (t : Complex) ^ (-3 : Complex)) (Ioc (1 : Real) 3)
    have h :=
      (nicolasPsiErrorMellin_integrable (s := (2 : Complex))
        (by norm_num)).mono_set
        (show Ioc (1 : Real) 3 <= Ioi 1 from Ioc_subset_Ioi_self)
    apply h.congr_fun
    . intro t ht
      norm_num
    . exact measurableSet_Ioc
  have hMajorantIntegrable : Integrable majorant
      (volume.restrict (Ioc (1 : Real) 3)) := by
    have h := hBaseIntegrable.norm.const_mul
      ((3 : Real) ^ (abs s0.re + 4))
    simpa [majorant, mul_comm] using h
  have hMeasurable : forall s : Complex, AEStronglyMeasurable (F s)
      (volume.restrict (Ioc (1 : Real) 3)) := by
    intro s
    have hRatioContinuous : ContinuousOn (ratio s) (Ioc (1 : Real) 3) := by
      apply continuousOn_of_forall_continuousAt
      intro t ht
      dsimp [ratio]
      have htPos : 0 < t := lt_trans zero_lt_one ht.1
      exact (continuousAt_cpow_const
        (Complex.ofReal_mem_slitPlane.2 htPos)).comp
          Complex.continuous_ofReal.continuousAt
    have hProduct := hBaseIntegrable.aestronglyMeasurable.mul
      (hRatioContinuous.aestronglyMeasurable measurableSet_Ioc)
    apply hProduct.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one ht.1))
    dsimp [F, base, ratio]
    rw [mul_assoc, <- Complex.cpow_add _ _ htZero]
    congr 2
    ring
  have hBound : forall s : Complex, dist s s0 < 1 ->
      forall t : Real, 1 < t -> t <= 3 ->
        norm (F s t) <= majorant t := by
    intro s hs t htOneStrict htThree
    have hDist : norm (s - s0) < 1 := by
      simpa [dist_eq_norm] using hs
    have hReAbs : abs (s.re - s0.re) <= norm (s - s0) := by
      simpa using Complex.abs_re_le_norm (s - s0)
    have hReLower : s0.re - 1 < s.re := by
      have hAbsLt : abs (s.re - s0.re) < 1 := lt_of_le_of_lt hReAbs hDist
      linarith [(abs_lt.mp hAbsLt).1]
    have htPos : 0 < t := lt_trans zero_lt_one htOneStrict
    have htOne : 1 <= t := le_of_lt htOneStrict
    have hExponent : 2 - s.re <= abs s0.re + 4 := by
      have hNeg : -s0.re <= abs s0.re := neg_le_abs s0.re
      linarith
    have hExponentNonneg : 0 <= abs s0.re + 4 := by positivity
    have hRatioBound : norm (ratio s t) <=
        (3 : Real) ^ (abs s0.re + 4) := by
      dsimp [ratio]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos htPos]
      calc
        t ^ (2 - s.re) <= t ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow_of_exponent_le htOne hExponent
        _ <= (3 : Real) ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow (le_of_lt htPos) htThree hExponentNonneg
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt htPos)
    dsimp [F]
    rw [show -(s + 1) = (-3 : Complex) + ((2 : Complex) - s) by ring,
      Complex.cpow_add _ _ htZero, norm_mul]
    dsimp [majorant, base]
    simp only [norm_mul]
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hRatioBound
        (mul_nonneg (norm_nonneg ((nicolasPsiError t : Complex)))
          (norm_nonneg ((t : Complex) ^ (-3 : Complex)))))
  have hFIntegrable : Integrable (F s0)
      (volume.restrict (Ioc (1 : Real) 3)) := by
    apply Integrable.mono hMajorantIntegrable (hMeasurable s0)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hMajorantNonneg : 0 <= majorant t := by
      dsimp [majorant]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hMajorantNonneg]
    exact hBound s0 (by simp [dist_self]) t ht.1 ht.2
  have hDerivativeMeasurable : AEStronglyMeasurable (F' s0)
      (volume.restrict (Ioc (1 : Real) 3)) := by
    have hRealLogOn : ContinuousOn (fun t : Real => Real.log t)
        (Ioc (1 : Real) 3) := by
      apply Real.continuousOn_log.mono
      intro t ht
      exact Set.mem_compl_singleton_iff.mpr
        (ne_of_gt (lt_trans zero_lt_one ht.1))
    have hRealLog : AEStronglyMeasurable (fun t : Real => Real.log t)
        (volume.restrict (Ioc (1 : Real) 3)) :=
      hRealLogOn.aestronglyMeasurable measurableSet_Ioc
    have hLog : AEStronglyMeasurable
        (fun t : Real => ((Real.log t : Real) : Complex))
        (volume.restrict (Ioc (1 : Real) 3)) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hRealLog
    exact hLog.neg.mul (hMeasurable s0)
  have hDerivativeBound : Filter.Eventually
      (fun t : Real => forall s : Complex, Membership.mem (Metric.ball s0 1) s ->
        norm (F' s t) <= 3 * majorant t)
      (ae (volume.restrict (Ioc (1 : Real) 3))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro s hs
    have htPos : 0 < t := lt_trans zero_lt_one ht.1
    have hLogNonneg : 0 <= Real.log t := Real.log_nonneg ht.1.le
    have hLogBound : Real.log t <= 3 := by
      have hLogSub := Real.log_le_sub_one_of_pos htPos
      linarith [ht.2]
    have hFBound : norm (F s t) <= majorant t :=
      hBound s (by simpa [Metric.mem_ball] using hs) t ht.1 ht.2
    dsimp [F']
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hLogNonneg]
    exact mul_le_mul hLogBound hFBound (norm_nonneg _) (by norm_num)
  have hDerivativeIntegrable : Integrable (fun t : Real => 3 * majorant t)
      (volume.restrict (Ioc (1 : Real) 3)) :=
    hMajorantIntegrable.const_mul 3
  have hDerivative : Filter.Eventually
      (fun t : Real => forall s : Complex, Membership.mem (Metric.ball s0 1) s ->
        HasDerivAt (fun z : Complex => F z t) (F' s t) s)
      (ae (volume.restrict (Ioc (1 : Real) 3))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro s hs
    have htPos : 0 < t := lt_trans zero_lt_one ht.1
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt htPos)
    have hExponent : HasDerivAt (fun z : Complex => -(z + 1)) (-1) s := by
      have hRaw := ((hasDerivAt_id' s).add_const 1).neg
      exact hRaw.congr_of_eventuallyEq
        (Eventually.of_forall (fun _ => rfl))
    have hPower := hExponent.const_cpow (Or.inl htZero)
    have hProduct := hPower.const_smul (nicolasPsiError t : Complex)
    have hProduct' : HasDerivAt
        (fun z : Complex => (nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(z + 1)))
        ((nicolasPsiError t : Complex) *
          ((t : Complex) ^ (-(s + 1)) * Complex.log (t : Complex) * -1)) s := by
      convert hProduct using 1 <;> try rfl
    dsimp [F, F']
    apply hProduct'.congr_deriv
    rw [Complex.ofReal_log htPos.le]
    ring
  unfold nicolasPsiMellinStartup
  have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s0 zero_lt_one)
    (Eventually.of_forall hMeasurable) hFIntegrable
    hDerivativeMeasurable hDerivativeBound hDerivativeIntegrable hDerivative
  exact hMain.2.differentiableAt

theorem nicolasPsiMellinStartup_three_differentiable :
    Differentiable Complex (nicolasPsiMellinStartup 3) :=
  nicolasPsiMellinStartup_three_differentiableAt

theorem nicolasPsiMellinStartup_three_analyticAt (s0 : Complex) :
    AnalyticAt Complex (nicolasPsiMellinStartup 3) s0 :=
  nicolasPsiMellinStartup_three_differentiable.analyticAt s0

def nicolasPsiMellinTailContinuationFilled (s : Complex) : Complex :=
  nicolasPsiMellinContinuationFilled s - nicolasPsiMellinStartup 3 s

theorem nicolasPsiMellinTailContinuationFilled_analyticAt_one :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled 1 := by
  unfold nicolasPsiMellinTailContinuationFilled
  exact nicolasPsiMellinContinuationFilled_analyticAt_one.sub
    (nicolasPsiMellinStartup_three_analyticAt 1)

theorem nicolasPsiMellinTailContinuationFilled_eq_raw
    {s : Complex} (hsZero : Not (s = 0)) (hsOne : Not (s = 1))
    (hZeta : Not (riemannZeta s = 0)) :
    nicolasPsiMellinTailContinuationFilled s =
      nicolasPsiMellinTailContinuation 3 s := by
  unfold nicolasPsiMellinTailContinuationFilled
    nicolasPsiMellinTailContinuation
  rw [nicolasPsiMellinContinuationFilled_eq_raw hsZero hsOne hZeta]

theorem nicolasZetaPoleFactor_ne_zero_of_zeta_ne_zero
    {s : Complex} (hsOne : Not (s = 1))
    (hZeta : Not (riemannZeta s = 0)) :
    Not (nicolasZetaPoleFactor s = 0) := by
  intro hFactor
  have hIdentity := riemannZeta_eq_nicolasZetaPoleFactor_div hsOne
  rw [hFactor, zero_div] at hIdentity
  exact hZeta hIdentity

theorem nicolasPsiMellinContinuationFilled_analyticAt
    {s : Complex} (hsZero : Not (s = 0))
    (hFactor : Not (nicolasZetaPoleFactor s = 0)) :
    AnalyticAt Complex nicolasPsiMellinContinuationFilled s := by
  have hPoleFactor : AnalyticAt Complex nicolasZetaPoleFactor s :=
    nicolasZetaPoleFactor_differentiable.analyticAt s
  have hPoleFactorDeriv : AnalyticAt Complex
      (deriv nicolasZetaPoleFactor) s :=
    nicolasZetaPoleFactor_differentiable.deriv.analyticAt s
  have hLogDeriv : AnalyticAt Complex
      (logDeriv nicolasZetaPoleFactor) s := by
    unfold logDeriv
    exact hPoleFactorDeriv.div hPoleFactor hFactor
  have hOne : AnalyticAt Complex (fun _ : Complex => (1 : Complex)) s :=
    analyticAt_const
  have hNumerator : AnalyticAt Complex
      (fun w : Complex => -(logDeriv nicolasZetaPoleFactor w + 1)) s :=
    (hLogDeriv.add hOne).neg
  unfold nicolasPsiMellinContinuationFilled
  exact hNumerator.div analyticAt_id hsZero

theorem nicolasPsiMellinTailContinuationFilled_eq_raw_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    nicolasPsiMellinTailContinuationFilled s =
      nicolasPsiMellinTailContinuation 3 s := by
  have hsZero : Not (s = 0) := by
    intro hZero
    rw [hZero] at hs
    norm_num at hs
  have hsOne : Not (s = 1) := by
    intro hOne
    rw [hOne] at hs
    norm_num at hs
  exact nicolasPsiMellinTailContinuationFilled_eq_raw
    hsZero hsOne (riemannZeta_ne_zero_of_one_lt_re hs)

theorem abs_nicolasPsiError_le_linear
    {t : Real} (ht : 0 <= t) :
    abs (nicolasPsiError t) <= (Real.log 4 + 5) * t := by
  have hPsiNonneg : 0 <= Chebyshev.psi t := Chebyshev.psi_nonneg t
  have hPsi := Chebyshev.psi_le_const_mul_self ht
  unfold nicolasPsiError
  calc
    abs (Chebyshev.psi t - t) <=
        abs (Chebyshev.psi t) + abs t := abs_sub _ _
    _ = Chebyshev.psi t + t := by
      rw [abs_of_nonneg hPsiNonneg, abs_of_nonneg ht]
    _ <= (Real.log 4 + 4) * t + t := by
      simpa [add_comm] using add_le_add_right hPsi t
    _ = (Real.log 4 + 5) * t := by ring

theorem norm_nicolasPsiMellinTailContinuationFilled_le
    {s : Complex} (hs : 1 < s.re) :
    norm (nicolasPsiMellinTailContinuationFilled s) <=
      (Real.log 4 + 5) * (3 ^ (1 - s.re) / (s.re - 1)) := by
  let c : Real := Real.log 4 + 5
  have hcPos : 0 < c := by
    dsimp [c]
    positivity
  have hPowerIntegrable : IntegrableOn
      (fun t : Real => t ^ (-s.re)) (Ioi (3 : Real)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hMajorantIntegrable : IntegrableOn
      (fun t : Real => c * t ^ (-s.re)) (Ioi (3 : Real)) :=
    hPowerIntegrable.const_mul c
  have hIntegralEq :
      integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          (nicolasPsiError t : Complex) *
            (t : Complex) ^ (-(s + 1))) =
        nicolasPsiMellinTailContinuationFilled s := by
    calc
      integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          (nicolasPsiError t : Complex) *
            (t : Complex) ^ (-(s + 1))) =
          nicolasPsiMellinTailContinuation 3 s :=
        nicolasPsiErrorTailMellin_eq_continuation (by norm_num) hs
      _ = nicolasPsiMellinTailContinuationFilled s :=
        (nicolasPsiMellinTailContinuationFilled_eq_raw_of_one_lt_re hs).symm
  have hNormIntegral :
      norm (integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
          (nicolasPsiError t : Complex) *
            (t : Complex) ^ (-(s + 1)))) <=
        integral (volume.restrict (Ioi (3 : Real)))
          (fun t : Real => c * t ^ (-s.re)) := by
    apply MeasureTheory.norm_integral_le_of_norm_le hMajorantIntegrable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htPos : 0 < t := lt_trans (by norm_num) ht
    have hError := abs_nicolasPsiError_le_linear htPos.le
    have hPowNonneg : 0 <= t ^ (-(s + 1)).re :=
      Real.rpow_nonneg htPos.le _
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos htPos]
    calc
      abs (nicolasPsiError t) * t ^ (-(s + 1)).re <=
          (c * t) * t ^ (-(s + 1)).re :=
        mul_le_mul_of_nonneg_right (by simpa [c] using hError) hPowNonneg
      _ = c * t ^ (-s.re) := by
        calc
          (c * t) * t ^ (-(s + 1)).re =
              c * (t ^ (1 : Real) * t ^ (-(s + 1)).re) := by
            rw [Real.rpow_one]
            ring
          _ = c * t ^ ((1 : Real) + (-(s + 1)).re) := by
            rw [Real.rpow_add htPos]
          _ = c * t ^ (-s.re) := by
            congr 2
            simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
            ring
  rw [<- hIntegralEq]
  calc
    norm (integral (volume.restrict (Ioi (3 : Real))) (fun t : Real =>
        (nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1)))) <=
        integral (volume.restrict (Ioi (3 : Real)))
          (fun t : Real => c * t ^ (-s.re)) := hNormIntegral
    _ = c * (-3 ^ (-s.re + 1) / (-s.re + 1)) := by
      rw [integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith) (by norm_num)]
    _ = (Real.log 4 + 5) * (3 ^ (1 - s.re) / (s.re - 1)) := by
      dsimp [c]
      have hDen : Not (s.re - 1 = 0) := ne_of_gt (sub_pos.mpr hs)
      have hDenLeft : Not (-s.re + 1 = 0) := by linarith
      field_simp [hDen, hDenLeft]
      ring

def nicolasJShiftNumeratorFilled (u : Real) (z : Complex) : Complex :=
  nicolasPsiMellinTailContinuationFilled
      (((u + 1 : Real) : Complex) - z) -
    (3 : Complex) ^ z * nicolasPsiMellinTailContinuationFilled
      ((u + 1 : Real) : Complex)

theorem nicolasJShiftNumeratorFilled_zero (u : Real) :
    nicolasJShiftNumeratorFilled u 0 = 0 := by
  unfold nicolasJShiftNumeratorFilled
  simp

def nicolasJMellinShiftIntegrandFilled (z : Complex) (u : Real) : Complex :=
  ((u + 1 : Real) : Complex) *
    dslope (nicolasJShiftNumeratorFilled u) 0 z

def nicolasJDerivativeStep (n : Nat) : Complex :=
  (((1 : Real) / (8 * ((n : Real) + 1)) : Real) : Complex)

theorem nicolasJDerivativeStep_ne_zero (n : Nat) :
    Not (nicolasJDerivativeStep n = 0) := by
  unfold nicolasJDerivativeStep
  exact Complex.ofReal_ne_zero.mpr
    (div_ne_zero (by norm_num) (by positivity))

theorem norm_nicolasJDerivativeStep_lt (n : Nat) :
    norm (nicolasJDerivativeStep n) <= (1 / 8 : Real) := by
  unfold nicolasJDerivativeStep
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity :
      0 < (1 : Real) / (8 * ((n : Real) + 1)))]
  apply one_div_le_one_div_of_le (by norm_num : (0 : Real) < 8)
  have hn : 0 <= (n : Real) := by positivity
  nlinarith

theorem nicolasJDerivativeStep_tendsto_zero :
    Tendsto nicolasJDerivativeStep atTop (nhds (0 : Complex)) := by
  have hRecip : Tendsto
      (fun n : Nat => (1 : Real) / ((n : Real) + 1))
      atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hScaled : Tendsto
      (fun n : Nat => (1 / 8 : Real) *
        ((1 : Real) / ((n : Real) + 1)))
      atTop (nhds ((1 / 8 : Real) * 0)) :=
    tendsto_const_nhds.mul hRecip
  have hFunctions :
      (fun n : Nat => (1 : Real) / (8 * ((n : Real) + 1))) =
        (fun n : Nat => (1 / 8 : Real) *
          ((1 : Real) / ((n : Real) + 1))) := by
    funext n
    field_simp
  have hReal : Tendsto
      (fun n : Nat => (1 : Real) / (8 * ((n : Real) + 1)))
      atTop (nhds 0) := by
    rw [hFunctions]
    simpa using hScaled
  have hCast := Complex.continuous_ofReal.continuousAt.tendsto.comp hReal
  change Tendsto nicolasJDerivativeStep atTop (nhds (0 : Complex)) at hCast
  exact hCast

def nicolasJShiftedComplexContinuationFilledLarge (z : Complex) : Complex :=
  integral (volume.restrict (Ioi (1 : Real)))
    (nicolasJMellinShiftIntegrandFilled z)

theorem nicolasJMellinShiftIntegrandFilled_eq_raw
    {z : Complex} (hzRe : z.re < 0) {u : Real} (hu : 0 < u) :
    nicolasJMellinShiftIntegrandFilled z u =
      nicolasJMellinShiftIntegrand z u := by
  have hzZero : Not (z = 0) := by
    intro hZero
    rw [hZero] at hzRe
    norm_num at hzRe
  have hBaseRe : 1 < (((u + 1 : Real) : Complex)).re := by
    simp
    linarith
  have hShiftRe : 1 <
      ((((u + 1 : Real) : Complex) - z)).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have hBaseEq :=
    nicolasPsiMellinTailContinuationFilled_eq_raw_of_one_lt_re hBaseRe
  have hShiftEq :=
    nicolasPsiMellinTailContinuationFilled_eq_raw_of_one_lt_re hShiftRe
  unfold nicolasJMellinShiftIntegrandFilled
  rw [dslope_of_ne _ hzZero]
  unfold slope
  rw [nicolasJShiftNumeratorFilled_zero]
  unfold nicolasJShiftNumeratorFilled nicolasJMellinShiftIntegrand
  rw [hBaseEq, hShiftEq]
  simp only [sub_zero, smul_eq_mul, vsub_eq_sub]
  field_simp [hzZero]

def nicolasJShiftedComplexContinuationFilled (z : Complex) : Complex :=
  integral (volume.restrict (Ioi (0 : Real)))
    (nicolasJMellinShiftIntegrandFilled z)

end

end Robin1984

end
section

namespace Robin1984

open Filter MeasureTheory Set

noncomputable section

alias riemannZeta_real_ne_zero_of_mem_Ioo_zero_one :=
  RiemannZeta.real_ne_zero_of_mem_Ioo_zero_one

alias nicolasZetaPoleFactor_ne_zero_of_pos_real :=
  RiemannZeta.poleFactor_ne_zero_of_pos_real

theorem nicolasPsiMellinTailContinuationFilled_analyticAt_pos_real
    {s : Real} (hs : 0 < s) :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled (s : Complex) := by
  by_cases hsOne : s = 1
  case pos =>
    subst s
    exact nicolasPsiMellinTailContinuationFilled_analyticAt_one
  case neg =>
    have hsZero : Not ((s : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr hs.ne'
    have hFactor := nicolasZetaPoleFactor_ne_zero_of_pos_real hs
    unfold nicolasPsiMellinTailContinuationFilled
    exact (nicolasPsiMellinContinuationFilled_analyticAt hsZero hFactor).sub
      (nicolasPsiMellinStartup_three_analyticAt (s : Complex))

def nicolasJLargeMajorantHalf (u : Real) : Real :=
  (20 / 3 : Real) * (Real.log 4 + 5) * (u + 1) *
    (3 : Real) ^ (-u + (3 / 4 : Real))

theorem nicolasJLargeMajorantHalf_integrableOn :
    IntegrableOn nicolasJLargeMajorantHalf (Ioi (1 : Real)) := by
  have hLog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hExp : IntegrableOn
      (fun u : Real => Real.exp (-(Real.log 3) * u))
      (Ioi (1 : Real)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : Real)) (s := (0 : Real)) (b := Real.log 3)
      (by norm_num) (by norm_num) hLog
    have hSubset : Ioi (1 : Real) <= Ioi (0 : Real) := by
      intro u hu
      exact zero_lt_one.trans (mem_Ioi.mp hu)
    apply (h.mono_set hSubset).congr_fun _ measurableSet_Ioi
    intro u hu
    simp
  have hUExp : IntegrableOn
      (fun u : Real => u * Real.exp (-(Real.log 3) * u))
      (Ioi (1 : Real)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : Real)) (s := (1 : Real)) (b := Real.log 3)
      (by norm_num) (by norm_num) hLog
    have hSubset : Ioi (1 : Real) <= Ioi (0 : Real) := by
      intro u hu
      exact zero_lt_one.trans (mem_Ioi.mp hu)
    apply (h.mono_set hSubset).congr_fun _ measurableSet_Ioi
    intro u hu
    simp
  have hLinear : IntegrableOn
      (fun u : Real => (u + 1) * Real.exp (-(Real.log 3) * u))
      (Ioi (1 : Real)) := by
    apply (hUExp.add hExp).congr_fun _ measurableSet_Ioi
    intro u hu
    change u * Real.exp (-(Real.log 3) * u) +
      Real.exp (-(Real.log 3) * u) =
        (u + 1) * Real.exp (-(Real.log 3) * u)
    ring
  have hScaled : IntegrableOn
      (fun u : Real =>
        ((20 / 3 : Real) * (Real.log 4 + 5) *
            Real.exp (3 * Real.log 3 / 4)) *
          ((u + 1) * Real.exp (-(Real.log 3) * u)))
      (Ioi (1 : Real)) :=
    hLinear.const_mul
      ((20 / 3 : Real) * (Real.log 4 + 5) *
        Real.exp (3 * Real.log 3 / 4))
  apply hScaled.congr_fun _ measurableSet_Ioi
  intro u hu
  unfold nicolasJLargeMajorantHalf
  rw [Real.rpow_def_of_pos (by norm_num : (0 : Real) < 3)]
  rw [show Real.log 3 * (-u + (3 / 4 : Real)) =
      3 * Real.log 3 / 4 + (-(Real.log 3) * u) by ring]
  rw [Real.exp_add]
  ring

end

end Robin1984

end
section

namespace Robin1984

open Filter MeasureTheory Set

open scoped ENNReal Topology

noncomputable section

def nicolasJShiftedComplexContinuationFilledCompact (z : Complex) : Complex :=
  integral (volume.restrict (Ioc (0 : Real) 1))
    (nicolasJMellinShiftIntegrandFilled z)

end

end Robin1984

end
section

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set

noncomputable section

theorem nicolasPsiMellinTailContinuationFilled_analyticAt_of_ne_zero_of_factor_ne_zero
    {s : Complex} (hsZero : Not (s = 0))
    (hFactor : Not (nicolasZetaPoleFactor s = 0)) :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled s := by
  unfold nicolasPsiMellinTailContinuationFilled
  exact (nicolasPsiMellinContinuationFilled_analyticAt hsZero hFactor).sub
    (nicolasPsiMellinStartup_three_analyticAt s)

theorem nicolasJMellinShiftIntegrandFilled_joint_continuousAt
    {u : Real} (hu : 0 <= u) {z : Complex}
    (hzZero : Not (z = 0))
    (hShiftZero : Not ((((u + 1 : Real) : Complex) - z) = 0))
    (hFactor : Not (nicolasZetaPoleFactor
      (((u + 1 : Real) : Complex) - z) = 0)) :
    ContinuousAt (fun p : Prod Real Complex =>
      nicolasJMellinShiftIntegrandFilled p.2 p.1) (u, z) := by
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs0Pos : 0 < u + 1 := by linarith
  have hTail0 : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled s0 := by
    simpa [s0] using
      nicolasPsiMellinTailContinuationFilled_analyticAt_pos_real hs0Pos
  have hTail1 : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled s1 := by
    exact
      nicolasPsiMellinTailContinuationFilled_analyticAt_of_ne_zero_of_factor_ne_zero
        (by simpa [s1, s0] using hShiftZero)
        (by simpa [s1, s0] using hFactor)
  let S0 : Prod Real Complex -> Complex := fun p =>
    ((p.1 + 1 : Real) : Complex)
  let S1 : Prod Real Complex -> Complex := fun p => S0 p - p.2
  have hS0 : Continuous S0 := by
    dsimp [S0]
    fun_prop
  have hS1 : Continuous S1 := by
    dsimp [S1]
    exact hS0.sub continuous_snd
  have hTail0Comp : ContinuousAt (fun p : Prod Real Complex =>
      nicolasPsiMellinTailContinuationFilled (S0 p)) (u, z) := by
    have hAt : ContinuousAt nicolasPsiMellinTailContinuationFilled
        (S0 (u, z)) := by
      simpa [S0, s0] using hTail0.continuousAt
    exact hAt.comp' hS0.continuousAt
  have hTail1Comp : ContinuousAt (fun p : Prod Real Complex =>
      nicolasPsiMellinTailContinuationFilled (S1 p)) (u, z) := by
    have hAt : ContinuousAt nicolasPsiMellinTailContinuationFilled
        (S1 (u, z)) := by
      simpa [S1, S0, s1, s0] using hTail1.continuousAt
    exact hAt.comp' hS1.continuousAt
  have hPower : Continuous (fun p : Prod Real Complex =>
      (3 : Complex) ^ p.2) := by
    fun_prop
  let raw : Prod Real Complex -> Complex := fun p =>
    ((p.1 + 1 : Real) : Complex) * Inv.inv (p.2 - 0) *
      (nicolasJShiftNumeratorFilled p.1 p.2 -
        nicolasJShiftNumeratorFilled p.1 0)
  have hNumerator : ContinuousAt (fun p : Prod Real Complex =>
      nicolasJShiftNumeratorFilled p.1 p.2) (u, z) := by
    unfold nicolasJShiftNumeratorFilled
    change ContinuousAt (fun p : Prod Real Complex =>
      nicolasPsiMellinTailContinuationFilled (S1 p) -
        (3 : Complex) ^ p.2 *
          nicolasPsiMellinTailContinuationFilled (S0 p)) (u, z)
    exact hTail1Comp.sub (hPower.continuousAt.mul hTail0Comp)
  have hNumeratorZero : ContinuousAt (fun p : Prod Real Complex =>
      nicolasJShiftNumeratorFilled p.1 0) (u, z) := by
    have hEq : (fun p : Prod Real Complex =>
        nicolasJShiftNumeratorFilled p.1 0) = fun _ => 0 := by
      funext p
      exact nicolasJShiftNumeratorFilled_zero p.1
    rw [hEq]
    exact continuousAt_const
  have hRaw : ContinuousAt raw (u, z) := by
    dsimp [raw]
    have hInv : ContinuousAt (fun p : Prod Real Complex =>
        Inv.inv (p.2 - 0)) (u, z) := by
      have hDen : ContinuousAt (fun p : Prod Real Complex => p.2 - 0)
          (u, z) := continuousAt_snd.sub continuousAt_const
      have hDiv : ContinuousAt (fun p : Prod Real Complex =>
          (1 : Complex) / (p.2 - 0)) (u, z) :=
        continuousAt_const.div hDen (by simpa using hzZero)
      simpa [one_div] using hDiv
    have hU : Continuous (fun p : Prod Real Complex =>
        ((p.1 + 1 : Real) : Complex)) := by
      fun_prop
    exact (hU.continuousAt.mul hInv).mul
      (hNumerator.sub hNumeratorZero)
  have hSecondNe : Filter.Eventually
      (fun p : Prod Real Complex => Not (p.2 = 0)) (nhds (u, z)) := by
    have hSecondContinuous : ContinuousAt
        (fun p : Prod Real Complex => p.2) (u, z) := continuousAt_snd
    exact hSecondContinuous.eventually_ne hzZero
  have hEq : Filter.EventuallyEq (nhds (u, z))
      (fun p : Prod Real Complex =>
        nicolasJMellinShiftIntegrandFilled p.2 p.1) raw := by
    filter_upwards [hSecondNe] with p hp
    unfold nicolasJMellinShiftIntegrandFilled raw
    rw [dslope_of_ne _ hp]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub]
    ring
  exact hRaw.congr_of_eventuallyEq hEq

theorem nicolasJMellinShiftIntegrandFilled_analyticAt_of_ne_zero_of_factor_ne_zero
    {u : Real} (hu : 0 <= u) {z : Complex}
    (hzZero : Not (z = 0))
    (hShiftZero : Not ((((u + 1 : Real) : Complex) - z) = 0))
    (hFactor : Not (nicolasZetaPoleFactor
      (((u + 1 : Real) : Complex) - z) = 0)) :
    AnalyticAt Complex (fun w : Complex =>
      nicolasJMellinShiftIntegrandFilled w u) z := by
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs0Pos : 0 < u + 1 := by linarith
  have hTail0 : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled s0 := by
    simpa [s0] using
      nicolasPsiMellinTailContinuationFilled_analyticAt_pos_real hs0Pos
  have hTail1 : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled s1 :=
    nicolasPsiMellinTailContinuationFilled_analyticAt_of_ne_zero_of_factor_ne_zero
      (by simpa [s1, s0] using hShiftZero)
      (by simpa [s1, s0] using hFactor)
  have hAffine : AnalyticAt Complex (fun w : Complex => s0 - w) z :=
    analyticAt_const.sub analyticAt_id
  have hShift : AnalyticAt Complex (fun w : Complex =>
      nicolasPsiMellinTailContinuationFilled (s0 - w)) z := by
    have hComp := hTail1.comp_of_eq hAffine (by simp [s1])
    exact hComp.congr (Eventually.of_forall (fun _ => rfl))
  have hPower : AnalyticAt Complex (fun w : Complex =>
      (3 : Complex) ^ w) z := by
    have hDiff : Differentiable Complex (fun w : Complex =>
        (3 : Complex) ^ w) := by
      intro w
      exact DifferentiableAt.const_cpow differentiableAt_id
        (Or.inl (by norm_num))
    exact hDiff.analyticAt z
  have hNumerator : AnalyticAt Complex
      (nicolasJShiftNumeratorFilled u) z := by
    unfold nicolasJShiftNumeratorFilled
    exact hShift.sub (hPower.mul analyticAt_const)
  let raw : Complex -> Complex := fun w =>
    ((u + 1 : Real) : Complex) *
      slope (nicolasJShiftNumeratorFilled u) 0 w
  have hRaw : AnalyticAt Complex raw z := by
    have hDifference : AnalyticAt Complex (fun w : Complex =>
        nicolasJShiftNumeratorFilled u w -
          nicolasJShiftNumeratorFilled u 0) z :=
      hNumerator.sub analyticAt_const
    have hDenominator : AnalyticAt Complex (fun w : Complex => w - 0) z :=
      analyticAt_id.sub analyticAt_const
    have hQuotient := hDifference.div hDenominator
      (sub_ne_zero.mpr hzZero)
    have hDiv : AnalyticAt Complex (fun w : Complex =>
        ((u + 1 : Real) : Complex) *
          ((nicolasJShiftNumeratorFilled u w -
            nicolasJShiftNumeratorFilled u 0) / (w - 0))) z :=
      analyticAt_const.mul hQuotient
    have hRawEq : Filter.EventuallyEq (nhds z) raw
        (fun w : Complex => ((u + 1 : Real) : Complex) *
          ((nicolasJShiftNumeratorFilled u w -
            nicolasJShiftNumeratorFilled u 0) / (w - 0))) :=
      Eventually.of_forall (fun w => by
        unfold raw slope
        simp only [smul_eq_mul, vsub_eq_sub, div_eq_mul_inv]
        ring)
    exact (analyticAt_congr hRawEq).mpr hDiv
  have hEq : Filter.EventuallyEq (nhds z)
      (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u) raw := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hzZero] with w hw
    unfold nicolasJMellinShiftIntegrandFilled raw
    rw [dslope_of_ne _ hw]
  exact (analyticAt_congr hEq).mpr hRaw

def nicolasCompactStripDerivativeStep (R : Real) (n : Nat) : Complex :=
  (R : Complex) * nicolasJDerivativeStep n

theorem nicolasCompactStripDerivativeStep_ne_zero
    {R : Real} (hRPos : 0 < R) (n : Nat) :
    Not (nicolasCompactStripDerivativeStep R n = 0) := by
  unfold nicolasCompactStripDerivativeStep
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hRPos.ne')
    (nicolasJDerivativeStep_ne_zero n)

theorem norm_nicolasCompactStripDerivativeStep_le
    {R : Real} (hRPos : 0 < R) (n : Nat) :
    norm (nicolasCompactStripDerivativeStep R n) <= R / 8 := by
  unfold nicolasCompactStripDerivativeStep
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRPos]
  calc
    R * norm (nicolasJDerivativeStep n) <= R * (1 / 8 : Real) :=
      mul_le_mul_of_nonneg_left (norm_nicolasJDerivativeStep_lt n) hRPos.le
    _ = R / 8 := by ring

theorem nicolasCompactStripDerivativeStep_tendsto_zero
    (R : Real) :
    Tendsto (nicolasCompactStripDerivativeStep R) atTop
      (nhds (0 : Complex)) := by
  have hConst : Tendsto (fun _ : Nat => (R : Complex)) atTop
      (nhds (R : Complex)) := tendsto_const_nhds
  have h := hConst.mul nicolasJDerivativeStep_tendsto_zero
  unfold nicolasCompactStripDerivativeStep
  simpa using h

end

end Robin1984

end
section

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal Topology

noncomputable section

theorem riemannZeta_zero_im_ne_zero_of_re_mem_Ioo
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hRePos : 0 < rho.re) (hReLt : rho.re < 1) :
    Not (rho.im = 0) := by
  intro hIm
  have hEq : rho = (rho.re : Complex) := by
    apply Complex.ext
    . simp
    . simpa using hIm
  rw [hEq] at hZero
  exact (riemannZeta_real_ne_zero_of_mem_Ioo_zero_one
    (And.intro hRePos hReLt)) hZero

theorem nicolasJShiftedComplexContinuationFilledCompact_analyticAt_of_tube
    {center : Complex} {R : Real} (hRPos : 0 < R)
    (hGood : forall z : Complex,
      Membership.mem (Metric.ball center R) z ->
        And (Not (z = 0))
          (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
            And (Not ((((u + 1 : Real) : Complex) - z) = 0))
              (Not (nicolasZetaPoleFactor
                (((u + 1 : Real) : Complex) - z) = 0)))) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledCompact
      center := by
  let K : Set (Prod Real Complex) := fun p =>
    And (Membership.mem (Icc (0 : Real) 1) p.1)
      (Membership.mem (Metric.closedBall center (R / 2)) p.2)
  let F : Prod Real Complex -> Complex := fun p =>
    nicolasJMellinShiftIntegrandFilled p.2 p.1
  have hKCompact : IsCompact K := by
    dsimp [K]
    exact (isCompact_Icc : IsCompact (Icc (0 : Real) 1)).prod
      (isCompact_closedBall center (R / 2))
  have hKNonempty : K.Nonempty := by
    refine Exists.intro ((0 : Real), center) ?_
    dsimp [K]
    exact And.intro (And.intro le_rfl zero_le_one)
      (Metric.mem_closedBall_self (by linarith))
  have hContinuous : ContinuousOn F K := by
    apply continuousOn_of_forall_continuousAt
    intro p hp
    change And (Membership.mem (Icc (0 : Real) 1) p.1)
      (Membership.mem (Metric.closedBall center (R / 2)) p.2) at hp
    have hpBall : Membership.mem (Metric.ball center R) p.2 := by
      rw [Metric.mem_closedBall] at hp
      rw [Metric.mem_ball]
      linarith
    have hpGood := hGood p.2 hpBall
    exact nicolasJMellinShiftIntegrandFilled_joint_continuousAt
      hp.1.1 hpGood.1 (hpGood.2 p.1 hp.1).1 (hpGood.2 p.1 hp.1).2
  choose p hpK hpMax using hKCompact.exists_isMaxOn hKNonempty hContinuous.norm
  let M : Real := norm (F p)
  have hMNonneg : 0 <= M := norm_nonneg _
  have hKernelBound : forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        forall z : Complex,
          Membership.mem (Metric.closedBall center (R / 2)) z ->
            norm (nicolasJMellinShiftIntegrandFilled z u) <= M := by
    intro u hu z hz
    have hPair : K (u, z) := by
      dsimp [K]
      exact And.intro hu hz
    simpa [M, F] using hpMax hPair
  have hContinuousU : forall z : Complex,
      Membership.mem (Metric.closedBall center (R / 2)) z ->
        ContinuousOn (fun u : Real =>
          nicolasJMellinShiftIntegrandFilled z u) (Icc (0 : Real) 1) := by
    intro z hz
    have hzBall : Membership.mem (Metric.ball center R) z := by
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have hzGood := hGood z hzBall
    intro u hu
    have hJoint := nicolasJMellinShiftIntegrandFilled_joint_continuousAt
      hu.1 hzGood.1 (hzGood.2 u hu).1 (hzGood.2 u hu).2
    have hEmbed : ContinuousAt (fun v : Real => (v, z)) u := by
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    have hAt : ContinuousAt (fun v : Real =>
        nicolasJMellinShiftIntegrandFilled z v) u := by
      simpa [Function.comp_def] using hComp
    exact hAt.continuousWithinAt
  have hAnalytic : forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        forall z : Complex,
          Membership.mem (Metric.closedBall center (R / 2)) z ->
            AnalyticAt Complex (fun w : Complex =>
              nicolasJMellinShiftIntegrandFilled w u) z := by
    intro u hu z hz
    have hzBall : Membership.mem (Metric.ball center R) z := by
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have hzGood := hGood z hzBall
    exact
      nicolasJMellinShiftIntegrandFilled_analyticAt_of_ne_zero_of_factor_ne_zero
        hu.1 hzGood.1 (hzGood.2 u hu).1 (hzGood.2 u hu).2
  have hDerivativeMeasurable : forall z : Complex,
      Membership.mem (Metric.ball center (R / 4)) z ->
        AEStronglyMeasurable (fun u : Real =>
          deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z)
          (volume.restrict (Ioc (0 : Real) 1)) := by
    intro z hz
    let slopeSeq : Nat -> Real -> Complex := fun n : Nat => fun u : Real =>
      slope (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u)
        z (z + nicolasCompactStripDerivativeStep R n)
    have hzDist : dist z center < R / 4 := by
      simpa [Metric.mem_ball] using hz
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      rw [Metric.mem_closedBall]
      linarith
    have hShiftClosed : forall n : Nat,
        Membership.mem (Metric.closedBall center (R / 2))
          (z + nicolasCompactStripDerivativeStep R n) := by
      intro n
      rw [Metric.mem_closedBall]
      calc
        dist (z + nicolasCompactStripDerivativeStep R n) center <=
            dist (z + nicolasCompactStripDerivativeStep R n) z +
              dist z center := dist_triangle _ z _
        _ = norm (nicolasCompactStripDerivativeStep R n) +
              dist z center := by rw [dist_eq_norm]; simp
        _ <= R / 8 + R / 4 :=
          (add_lt_add_of_le_of_lt
            (norm_nicolasCompactStripDerivativeStep_le hRPos n) hzDist).le
        _ <= R / 2 := by linarith
    have hMeas : forall n : Nat, AEMeasurable (slopeSeq n)
        (volume.restrict (Ioc (0 : Real) 1)) := by
      intro n
      have hShift := (hContinuousU _ (hShiftClosed n)).mono
        Ioc_subset_Icc_self
      have hBase := (hContinuousU z hzClosed).mono Ioc_subset_Icc_self
      have hShiftMeas : AEStronglyMeasurable
          (fun u : Real => nicolasJMellinShiftIntegrandFilled
            (z + nicolasCompactStripDerivativeStep R n) u)
          (volume.restrict (Ioc (0 : Real) 1)) :=
        hShift.aestronglyMeasurable measurableSet_Ioc
      have hBaseMeas : AEStronglyMeasurable
          (fun u : Real => nicolasJMellinShiftIntegrandFilled z u)
          (volume.restrict (Ioc (0 : Real) 1)) :=
        hBase.aestronglyMeasurable measurableSet_Ioc
      have hEq : slopeSeq n = fun u : Real =>
          Inv.inv ((z + nicolasCompactStripDerivativeStep R n) - z) *
            (nicolasJMellinShiftIntegrandFilled
                (z + nicolasCompactStripDerivativeStep R n) u -
              nicolasJMellinShiftIntegrandFilled z u) := by
        funext u
        dsimp [slopeSeq]
        unfold slope
        simp only [smul_eq_mul, vsub_eq_sub]
      rw [hEq]
      exact ((hShiftMeas.sub hBaseMeas).const_mul
        (Inv.inv ((z + nicolasCompactStripDerivativeStep R n) - z))).aemeasurable
    have hStepWithin : Tendsto (nicolasCompactStripDerivativeStep R) atTop
        (nhdsWithin (0 : Complex) (Set.compl {(0 : Complex)})) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact And.intro (nicolasCompactStripDerivativeStep_tendsto_zero R)
        (Eventually.of_forall (fun n : Nat =>
          Set.mem_compl_singleton_iff.mpr
            (nicolasCompactStripDerivativeStep_ne_zero hRPos n)))
    have hTendsto : Filter.Eventually
        (fun u : Real => Tendsto (fun n : Nat => slopeSeq n u) atTop
          (nhds (deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z)))
        (ae (volume.restrict (Ioc (0 : Real) 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have huIcc : Membership.mem (Icc (0 : Real) 1) u :=
        Ioc_subset_Icc_self hu
      have hSlope := (hAnalytic u huIcc z hzClosed).differentiableAt.hasDerivAt
        |>.tendsto_slope_zero.comp hStepWithin
      change Tendsto (fun n : Nat =>
        Inv.inv (nicolasCompactStripDerivativeStep R n) *
          (nicolasJMellinShiftIntegrandFilled
              (z + nicolasCompactStripDerivativeStep R n) u -
            nicolasJMellinShiftIntegrandFilled z u))
        atTop (nhds (deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)) at hSlope
      dsimp [slopeSeq]
      unfold slope
      simp only [smul_eq_mul, vsub_eq_sub, add_sub_cancel_left]
      exact hSlope
    exact (aemeasurable_of_tendsto_metrizable_ae'
      hMeas hTendsto).aestronglyMeasurable
  have hDerivativeBound : forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        forall z : Complex,
          Membership.mem (Metric.ball center (R / 4)) z ->
            norm (deriv (fun w : Complex =>
              nicolasJMellinShiftIntegrandFilled w u) z) <= 8 * M / R := by
    intro u hu z hz
    let f : Complex -> Complex := fun w =>
      nicolasJMellinShiftIntegrandFilled w u
    let r : Real := R / 4
    have hzDist : dist z center < R / 4 := by
      simpa [Metric.mem_ball] using hz
    have hSmallSubset : Metric.ball z r <=
        Metric.closedBall center (R / 2) := by
      intro w hw
      rw [Metric.mem_ball] at hw
      rw [Metric.mem_closedBall]
      calc
        dist w center <= dist w z + dist z center := dist_triangle _ z _
        _ <= R / 4 + R / 4 := by
          dsimp [r] at hw
          exact (add_lt_add hw hzDist).le
        _ <= R / 2 := by linarith
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      apply hSmallSubset
      exact Metric.mem_ball_self (by dsimp [r]; linarith)
    have hDiff : DifferentiableOn Complex f (Metric.ball z r) := by
      intro w hw
      exact (hAnalytic u hu w (hSmallSubset hw)).differentiableAt.differentiableWithinAt
    have hMaps : MapsTo f (Metric.ball z r)
        (Metric.closedBall (f z) (2 * M)) := by
      intro w hw
      have hwBound : norm (f w) <= M := hKernelBound u hu w (hSmallSubset hw)
      have hzBound : norm (f z) <= M := hKernelBound u hu z hzClosed
      rw [Metric.mem_closedBall]
      calc
        dist (f w) (f z) <= norm (f w) + norm (f z) := by
          simpa [dist_eq_norm] using norm_sub_le (f w) (f z)
        _ <= M + M := add_le_add hwBound hzBound
        _ = 2 * M := by ring
    have hCauchy := Complex.norm_deriv_le_div_of_mapsTo_ball
      hDiff hMaps (by dsimp [r]; linarith)
    change norm (deriv f z) <= 8 * M / R
    calc
      norm (deriv f z) <= (2 * M) / r := hCauchy
      _ = 8 * M / R := by
        dsimp [r]
        field_simp [hRPos.ne']
        ring
  let s : Set Complex := Metric.ball center (R / 4)
  have hHasDeriv : forall z : Complex, Membership.mem s z ->
      HasDerivAt nicolasJShiftedComplexContinuationFilledCompact
        (integral (volume.restrict (Ioc (0 : Real) 1)) (fun u : Real =>
          deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z)) z := by
    intro z hz
    let G : Complex -> Real -> Complex := fun w => fun u =>
      nicolasJMellinShiftIntegrandFilled w u
    let G' : Complex -> Real -> Complex := fun w => fun u =>
      deriv (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w
    have hsNhd : Membership.mem (nhds z) s :=
      Metric.isOpen_ball.mem_nhds hz
    have hGMeas : Filter.Eventually
        (fun w : Complex => AEStronglyMeasurable (G w)
          (volume.restrict (Ioc (0 : Real) 1))) (nhds z) := by
      filter_upwards [hsNhd] with w hw
      have hwClosed : Membership.mem
          (Metric.closedBall center (R / 2)) w := by
        rw [Metric.mem_closedBall]
        have hwDist : dist w center < R / 4 := by
          simpa [s, Metric.mem_ball] using hw
        linarith
      dsimp [G]
      exact ((hContinuousU w hwClosed).mono Ioc_subset_Icc_self)
        |>.aestronglyMeasurable measurableSet_Ioc
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      rw [Metric.mem_closedBall]
      have hzDist : dist z center < R / 4 := by
        simpa [s, Metric.mem_ball] using hz
      linarith
    have hGInt : Integrable (G z)
        (volume.restrict (Ioc (0 : Real) 1)) := by
      have hInt : IntegrableOn (fun u : Real =>
          nicolasJMellinShiftIntegrandFilled z u) (Icc (0 : Real) 1) := by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        exact hContinuousU z hzClosed
      exact hInt.mono_set Ioc_subset_Icc_self
    have hG'Meas : AEStronglyMeasurable (G' z)
        (volume.restrict (Ioc (0 : Real) 1)) := by
      dsimp [G']
      exact hDerivativeMeasurable z hz
    have hBound : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          norm (G' w u) <= 8 * M / R)
        (ae (volume.restrict (Ioc (0 : Real) 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      intro w hw
      exact hDerivativeBound u (Ioc_subset_Icc_self hu) w hw
    have hBoundInt : IntegrableOn (fun _ : Real => 8 * M / R)
        (Ioc (0 : Real) 1) := by
      have hInt : IntegrableOn (fun _ : Real => 8 * M / R)
          (Icc (0 : Real) 1) := by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        exact continuousOn_const
      exact hInt.mono_set Ioc_subset_Icc_self
    have hDiff : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          HasDerivAt (fun v : Complex => G v u) (G' w u) w)
        (ae (volume.restrict (Ioc (0 : Real) 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      intro w hw
      have hwClosed : Membership.mem
          (Metric.closedBall center (R / 2)) w := by
        rw [Metric.mem_closedBall]
        have hwDist : dist w center < R / 4 := by
          simpa [s, Metric.mem_ball] using hw
        linarith
      dsimp [G, G']
      exact (hAnalytic u (Ioc_subset_Icc_self hu) w hwClosed)
        |>.differentiableAt.hasDerivAt
    have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := G) (F' := G') (bound := fun _ : Real => 8 * M / R)
      hsNhd hGMeas hGInt hG'Meas hBound hBoundInt hDiff
    unfold nicolasJShiftedComplexContinuationFilledCompact
    simpa [G, G'] using hMain.2
  have hDiffOn : DifferentiableOn Complex
      nicolasJShiftedComplexContinuationFilledCompact s := by
    intro z hz
    exact (hHasDeriv z hz).differentiableAt.differentiableWithinAt
  apply hDiffOn.analyticAt
  dsimp [s]
  exact Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self (by linarith : 0 < R / 4))

theorem exists_nicolasRightmostRayCompactTubeRadius
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    Exists fun R : Real => And (0 < R)
      (forall z : Complex,
        Membership.mem
          (Metric.ball ((1 - rho) - (eps : Complex)) R) z ->
          And (Not (z = 0))
            (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
              And (Not ((((u + 1 : Real) : Complex) - z) = 0))
                (Not (nicolasZetaPoleFactor
                  (((u + 1 : Real) : Complex) - z) = 0)))) := by
  let center : Complex := (1 - rho) - (eps : Complex)
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOne
  have hCenterIm : center.im = -rho.im := by
    dsimp [center]
    simp
  have hCenterNe : Not (center = 0) := by
    intro hEq
    have hZeroIm : center.im = 0 := by rw [hEq]; simp
    exact hIm (neg_eq_zero.mp (hCenterIm.symm.trans hZeroIm))
  have hZeroNhd : Filter.Eventually (fun z : Complex => Not (z = 0))
      (nhds center) := continuousAt_id.eventually_ne hCenterNe
  have hShiftNhd : Filter.Eventually (fun z : Complex => forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        Not ((((u + 1 : Real) : Complex) - z) = 0))
      (nhds center) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    have hShiftIm :
        ((((u + 1 : Real) : Complex) - center)).im = rho.im := by
      rw [Complex.sub_im, Complex.ofReal_im, hCenterIm]
      ring
    have hShiftNe : Not ((((u + 1 : Real) : Complex) - center) = 0) := by
      intro hEq
      have hZeroIm : ((((u + 1 : Real) : Complex) - center)).im = 0 := by
        rw [hEq]
        simp
      exact hIm (hShiftIm.symm.trans hZeroIm)
    let G : Prod Complex Real -> Complex := fun p =>
      ((p.2 + 1 : Real) : Complex) - p.1
    have hContinuous : Continuous G := by
      dsimp [G]
      fun_prop
    have hAt : Not (G (center, u) = 0) := by
      simpa [G] using hShiftNe
    exact hContinuous.continuousAt.eventually_ne hAt
  have hFactorNhd : Filter.Eventually (fun z : Complex => forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        Not (nicolasZetaPoleFactor
          (((u + 1 : Real) : Complex) - z) = 0))
      (nhds center) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    let s : Complex := rho + ((eps + u : Real) : Complex)
    have hShift : (((u + 1 : Real) : Complex) - center) = s := by
      dsimp [center, s]
      push_cast
      ring
    have hZeta : Not (riemannZeta s = 0) := by
      dsimp [s]
      exact hRay (eps + u) (by linarith [hu.1])
    have hFactor : Not (nicolasZetaPoleFactor s = 0) := by
      by_cases hsOne : s = 1
      . rw [hsOne, nicolasZetaPoleFactor_one]
        norm_num
      . intro hFactorZero
        have hIdentity := riemannZeta_eq_nicolasZetaPoleFactor_div hsOne
        rw [hFactorZero, zero_div] at hIdentity
        exact hZeta hIdentity
    let G : Prod Complex Real -> Complex := fun p =>
      nicolasZetaPoleFactor (((p.2 + 1 : Real) : Complex) - p.1)
    have hAffine : Continuous (fun p : Prod Complex Real =>
        (((p.2 + 1 : Real) : Complex) - p.1)) := by
      fun_prop
    have hContinuous : Continuous G := by
      dsimp [G]
      exact nicolasZetaPoleFactor_differentiable.continuous.comp hAffine
    have hAt : Not (nicolasZetaPoleFactor
        (((u + 1 : Real) : Complex) - center) = 0) := by
      rw [hShift]
      exact hFactor
    have hPairAt : Not (G (center, u) = 0) := by
      simpa [G] using hAt
    exact hContinuous.continuousAt.eventually_ne hPairAt
  have hAll := hZeroNhd.and (hShiftNhd.and hFactorNhd)
  choose R hRPos hR using Metric.mem_nhds_iff.1 hAll
  refine Exists.intro R (And.intro hRPos ?_)
  intro z hz
  have hzGood := hR hz
  exact And.intro hzGood.1 (fun u hu =>
    And.intro (hzGood.2.1 u hu) (hzGood.2.2 u hu))

theorem nicolasJShiftedComplexContinuationFilledCompact_analyticAt_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledCompact
      ((1 - rho) - (eps : Complex)) := by
  choose R hRPos hGood using
    exists_nicolasRightmostRayCompactTubeRadius
      hZero hHalf hOne hRay hEps
  exact nicolasJShiftedComplexContinuationFilledCompact_analyticAt_of_tube
    hRPos hGood

theorem norm_nicolasJShiftNumeratorFilled_le_of_re_le_threeQuarter
    {u : Real} (hu : 1 < u) {z : Complex}
    (hzRe : z.re <= (3 / 4 : Real)) :
    norm (nicolasJShiftNumeratorFilled u z) <=
      5 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs0 : 1 < s0.re := by
    dsimp [s0]
    linarith
  have hs1 : 1 < s1.re := by
    dsimp [s1, s0]
    linarith
  have hDen1 : (1 / 4 : Real) < s1.re - 1 := by
    dsimp [s1, s0]
    linarith
  have hShiftRaw := norm_nicolasPsiMellinTailContinuationFilled_le hs1
  have hShiftNumerator : (3 : Real) ^ (1 - s1.re) <=
      (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    dsimp [s1, s0]
    linarith
  have hShiftPowerNonneg : 0 <= (3 : Real) ^ (1 - s1.re) :=
    Real.rpow_nonneg (by norm_num) _
  have hShiftFraction : (3 : Real) ^ (1 - s1.re) / (s1.re - 1) <=
      4 * (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    calc
      (3 : Real) ^ (1 - s1.re) / (s1.re - 1) <=
          (3 : Real) ^ (1 - s1.re) / (1 / 4 : Real) :=
        div_le_div_of_nonneg_left hShiftPowerNonneg (by norm_num) hDen1.le
      _ = 4 * (3 : Real) ^ (1 - s1.re) := by ring
      _ <= 4 * (3 : Real) ^ (-u + (3 / 4 : Real)) :=
        mul_le_mul_of_nonneg_left hShiftNumerator (by norm_num)
  have hShift : norm (nicolasPsiMellinTailContinuationFilled s1) <=
      4 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    calc
      norm (nicolasPsiMellinTailContinuationFilled s1) <=
          (Real.log 4 + 5) *
            ((3 : Real) ^ (1 - s1.re) / (s1.re - 1)) := hShiftRaw
      _ <= (Real.log 4 + 5) *
          (4 * (3 : Real) ^ (-u + (3 / 4 : Real))) :=
        mul_le_mul_of_nonneg_left hShiftFraction (by positivity)
      _ = 4 * (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) := by ring
  have hBaseRaw := norm_nicolasPsiMellinTailContinuationFilled_le hs0
  have hBase : norm (nicolasPsiMellinTailContinuationFilled s0) <=
      (Real.log 4 + 5) * (3 : Real) ^ (-u) := by
    have hPowNonneg : 0 <= (3 : Real) ^ (-u) :=
      Real.rpow_nonneg (by norm_num) _
    have hS0Exponent : 1 - s0.re = -u := by
      dsimp [s0]
      ring
    have hS0Denominator : s0.re - 1 = u := by
      dsimp [s0]
      ring
    rw [hS0Exponent, hS0Denominator] at hBaseRaw
    calc
      norm (nicolasPsiMellinTailContinuationFilled s0) <=
          (Real.log 4 + 5) * ((3 : Real) ^ (-u) / u) := hBaseRaw
      _ <= (Real.log 4 + 5) * ((3 : Real) ^ (-u) / 1) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left hPowNonneg zero_lt_one hu.le)
          (by positivity)
      _ = (Real.log 4 + 5) * (3 : Real) ^ (-u) := by ring
  have hPowerNorm : norm ((3 : Complex) ^ z) =
      (3 : Real) ^ z.re := by
    change norm (((3 : Real) : Complex) ^ z) = (3 : Real) ^ z.re
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
  have hPowerProduct : norm ((3 : Complex) ^ z *
      nicolasPsiMellinTailContinuationFilled s0) <=
      (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    rw [norm_mul, hPowerNorm]
    calc
      (3 : Real) ^ z.re *
          norm (nicolasPsiMellinTailContinuationFilled s0) <=
          (3 : Real) ^ z.re *
            ((Real.log 4 + 5) * (3 : Real) ^ (-u)) :=
        mul_le_mul_of_nonneg_left hBase
          (Real.rpow_nonneg (by norm_num) _)
      _ = (Real.log 4 + 5) *
          ((3 : Real) ^ z.re * (3 : Real) ^ (-u)) := by ring
      _ = (Real.log 4 + 5) * (3 : Real) ^ (z.re + (-u)) := by
        rw [Real.rpow_add (by norm_num : (0 : Real) < 3)]
      _ = (Real.log 4 + 5) * (3 : Real) ^ (z.re - u) := by
        congr 2
      _ <= (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith
  unfold nicolasJShiftNumeratorFilled
  change norm (nicolasPsiMellinTailContinuationFilled s1 -
      (3 : Complex) ^ z * nicolasPsiMellinTailContinuationFilled s0) <= _
  calc
    norm (nicolasPsiMellinTailContinuationFilled s1 -
        (3 : Complex) ^ z * nicolasPsiMellinTailContinuationFilled s0) <=
        norm (nicolasPsiMellinTailContinuationFilled s1) +
          norm ((3 : Complex) ^ z *
            nicolasPsiMellinTailContinuationFilled s0) := norm_sub_le _ _
    _ <= 4 * (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) +
        (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) :=
      add_le_add hShift hPowerProduct
    _ = 5 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by ring

def nicolasJLargeMajorantAtDistance (d u : Real) : Real :=
  (5 / d) * (Real.log 4 + 5) * (u + 1) *
    (3 : Real) ^ (-u + (3 / 4 : Real))

theorem nicolasJLargeMajorantAtDistance_integrableOn
    {d : Real} (hd : 0 < d) :
    IntegrableOn (nicolasJLargeMajorantAtDistance d) (Ioi (1 : Real)) := by
  have hScaled := nicolasJLargeMajorantHalf_integrableOn.const_mul
    (3 / (4 * d))
  apply hScaled.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  unfold nicolasJLargeMajorantAtDistance nicolasJLargeMajorantHalf
  field_simp [hd.ne']
  ring

theorem norm_nicolasJMellinShiftIntegrandFilled_le_of_re_le_of_norm_ge
    {d u : Real} (hd : 0 < d) (hu : 1 < u) {z : Complex}
    (hzRe : z.re <= (3 / 4 : Real)) (hzNorm : d <= norm z) :
    norm (nicolasJMellinShiftIntegrandFilled z u) <=
      nicolasJLargeMajorantAtDistance d u := by
  have hzNe : Not (z = 0) := by
    intro hEq
    rw [hEq, norm_zero] at hzNorm
    linarith
  have hNumerator :=
    norm_nicolasJShiftNumeratorFilled_le_of_re_le_threeQuarter hu hzRe
  have hInv : norm (Inv.inv z) <= 1 / d := by
    rw [norm_inv]
    simpa [one_div] using one_div_le_one_div_of_le hd hzNorm
  have huPos : 0 < u + 1 := by linarith
  unfold nicolasJMellinShiftIntegrandFilled
  rw [dslope_of_ne _ hzNe]
  unfold slope
  rw [nicolasJShiftNumeratorFilled_zero]
  simp only [smul_eq_mul, vsub_eq_sub, sub_zero]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos huPos,
    norm_mul]
  calc
    (u + 1) * (norm (Inv.inv z) *
        norm (nicolasJShiftNumeratorFilled u z)) <=
        (u + 1) * ((1 / d) *
          (5 * (Real.log 4 + 5) *
            (3 : Real) ^ (-u + (3 / 4 : Real)))) := by
      apply mul_le_mul_of_nonneg_left _ huPos.le
      exact mul_le_mul hInv hNumerator (norm_nonneg _)
        (by positivity)
    _ = nicolasJLargeMajorantAtDistance d u := by
      unfold nicolasJLargeMajorantAtDistance
      field_simp [hd.ne']

theorem nicolasJShiftedComplexContinuationFilledLarge_analyticAt_of_ball
    {center : Complex} {R d : Real} (hRPos : 0 < R) (hd : 0 < d)
    (hGeometry : forall z : Complex,
      Membership.mem (Metric.ball center R) z ->
        And (z.re <= (3 / 4 : Real)) (d <= norm z)) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledLarge
      center := by
  have hPointData : forall u : Real, 1 < u ->
      forall z : Complex,
        Membership.mem (Metric.closedBall center (R / 2)) z ->
          And (Not (z = 0))
            (And (Not ((((u + 1 : Real) : Complex) - z) = 0))
              (Not (nicolasZetaPoleFactor
                (((u + 1 : Real) : Complex) - z) = 0))) := by
    intro u hu z hz
    have hzBall : Membership.mem (Metric.ball center R) z := by
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have hzGeometry := hGeometry z hzBall
    have hzNe : Not (z = 0) := by
      intro hEq
      rw [hEq, norm_zero] at hzGeometry
      linarith
    have hsRe : 1 < ((((u + 1 : Real) : Complex) - z).re) := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      linarith [hzGeometry.1]
    have hsZero : Not ((((u + 1 : Real) : Complex) - z) = 0) := by
      intro hEq
      rw [hEq] at hsRe
      norm_num at hsRe
    have hsOne : Not ((((u + 1 : Real) : Complex) - z) = 1) := by
      intro hEq
      rw [hEq] at hsRe
      norm_num at hsRe
    have hZeta : Not (riemannZeta
        (((u + 1 : Real) : Complex) - z) = 0) :=
      riemannZeta_ne_zero_of_one_lt_re hsRe
    have hFactor : Not (nicolasZetaPoleFactor
        (((u + 1 : Real) : Complex) - z) = 0) :=
      nicolasZetaPoleFactor_ne_zero_of_zeta_ne_zero hsOne hZeta
    exact And.intro hzNe (And.intro hsZero hFactor)
  have hKernelBound : forall u : Real, 1 < u ->
      forall z : Complex,
        Membership.mem (Metric.closedBall center (R / 2)) z ->
          norm (nicolasJMellinShiftIntegrandFilled z u) <=
            nicolasJLargeMajorantAtDistance d u := by
    intro u hu z hz
    have hzBall : Membership.mem (Metric.ball center R) z := by
      rw [Metric.mem_closedBall] at hz
      rw [Metric.mem_ball]
      linarith
    have hzGeometry := hGeometry z hzBall
    exact norm_nicolasJMellinShiftIntegrandFilled_le_of_re_le_of_norm_ge
      hd hu hzGeometry.1 hzGeometry.2
  have hContinuousU : forall z : Complex,
      Membership.mem (Metric.closedBall center (R / 2)) z ->
        ContinuousOn (fun u : Real =>
          nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
    intro z hz u hu
    have hData := hPointData u (mem_Ioi.mp hu) z hz
    have hJoint := nicolasJMellinShiftIntegrandFilled_joint_continuousAt
      (by linarith [mem_Ioi.mp hu] : 0 <= u)
      hData.1 hData.2.1 hData.2.2
    have hEmbed : ContinuousAt (fun v : Real => (v, z)) u := by
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    have hAt : ContinuousAt (fun v : Real =>
        nicolasJMellinShiftIntegrandFilled z v) u := by
      simpa [Function.comp_def] using hComp
    exact hAt.continuousWithinAt
  have hAnalytic : forall u : Real, 1 < u ->
      forall z : Complex,
        Membership.mem (Metric.closedBall center (R / 2)) z ->
          AnalyticAt Complex (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z := by
    intro u hu z hz
    have hData := hPointData u hu z hz
    exact
      nicolasJMellinShiftIntegrandFilled_analyticAt_of_ne_zero_of_factor_ne_zero
        (by linarith [hu] : 0 <= u) hData.1 hData.2.1 hData.2.2
  have hDerivativeMeasurable : forall z : Complex,
      Membership.mem (Metric.ball center (R / 4)) z ->
        AEStronglyMeasurable (fun u : Real =>
          deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z)
          (volume.restrict (Ioi (1 : Real))) := by
    intro z hz
    let slopeSeq : Nat -> Real -> Complex := fun n : Nat => fun u : Real =>
      slope (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u)
        z (z + nicolasCompactStripDerivativeStep R n)
    have hzDist : dist z center < R / 4 := by
      simpa [Metric.mem_ball] using hz
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      rw [Metric.mem_closedBall]
      linarith
    have hShiftClosed : forall n : Nat,
        Membership.mem (Metric.closedBall center (R / 2))
          (z + nicolasCompactStripDerivativeStep R n) := by
      intro n
      rw [Metric.mem_closedBall]
      calc
        dist (z + nicolasCompactStripDerivativeStep R n) center <=
            dist (z + nicolasCompactStripDerivativeStep R n) z +
              dist z center := dist_triangle _ z _
        _ = norm (nicolasCompactStripDerivativeStep R n) +
              dist z center := by rw [dist_eq_norm]; simp
        _ <= R / 8 + R / 4 :=
          (add_lt_add_of_le_of_lt
            (norm_nicolasCompactStripDerivativeStep_le hRPos n) hzDist).le
        _ <= R / 2 := by linarith
    have hMeas : forall n : Nat, AEMeasurable (slopeSeq n)
        (volume.restrict (Ioi (1 : Real))) := by
      intro n
      have hShift := hContinuousU _ (hShiftClosed n)
      have hBase := hContinuousU z hzClosed
      have hShiftMeas : AEStronglyMeasurable
          (fun u : Real => nicolasJMellinShiftIntegrandFilled
            (z + nicolasCompactStripDerivativeStep R n) u)
          (volume.restrict (Ioi (1 : Real))) :=
        hShift.aestronglyMeasurable measurableSet_Ioi
      have hBaseMeas : AEStronglyMeasurable
          (fun u : Real => nicolasJMellinShiftIntegrandFilled z u)
          (volume.restrict (Ioi (1 : Real))) :=
        hBase.aestronglyMeasurable measurableSet_Ioi
      have hEq : slopeSeq n = fun u : Real =>
          Inv.inv ((z + nicolasCompactStripDerivativeStep R n) - z) *
            (nicolasJMellinShiftIntegrandFilled
                (z + nicolasCompactStripDerivativeStep R n) u -
              nicolasJMellinShiftIntegrandFilled z u) := by
        funext u
        dsimp [slopeSeq]
        unfold slope
        simp only [smul_eq_mul, vsub_eq_sub]
      rw [hEq]
      exact ((hShiftMeas.sub hBaseMeas).const_mul
        (Inv.inv ((z + nicolasCompactStripDerivativeStep R n) - z))).aemeasurable
    have hStepWithin : Tendsto (nicolasCompactStripDerivativeStep R) atTop
        (nhdsWithin (0 : Complex) (Set.compl {(0 : Complex)})) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact And.intro (nicolasCompactStripDerivativeStep_tendsto_zero R)
        (Eventually.of_forall (fun n : Nat =>
          Set.mem_compl_singleton_iff.mpr
            (nicolasCompactStripDerivativeStep_ne_zero hRPos n)))
    have hTendsto : Filter.Eventually
        (fun u : Real => Tendsto (fun n : Nat => slopeSeq n u) atTop
          (nhds (deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z)))
        (ae (volume.restrict (Ioi (1 : Real)))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hSlope := (hAnalytic u hu z hzClosed).differentiableAt.hasDerivAt
        |>.tendsto_slope_zero.comp hStepWithin
      change Tendsto (fun n : Nat =>
        Inv.inv (nicolasCompactStripDerivativeStep R n) *
          (nicolasJMellinShiftIntegrandFilled
              (z + nicolasCompactStripDerivativeStep R n) u -
            nicolasJMellinShiftIntegrandFilled z u))
        atTop (nhds (deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)) at hSlope
      dsimp [slopeSeq]
      unfold slope
      simp only [smul_eq_mul, vsub_eq_sub, add_sub_cancel_left]
      exact hSlope
    exact (aemeasurable_of_tendsto_metrizable_ae'
      hMeas hTendsto).aestronglyMeasurable
  have hDerivativeBound : forall u : Real, 1 < u ->
      forall z : Complex,
        Membership.mem (Metric.ball center (R / 4)) z ->
          norm (deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z) <=
              (8 / R) * nicolasJLargeMajorantAtDistance d u := by
    intro u hu z hz
    let f : Complex -> Complex := fun w =>
      nicolasJMellinShiftIntegrandFilled w u
    let r : Real := R / 4
    have hzDist : dist z center < R / 4 := by
      simpa [Metric.mem_ball] using hz
    have hSmallSubset : Metric.ball z r <=
        Metric.closedBall center (R / 2) := by
      intro w hw
      rw [Metric.mem_ball] at hw
      rw [Metric.mem_closedBall]
      calc
        dist w center <= dist w z + dist z center := dist_triangle _ z _
        _ <= R / 4 + R / 4 := by
          dsimp [r] at hw
          exact (add_lt_add hw hzDist).le
        _ <= R / 2 := by linarith
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      apply hSmallSubset
      exact Metric.mem_ball_self (by dsimp [r]; linarith)
    have hDiff : DifferentiableOn Complex f (Metric.ball z r) := by
      intro w hw
      exact (hAnalytic u hu w (hSmallSubset hw)).differentiableAt.differentiableWithinAt
    have hMaps : MapsTo f (Metric.ball z r)
        (Metric.closedBall (f z)
          (2 * nicolasJLargeMajorantAtDistance d u)) := by
      intro w hw
      have hwBound := hKernelBound u hu w (hSmallSubset hw)
      have hzBound := hKernelBound u hu z hzClosed
      rw [Metric.mem_closedBall]
      calc
        dist (f w) (f z) <= norm (f w) + norm (f z) := by
          simpa [dist_eq_norm] using norm_sub_le (f w) (f z)
        _ <= nicolasJLargeMajorantAtDistance d u +
            nicolasJLargeMajorantAtDistance d u :=
          add_le_add hwBound hzBound
        _ = 2 * nicolasJLargeMajorantAtDistance d u := by ring
    have hCauchy := Complex.norm_deriv_le_div_of_mapsTo_ball
      hDiff hMaps (by dsimp [r]; linarith)
    change norm (deriv f z) <=
      (8 / R) * nicolasJLargeMajorantAtDistance d u
    calc
      norm (deriv f z) <=
          (2 * nicolasJLargeMajorantAtDistance d u) / r := hCauchy
      _ = (8 / R) * nicolasJLargeMajorantAtDistance d u := by
        dsimp [r]
        field_simp [hRPos.ne']
        ring
  let s : Set Complex := Metric.ball center (R / 4)
  have hHasDeriv : forall z : Complex, Membership.mem s z ->
      HasDerivAt nicolasJShiftedComplexContinuationFilledLarge
        (integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
          deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z)) z := by
    intro z hz
    let F : Complex -> Real -> Complex := fun w => fun u =>
      nicolasJMellinShiftIntegrandFilled w u
    let F' : Complex -> Real -> Complex := fun w => fun u =>
      deriv (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w
    have hsNhd : Membership.mem (nhds z) s :=
      Metric.isOpen_ball.mem_nhds hz
    have hFMeas : Filter.Eventually
        (fun w : Complex => AEStronglyMeasurable (F w)
          (volume.restrict (Ioi (1 : Real)))) (nhds z) := by
      filter_upwards [hsNhd] with w hw
      have hwClosed : Membership.mem
          (Metric.closedBall center (R / 2)) w := by
        rw [Metric.mem_closedBall]
        have hwDist : dist w center < R / 4 := by
          simpa [s, Metric.mem_ball] using hw
        linarith
      dsimp [F]
      exact (hContinuousU w hwClosed).aestronglyMeasurable measurableSet_Ioi
    have hzClosed : Membership.mem
        (Metric.closedBall center (R / 2)) z := by
      rw [Metric.mem_closedBall]
      have hzDist : dist z center < R / 4 := by
        simpa [s, Metric.mem_ball] using hz
      linarith
    have hFInt : Integrable (F z)
        (volume.restrict (Ioi (1 : Real))) := by
      apply Integrable.mono'
        (nicolasJLargeMajorantAtDistance_integrableOn hd)
        ((hContinuousU z hzClosed).aestronglyMeasurable measurableSet_Ioi)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hKernelBound u hu z hzClosed
    have hF'Meas : AEStronglyMeasurable (F' z)
        (volume.restrict (Ioi (1 : Real))) := by
      dsimp [F']
      exact hDerivativeMeasurable z hz
    have hBound : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          norm (F' w u) <=
            (8 / R) * nicolasJLargeMajorantAtDistance d u)
        (ae (volume.restrict (Ioi (1 : Real)))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro w hw
      exact hDerivativeBound u hu w hw
    have hBoundInt : IntegrableOn
        (fun u : Real => (8 / R) * nicolasJLargeMajorantAtDistance d u)
        (Ioi (1 : Real)) :=
      (nicolasJLargeMajorantAtDistance_integrableOn hd).const_mul (8 / R)
    have hDiff : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          HasDerivAt (fun v : Complex => F v u) (F' w u) w)
        (ae (volume.restrict (Ioi (1 : Real)))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      intro w hw
      have hwClosed : Membership.mem
          (Metric.closedBall center (R / 2)) w := by
        rw [Metric.mem_closedBall]
        have hwDist : dist w center < R / 4 := by
          simpa [s, Metric.mem_ball] using hw
        linarith
      dsimp [F, F']
      exact (hAnalytic u hu w hwClosed).differentiableAt.hasDerivAt
    have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F')
      (bound := fun u : Real =>
        (8 / R) * nicolasJLargeMajorantAtDistance d u)
      hsNhd hFMeas hFInt hF'Meas hBound hBoundInt hDiff
    unfold nicolasJShiftedComplexContinuationFilledLarge
    simpa [F, F'] using hMain.2
  have hDiffOn : DifferentiableOn Complex
      nicolasJShiftedComplexContinuationFilledLarge s := by
    intro z hz
    exact (hHasDeriv z hz).differentiableAt.differentiableWithinAt
  apply hDiffOn.analyticAt
  dsimp [s]
  exact Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self (by linarith : 0 < R / 4))

theorem nicolasJMellinShiftIntegrandFilled_integrableOn_large_of_geometry
    {d : Real} (hd : 0 < d) {z : Complex}
    (hzRe : z.re <= (3 / 4 : Real)) (hzNorm : d <= norm z) :
    IntegrableOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
  have hzNe : Not (z = 0) := by
    intro hEq
    rw [hEq, norm_zero] at hzNorm
    linarith
  have hContinuous : ContinuousOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
    intro u hu
    have hsRe : 1 < ((((u + 1 : Real) : Complex) - z).re) := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      linarith [hzRe, mem_Ioi.mp hu]
    have hsZero : Not ((((u + 1 : Real) : Complex) - z) = 0) := by
      intro hEq
      rw [hEq] at hsRe
      norm_num at hsRe
    have hsOne : Not ((((u + 1 : Real) : Complex) - z) = 1) := by
      intro hEq
      rw [hEq] at hsRe
      norm_num at hsRe
    have hZeta : Not (riemannZeta
        (((u + 1 : Real) : Complex) - z) = 0) :=
      riemannZeta_ne_zero_of_one_lt_re hsRe
    have hFactor : Not (nicolasZetaPoleFactor
        (((u + 1 : Real) : Complex) - z) = 0) :=
      nicolasZetaPoleFactor_ne_zero_of_zeta_ne_zero hsOne hZeta
    have hJoint := nicolasJMellinShiftIntegrandFilled_joint_continuousAt
      (by linarith [mem_Ioi.mp hu] : 0 <= u) hzNe hsZero hFactor
    have hEmbed : ContinuousAt (fun v : Real => (v, z)) u := by
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    have hAt : ContinuousAt (fun v : Real =>
        nicolasJMellinShiftIntegrandFilled z v) u := by
      simpa [Function.comp_def] using hComp
    exact hAt.continuousWithinAt
  apply Integrable.mono'
    (nicolasJLargeMajorantAtDistance_integrableOn hd)
    (hContinuous.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact norm_nicolasJMellinShiftIntegrandFilled_le_of_re_le_of_norm_ge
    hd hu hzRe hzNorm

theorem exists_nicolasRightmostRayLargeGeometry
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {eps : Real} (hEps : 0 < eps) :
    Exists fun d : Real => Exists fun R : Real =>
      And (0 < d) (And (0 < R)
        (forall z : Complex,
          Membership.mem
            (Metric.ball ((1 - rho) - (eps : Complex)) R) z ->
            And (z.re <= (3 / 4 : Real)) (d <= norm z))) := by
  let center : Complex := (1 - rho) - (eps : Complex)
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOne
  have hCenterIm : center.im = -rho.im := by
    dsimp [center]
    simp
  have hCenterNe : Not (center = 0) := by
    intro hEq
    have hZeroIm : center.im = 0 := by rw [hEq]; simp
    exact hIm (neg_eq_zero.mp (hCenterIm.symm.trans hZeroIm))
  have hCenterNorm : 0 < norm center := norm_pos_iff.mpr hCenterNe
  have hCenterRe : center.re = 1 - rho.re - eps := by
    dsimp [center]
  have hReMargin : 0 < (3 / 4 : Real) - center.re := by
    rw [hCenterRe]
    linarith
  let d : Real := norm center / 2
  let R : Real := min (norm center / 2)
    (((3 / 4 : Real) - center.re) / 2)
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hRPos : 0 < R := by
    dsimp [R]
    exact lt_min (by positivity) (by positivity)
  have hGeometry : forall z : Complex,
      Membership.mem (Metric.ball center R) z ->
        And (z.re <= (3 / 4 : Real)) (d <= norm z) := by
    intro z hz
    have hzDist : dist z center < R := by
      simpa [Metric.mem_ball] using hz
    have hDistNorm : dist z center < norm center / 2 :=
      lt_of_lt_of_le hzDist (by
        dsimp [R]
        exact min_le_left _ _)
    have hDistRe : dist z center <
        ((3 / 4 : Real) - center.re) / 2 :=
      lt_of_lt_of_le hzDist (by
        dsimp [R]
        exact min_le_right _ _)
    have hReDiff : z.re - center.re <= dist z center := by
      calc
        z.re - center.re <= abs (z.re - center.re) := le_abs_self _
        _ = abs ((z - center).re) :=
          congrArg abs (Complex.sub_re z center).symm
        _ <= norm (z - center) := Complex.abs_re_le_norm _
        _ = dist z center := by rw [dist_eq_norm]
    have hTriangle : norm center <= dist center z + norm z := by
      have h := dist_triangle center z 0
      simpa [dist_zero_right] using h
    have hNorm : d <= norm z := by
      dsimp [d]
      rw [dist_comm center z] at hTriangle
      linarith
    exact And.intro (by linarith) hNorm
  exact Exists.intro d (Exists.intro R
    (And.intro hd (And.intro hRPos (by simpa [center] using hGeometry))))

theorem nicolasJShiftedComplexContinuationFilledLarge_analyticAt_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledLarge
      ((1 - rho) - (eps : Complex)) := by
  choose d R hd hRPos hGeometry using
    exists_nicolasRightmostRayLargeGeometry hZero hHalf hOne hEps
  exact nicolasJShiftedComplexContinuationFilledLarge_analyticAt_of_ball
    hRPos hd hGeometry

theorem eventually_nicolasJMellinShiftIntegrandFilled_integrableOn_compact_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    Filter.Eventually (fun z : Complex =>
      IntegrableOn (fun u : Real =>
        nicolasJMellinShiftIntegrandFilled z u) (Ioc (0 : Real) 1))
      (nhds ((1 - rho) - (eps : Complex))) := by
  let center : Complex := (1 - rho) - (eps : Complex)
  choose R hRPos hGood using
    exists_nicolasRightmostRayCompactTubeRadius
      hZero hHalf hOne hRay hEps
  have hBall : Membership.mem (nhds center)
      (Metric.ball center (R / 2)) :=
    Metric.ball_mem_nhds _ (by linarith)
  filter_upwards [hBall] with z hz
  have hzClosed : Membership.mem
      (Metric.closedBall center (R / 2)) z :=
    Metric.ball_subset_closedBall hz
  have hzBall : Membership.mem (Metric.ball center R) z := by
    rw [Metric.mem_closedBall] at hzClosed
    rw [Metric.mem_ball]
    linarith
  have hzGood := hGood z (by simpa [center] using hzBall)
  have hContinuous : ContinuousOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Icc (0 : Real) 1) := by
    intro u hu
    have hJoint := nicolasJMellinShiftIntegrandFilled_joint_continuousAt
      hu.1 hzGood.1 (hzGood.2 u hu).1 (hzGood.2 u hu).2
    have hEmbed : ContinuousAt (fun v : Real => (v, z)) u := by
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    have hAt : ContinuousAt (fun v : Real =>
        nicolasJMellinShiftIntegrandFilled z v) u := by
      simpa [Function.comp_def] using hComp
    exact hAt.continuousWithinAt
  have hInt : IntegrableOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Icc (0 : Real) 1) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact hContinuous
  exact hInt.mono_set Ioc_subset_Icc_self

theorem eventually_nicolasJMellinShiftIntegrandFilled_integrableOn_large_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    {eps : Real} (hEps : 0 < eps) :
    Filter.Eventually (fun z : Complex =>
      IntegrableOn (fun u : Real =>
        nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)))
      (nhds ((1 - rho) - (eps : Complex))) := by
  let center : Complex := (1 - rho) - (eps : Complex)
  choose d R hd hRPos hGeometry using
    exists_nicolasRightmostRayLargeGeometry hZero hHalf hOne hEps
  have hBall : Membership.mem (nhds center) (Metric.ball center R) :=
    Metric.ball_mem_nhds _ hRPos
  filter_upwards [hBall] with z hz
  have hzGeometry := hGeometry z (by simpa [center] using hz)
  exact nicolasJMellinShiftIntegrandFilled_integrableOn_large_of_geometry
    hd hzGeometry.1 hzGeometry.2

theorem eventually_nicolasJShiftedComplexContinuationFilled_eq_compact_add_large_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    Filter.EventuallyEq (nhds ((1 - rho) - (eps : Complex)))
      nicolasJShiftedComplexContinuationFilled
      (fun z : Complex =>
        nicolasJShiftedComplexContinuationFilledCompact z +
          nicolasJShiftedComplexContinuationFilledLarge z) := by
  have hCompact :=
    eventually_nicolasJMellinShiftIntegrandFilled_integrableOn_compact_rightmostRay
      hZero hHalf hOne hRay hEps
  have hLarge :=
    eventually_nicolasJMellinShiftIntegrandFilled_integrableOn_large_rightmostRay
      hZero hHalf hOne hEps
  filter_upwards [hCompact, hLarge] with z hCompactInt hLargeInt
  unfold nicolasJShiftedComplexContinuationFilled
    nicolasJShiftedComplexContinuationFilledCompact
    nicolasJShiftedComplexContinuationFilledLarge
  rw [<- Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : Real) <= 1),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
  . exact hCompactInt
  . exact hLargeInt

theorem nicolasJShiftedComplexContinuationFilled_analyticAt_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOne : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps : Real} (hEps : 0 < eps) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilled
      ((1 - rho) - (eps : Complex)) := by
  have hCompact :=
    nicolasJShiftedComplexContinuationFilledCompact_analyticAt_rightmostRay
      hZero hHalf hOne hRay hEps
  have hLarge :=
    nicolasJShiftedComplexContinuationFilledLarge_analyticAt_rightmostRay
      hZero hHalf hOne hEps
  have hSum : AnalyticAt Complex (fun z : Complex =>
      nicolasJShiftedComplexContinuationFilledCompact z +
        nicolasJShiftedComplexContinuationFilledLarge z)
      ((1 - rho) - (eps : Complex)) := hCompact.add hLarge
  have hEq :=
    eventually_nicolasJShiftedComplexContinuationFilled_eq_compact_add_large_rightmostRay
      hZero hHalf hOne hRay hEps
  exact (analyticAt_congr hEq).mpr hSum

end

end Robin1984

end
section

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal Topology

noncomputable section

theorem norm_intervalIntegral_inv_smul_sub_le_of_intervalIntegrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [CompleteSpace E]
    {f : Real -> E} {a b delta : Real} {V : E}
    (hf : IntervalIntegrable f volume a b) (ha : 0 < a) (hb : 0 < b)
    (hDelta : 0 <= delta)
    (hBound : forall x : Real, Membership.mem (uIoc a b) x ->
      norm (f x - V) <= delta) :
    norm (intervalIntegral
        (fun x : Real => HSMul.hSMul (Inv.inv x) (f x)) a b volume -
      HSMul.hSMul (Real.log (b / a)) V) <=
      delta * abs (Real.log (b / a)) := by
  have hSubset : uIcc a b <= Ioi (0 : Real) := by
    simp [uIcc, Icc_subset_Ioi_iff, ha, hb]
  have hInv : ContinuousOn (fun x : Real => Inv.inv x) (uIcc a b) := by
    intro x hx
    exact (NormedField.continuousAt_inv.mpr
      (ne_of_gt (hSubset hx))).continuousWithinAt
  have hWeighted : IntervalIntegrable
      (fun x : Real => HSMul.hSMul (Inv.inv x) (f x)) volume a b :=
    hf.continuousOn_smul hInv
  have hConst : IntervalIntegrable
      (fun x : Real => HSMul.hSMul (Inv.inv x) V) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact hInv.smul continuousOn_const
  have hReal : IntervalIntegrable
      (fun x : Real => Inv.inv x * delta) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact hInv.mul continuousOn_const
  calc
    norm (intervalIntegral
          (fun x : Real => HSMul.hSMul (Inv.inv x) (f x)) a b volume -
        HSMul.hSMul (Real.log (b / a)) V) =
        norm (intervalIntegral
          (fun x : Real => HSMul.hSMul (Inv.inv x) (f x - V))
          a b volume) := by
      congr 1
      have hConstIntegral : HSMul.hSMul (Real.log (b / a)) V =
          intervalIntegral
            (fun x : Real => HSMul.hSMul (Inv.inv x) V) a b volume := by
        rw [intervalIntegral.integral_smul_const,
          integral_inv_of_pos ha hb]
      rw [hConstIntegral, <- intervalIntegral.integral_sub hWeighted hConst]
      congr 1
      funext x
      exact (smul_sub _ _ _).symm
    _ <= abs (intervalIntegral
        (fun x : Real => Inv.inv x * delta) a b volume) := by
      apply intervalIntegral.norm_integral_le_abs_of_norm_le
      . filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
        have hxPos : 0 < x :=
          lt_of_lt_of_le (lt_min ha hb) (uIoc_subset_uIcc hx).1
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxPos)]
        exact mul_le_mul_of_nonneg_left (hBound x hx)
          (inv_nonneg.mpr hxPos.le)
      . exact hReal
    _ = delta * abs (Real.log (b / a)) := by
      simp_rw [mul_comm]
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha hb]
      rw [abs_mul, abs_of_nonneg hDelta]

def nicolasRightmostRayPoint (rho : Complex) (eps : Real) : Complex :=
  (1 - rho) - (eps : Complex)

def nicolasJRightmostRayTranslatedScaledKernel
    (rho : Complex) (eps v : Real) : Complex :=
  (v : Complex) * nicolasJMellinShiftIntegrand
    (nicolasRightmostRayPoint rho eps) (v - eps)

theorem nicolasJMellinShiftIntegrandFilled_eq_raw_rightmostRay
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps u : Real} (hEps : 0 < eps) (hU : 0 < u) :
    nicolasJMellinShiftIntegrandFilled
        (nicolasRightmostRayPoint rho eps) u =
      nicolasJMellinShiftIntegrand
        (nicolasRightmostRayPoint rho eps) u := by
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOneRe
  have hzZero : Not (nicolasRightmostRayPoint rho eps = 0) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    unfold nicolasRightmostRayPoint at hEqIm
    simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im,
      Complex.zero_im] at hEqIm
    apply hIm
    linarith
  let s : Complex := rho + ((eps + u : Real) : Complex)
  have hShift :
      (((u + 1 : Real) : Complex) -
          nicolasRightmostRayPoint rho eps) = s := by
    dsimp [s, nicolasRightmostRayPoint]
    push_cast
    ring
  have hsIm : s.im = rho.im := by
    dsimp [s]
    simp
  have hsZero : Not (s = 0) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    rw [hsIm, Complex.zero_im] at hEqIm
    exact hIm hEqIm
  have hsOne : Not (s = 1) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    rw [hsIm, Complex.one_im] at hEqIm
    exact hIm hEqIm
  have hZeta : Not (riemannZeta s = 0) := by
    dsimp [s]
    exact hRay (eps + u) (by linarith)
  have hBaseRe : 1 < (((u + 1 : Real) : Complex)).re := by
    simp
    linarith
  have hBaseEq :=
    nicolasPsiMellinTailContinuationFilled_eq_raw_of_one_lt_re hBaseRe
  have hShiftEq :=
    nicolasPsiMellinTailContinuationFilled_eq_raw hsZero hsOne hZeta
  unfold nicolasJMellinShiftIntegrandFilled
  rw [dslope_of_ne _ hzZero]
  unfold slope
  rw [nicolasJShiftNumeratorFilled_zero]
  unfold nicolasJShiftNumeratorFilled nicolasJMellinShiftIntegrand
  rw [hBaseEq, hShift, hShiftEq]
  simp only [sub_zero, smul_eq_mul, vsub_eq_sub]
  field_simp [hzZero]

def nicolasJRightmostRayTranslatedScaledKernelFilled
    (rho : Complex) (eps v : Real) : Complex :=
  (v : Complex) * nicolasJMellinShiftIntegrandFilled
    (nicolasRightmostRayPoint rho eps) (v - eps)

theorem nicolasJRightmostRayTranslatedScaledKernelFilled_eq_raw
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps v : Real} (hEps : 0 < eps) (hEpsV : eps < v) :
    nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v =
      nicolasJRightmostRayTranslatedScaledKernel rho eps v := by
  unfold nicolasJRightmostRayTranslatedScaledKernelFilled
    nicolasJRightmostRayTranslatedScaledKernel
  rw [nicolasJMellinShiftIntegrandFilled_eq_raw_rightmostRay
    hZero hHalf hOneRe hRay hEps (by linarith)]

theorem nicolasJRightmostRayTranslatedScaledKernel_tendsto
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1) :
    Exists fun d : Complex => And (Not (d = 0))
      (Tendsto (fun p : Prod Real Real =>
          nicolasJRightmostRayTranslatedScaledKernel rho p.1 p.2)
        (nhdsWithin ((0 : Real), (0 : Real))
          {p : Prod Real Real | And (0 < p.1) (p.1 < p.2)})
        (nhds d)) := by
  have hRhoZero : Not (rho = 0) := by
    intro hEq
    rw [hEq] at hHalf
    norm_num at hHalf
  have hRhoOne : Not (rho = 1) := by
    intro hEq
    rw [hEq] at hOneRe
    norm_num at hOneRe
  choose c hc hPole using
    nicolasPsiMellinTailContinuation_three_simplePoleLimit_Ioi
      hZero hRhoZero hRhoOne
  let D : Set (Prod Real Real) :=
    {p : Prod Real Real | And (0 < p.1) (p.1 < p.2)}
  let l : Filter (Prod Real Real) :=
    nhdsWithin ((0 : Real), (0 : Real)) D
  let u : Prod Real Real -> Real := fun p => p.2 - p.1
  let z : Prod Real Real -> Complex := fun p =>
    nicolasRightmostRayPoint rho p.1
  let z0 : Complex := 1 - rho
  have hFst : Tendsto (fun p : Prod Real Real => p.1) l (nhds 0) := by
    exact continuousAt_fst.tendsto.mono_left nhdsWithin_le_nhds
  have hSnd : Tendsto (fun p : Prod Real Real => p.2) l (nhds 0) := by
    exact continuousAt_snd.tendsto.mono_left nhdsWithin_le_nhds
  have hU : Tendsto u l (nhds 0) := by
    dsimp [u]
    simpa using hSnd.sub hFst
  have hSndPos : Filter.Eventually
      (fun p : Prod Real Real => 0 < p.2) l := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact hp.1.trans hp.2
  have hUPos : Filter.Eventually (fun p : Prod Real Real => 0 < u p) l := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    dsimp [u]
    linarith [hp.2]
  have hSndWithin : Tendsto (fun p : Prod Real Real => p.2) l
      (nhdsWithin 0 (Ioi (0 : Real))) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact And.intro hSnd hSndPos
  have hUWithin : Tendsto u l (nhdsWithin 0 (Ioi (0 : Real))) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact And.intro hU hUPos
  have hPoleComp : Tendsto (fun p : Prod Real Real =>
      (p.2 : Complex) *
        nicolasPsiMellinTailContinuation 3 (rho + (p.2 : Complex)))
      l (nhds c) := hPole.comp hSndWithin
  have hBaseArg : Tendsto (fun p : Prod Real Real =>
      (((u p + 1 : Real) : Complex))) l
      (nhdsWithin 1 (Set.compl {(1 : Complex)})) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    . have hCast : Tendsto (fun p : Prod Real Real => (u p : Complex))
          l (nhds 0) := Complex.continuous_ofReal.continuousAt.tendsto.comp hU
      simpa using hCast.add tendsto_const_nhds
    . filter_upwards [hUPos] with p hp
      apply Set.mem_compl_singleton_iff.mpr
      intro hEq
      have hRe := congrArg Complex.re hEq
      simp only [Complex.ofReal_re, Complex.one_re] at hRe
      linarith
  have hBaseTail : Tendsto (fun p : Prod Real Real =>
      nicolasPsiMellinTailContinuation 3
        (((u p + 1 : Real) : Complex))) l
      (nhds (-(logDeriv nicolasZetaPoleFactor 1 + 1) -
        nicolasPsiMellinStartup 3 1)) :=
    nicolasPsiMellinTailContinuation_three_tendsto_one.comp hBaseArg
  have hSndCast : Tendsto (fun p : Prod Real Real => (p.2 : Complex))
      l (nhds 0) := Complex.continuous_ofReal.continuousAt.tendsto.comp hSnd
  have hScaledBase : Tendsto (fun p : Prod Real Real =>
      (p.2 : Complex) * nicolasPsiMellinTailContinuation 3
        (((u p + 1 : Real) : Complex))) l (nhds 0) := by
    simpa using hSndCast.mul hBaseTail
  have hZ : Tendsto z l (nhds z0) := by
    have hFstCast : Tendsto (fun p : Prod Real Real => (p.1 : Complex))
        l (nhds 0) := Complex.continuous_ofReal.continuousAt.tendsto.comp hFst
    dsimp [z, z0, nicolasRightmostRayPoint]
    simpa using (tendsto_const_nhds.sub hFstCast)
  have hz0Ne : Not (z0 = 0) := by
    dsimp [z0]
    exact sub_ne_zero.mpr (Ne.symm hRhoOne)
  have hNumerator : Tendsto (fun p : Prod Real Real =>
      (((u p + 1 : Real) : Complex))) l (nhds 1) := by
    have hCast : Tendsto (fun p : Prod Real Real => (u p : Complex))
        l (nhds 0) := Complex.continuous_ofReal.continuousAt.tendsto.comp hU
    simpa using hCast.add tendsto_const_nhds
  have hPrefactor : Tendsto (fun p : Prod Real Real =>
      (((u p + 1 : Real) : Complex)) / z p) l (nhds (1 / z0)) :=
    hNumerator.div hZ hz0Ne
  have hPowerAt : Tendsto (fun p : Prod Real Real =>
      (3 : Complex) ^ (z p)) l (nhds ((3 : Complex) ^ z0)) := by
    have hContinuous : ContinuousAt (fun w : Complex =>
        (3 : Complex) ^ w) z0 := by
      fun_prop
    exact hContinuous.tendsto.comp hZ
  have hDifference : Tendsto (fun p : Prod Real Real =>
      (p.2 : Complex) *
          nicolasPsiMellinTailContinuation 3 (rho + (p.2 : Complex)) -
        (3 : Complex) ^ (z p) *
          ((p.2 : Complex) * nicolasPsiMellinTailContinuation 3
            (((u p + 1 : Real) : Complex)))) l (nhds c) := by
    simpa using hPoleComp.sub (hPowerAt.mul hScaledBase)
  let d : Complex := c / z0
  have hd : Not (d = 0) := div_ne_zero hc hz0Ne
  refine Exists.intro d (And.intro hd ?_)
  have hProduct := hPrefactor.mul hDifference
  convert hProduct using 1
  . funext p
    have hShift :
        ((((p.2 - p.1 + 1 : Real) : Complex) -
            nicolasRightmostRayPoint rho p.1)) =
          rho + (p.2 : Complex) := by
      unfold nicolasRightmostRayPoint
      push_cast
      ring
    unfold nicolasJRightmostRayTranslatedScaledKernel
      nicolasJMellinShiftIntegrand
    rw [hShift]
    dsimp [u, z, nicolasRightmostRayPoint]
    ring
  . dsimp [d]
    ring

theorem exists_nicolasRightmostRayScaledKernel_uniform
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1) :
    Exists fun d : Complex => Exists fun r : Real =>
      And (Not (d = 0))
        (And (0 < r) (And (r < 1 / 2)
          (forall eps v : Real, 0 < eps -> eps < v -> v <= r ->
            norm (nicolasJRightmostRayTranslatedScaledKernel rho eps v - d) <=
              norm d / 4))) := by
  choose d hd hLimit using
    nicolasJRightmostRayTranslatedScaledKernel_tendsto hZero hHalf hOneRe
  have hdNorm : 0 < norm d := norm_pos_iff.mpr hd
  have hClose : Filter.Eventually
      (fun p : Prod Real Real =>
        norm (nicolasJRightmostRayTranslatedScaledKernel rho p.1 p.2 - d) <
          norm d / 4)
      (nhdsWithin ((0 : Real), (0 : Real))
        {p : Prod Real Real | And (0 < p.1) (p.1 < p.2)}) := by
    have hBall := hLimit.eventually
      (Metric.ball_mem_nhds d (by positivity : 0 < norm d / 4))
    simpa [Metric.mem_ball, dist_eq_norm] using hBall
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hClose
  choose eta hEta hCloseEta using hClose
  let r : Real := min (eta / 2) (1 / 4)
  have hrPos : 0 < r := by
    dsimp [r]
    exact lt_min (by positivity) (by norm_num)
  have hrHalf : r < 1 / 2 := by
    dsimp [r]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hrEta : r < eta := by
    dsimp [r]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine Exists.intro d (Exists.intro r
    (And.intro hd (And.intro hrPos (And.intro hrHalf ?_))))
  intro eps v hEps hEpsV hVr
  have hVPos : 0 < v := hEps.trans hEpsV
  have hDist : dist (eps, v) ((0 : Real), (0 : Real)) < eta := by
    change max (dist eps 0) (dist v 0) < eta
    rw [max_lt_iff]
    constructor
    . rw [Real.dist_eq, sub_zero, abs_of_pos hEps]
      exact hEpsV.trans_le hVr |>.trans hrEta
    . rw [Real.dist_eq, sub_zero, abs_of_pos hVPos]
      exact hVr.trans_lt hrEta
  exact (hCloseEta hDist (And.intro hEps hEpsV)).le

theorem nicolasJRightmostRayTranslatedScaledKernelFilled_intervalIntegrable
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {eps r : Real} (hEps : 0 < eps) (hEpsR : eps < r)
    (hWidth : r - eps <= 1) :
    IntervalIntegrable
      (nicolasJRightmostRayTranslatedScaledKernelFilled rho eps)
      volume eps r := by
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOneRe
  have hzZero : Not (nicolasRightmostRayPoint rho eps = 0) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    unfold nicolasRightmostRayPoint at hEqIm
    simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im,
      Complex.zero_im] at hEqIm
    apply hIm
    linarith
  apply ContinuousOn.intervalIntegrable
  intro v hv
  have hvIcc : Membership.mem (Icc eps r) v := by
    simpa [uIcc, min_eq_left hEpsR.le, max_eq_right hEpsR.le] using hv
  have hU : 0 <= v - eps := by linarith [hvIcc.1]
  have hULe : v - eps <= 1 := by linarith [hvIcc.2]
  let s : Complex := rho + (v : Complex)
  have hsIm : s.im = rho.im := by
    dsimp [s]
    simp
  have hsZero : Not (s = 0) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    rw [hsIm, Complex.zero_im] at hEqIm
    exact hIm hEqIm
  have hsOne : Not (s = 1) := by
    intro hEq
    have hEqIm := congrArg Complex.im hEq
    rw [hsIm, Complex.one_im] at hEqIm
    exact hIm hEqIm
  have hVPos : 0 < v := hEps.trans_le hvIcc.1
  have hZeta : Not (riemannZeta s = 0) := by
    dsimp [s]
    exact hRay v hVPos
  have hFactor : Not (nicolasZetaPoleFactor s = 0) :=
    nicolasZetaPoleFactor_ne_zero_of_zeta_ne_zero hsOne hZeta
  have hShift :
      ((((v - eps + 1 : Real) : Complex) -
          nicolasRightmostRayPoint rho eps)) = s := by
    dsimp [s, nicolasRightmostRayPoint]
    push_cast
    ring
  have hShiftZero : Not
      ((((v - eps + 1 : Real) : Complex) -
          nicolasRightmostRayPoint rho eps) = 0) := by
    rw [hShift]
    exact hsZero
  have hShiftFactor : Not
      (nicolasZetaPoleFactor
        (((v - eps + 1 : Real) : Complex) -
          nicolasRightmostRayPoint rho eps) = 0) := by
    rw [hShift]
    exact hFactor
  have hJoint := nicolasJMellinShiftIntegrandFilled_joint_continuousAt
    (u := v - eps) (z := nicolasRightmostRayPoint rho eps)
    hU hzZero hShiftZero hShiftFactor
  have hEmbed : ContinuousAt (fun w : Real =>
      (w - eps, nicolasRightmostRayPoint rho eps)) v := by
    fun_prop
  have hTail : ContinuousAt (fun w : Real =>
      nicolasJMellinShiftIntegrandFilled
        (nicolasRightmostRayPoint rho eps) (w - eps)) v := by
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    simpa [Function.comp_def] using hComp
  have hCast : ContinuousAt (fun w : Real => (w : Complex)) v := by
    fun_prop
  unfold nicolasJRightmostRayTranslatedScaledKernelFilled
  exact (hCast.mul hTail).continuousWithinAt

theorem exists_nicolasRightmostRayScaledKernelFilled_uniform
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Exists fun d : Complex => Exists fun r : Real =>
      And (Not (d = 0))
        (And (0 < r) (And (r < 1 / 2)
          (forall eps v : Real, 0 < eps -> eps < v -> v <= r ->
            norm
              (nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v - d) <=
              norm d / 4))) := by
  choose d r hd hrPos hrHalf hUniform using
    exists_nicolasRightmostRayScaledKernel_uniform hZero hHalf hOneRe
  refine Exists.intro d (Exists.intro r
    (And.intro hd (And.intro hrPos (And.intro hrHalf ?_))))
  intro eps v hEps hEpsV hVr
  rw [nicolasJRightmostRayTranslatedScaledKernelFilled_eq_raw
    hZero hHalf hOneRe hRay hEps hEpsV]
  exact hUniform eps v hEps hEpsV hVr

theorem exists_nicolasRightmostRayScaledKernel_log_interval_estimate
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Exists fun d : Complex => Exists fun r : Real =>
      And (Not (d = 0))
        (And (0 < r) (And (r < 1 / 2)
          (forall eps : Real, 0 < eps -> eps < r ->
            norm (intervalIntegral (fun v : Real =>
                HSMul.hSMul (Inv.inv v)
                  (nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v))
                eps r volume -
              HSMul.hSMul (Real.log (r / eps)) d) <=
              (norm d / 4) * abs (Real.log (r / eps))))) := by
  choose d r hd hrPos hrHalf hUniform using
    exists_nicolasRightmostRayScaledKernelFilled_uniform
      hZero hHalf hOneRe hRay
  refine Exists.intro d (Exists.intro r
    (And.intro hd (And.intro hrPos (And.intro hrHalf ?_))))
  intro eps hEps hEpsR
  have hInt :=
    nicolasJRightmostRayTranslatedScaledKernelFilled_intervalIntegrable
      hZero hHalf hOneRe hRay hEps hEpsR (by linarith)
  apply norm_intervalIntegral_inv_smul_sub_le_of_intervalIntegrable
    hInt hEps hrPos (by positivity)
  intro v hv
  have hvIoc : Membership.mem (Ioc eps r) v := by
    simpa [uIoc, min_eq_left hEpsR.le, max_eq_right hEpsR.le] using hv
  exact hUniform eps v hEps hvIoc.1 hvIoc.2

theorem nicolasRightmostRay_weighted_scaledKernelFilled_interval_eq
    {rho : Complex} {eps r : Real} (hEps : 0 < eps) (hEpsR : eps < r) :
    intervalIntegral (fun v : Real =>
        HSMul.hSMul (Inv.inv v)
          (nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v))
        eps r volume =
      intervalIntegral
        (nicolasJMellinShiftIntegrandFilled
          (nicolasRightmostRayPoint rho eps))
        0 (r - eps) volume := by
  calc
    intervalIntegral (fun v : Real =>
        HSMul.hSMul (Inv.inv v)
          (nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v))
        eps r volume =
        intervalIntegral (fun v : Real =>
          nicolasJMellinShiftIntegrandFilled
            (nicolasRightmostRayPoint rho eps) (v - eps))
          eps r volume := by
      apply intervalIntegral.integral_congr
      intro v hv
      have hvIcc : Membership.mem (Icc eps r) v := by
        simpa [uIcc, min_eq_left hEpsR.le,
          max_eq_right hEpsR.le] using hv
      have hvPos : 0 < v := hEps.trans_le hvIcc.1
      unfold nicolasJRightmostRayTranslatedScaledKernelFilled
      change ((Inv.inv v : Real) : Complex) *
          ((v : Complex) *
            nicolasJMellinShiftIntegrandFilled
              (nicolasRightmostRayPoint rho eps) (v - eps)) =
        nicolasJMellinShiftIntegrandFilled
          (nicolasRightmostRayPoint rho eps) (v - eps)
      rw [Complex.ofReal_inv]
      field_simp [Complex.ofReal_ne_zero.mpr hvPos.ne']
    _ = intervalIntegral
        (nicolasJMellinShiftIntegrandFilled
          (nicolasRightmostRayPoint rho eps))
        (eps - eps) (r - eps) volume := by
      exact intervalIntegral.integral_comp_sub_right
        (nicolasJMellinShiftIntegrandFilled
          (nicolasRightmostRayPoint rho eps)) eps
    _ = intervalIntegral
        (nicolasJMellinShiftIntegrandFilled
          (nicolasRightmostRayPoint rho eps))
        0 (r - eps) volume := by ring_nf

theorem exists_nicolasRightmostRayCompactSingularIntegral_lowerBound
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Exists fun d : Complex => Exists fun r : Real =>
      And (Not (d = 0))
        (And (0 < r) (And (r < 1 / 2)
          (forall eps : Real, 0 < eps -> eps < r ->
            (3 / 4 : Real) * norm d * Real.log (r / eps) <=
              norm (intervalIntegral
                (nicolasJMellinShiftIntegrandFilled
                  (nicolasRightmostRayPoint rho eps))
                0 (r - eps) volume)))) := by
  choose d r hd hrPos hrHalf hEstimate using
    exists_nicolasRightmostRayScaledKernel_log_interval_estimate
      hZero hHalf hOneRe hRay
  refine Exists.intro d (Exists.intro r
    (And.intro hd (And.intro hrPos (And.intro hrHalf ?_))))
  intro eps hEps hEpsR
  let I : Complex := intervalIntegral (fun v : Real =>
      HSMul.hSMul (Inv.inv v)
        (nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v))
      eps r volume
  let A : Complex := HSMul.hSMul (Real.log (r / eps)) d
  have hRatio : 1 < r / eps := (one_lt_div hEps).mpr hEpsR
  have hLogPos : 0 < Real.log (r / eps) := Real.log_pos hRatio
  have hErr : norm (I - A) <=
      (norm d / 4) * Real.log (r / eps) := by
    dsimp [I, A]
    simpa [abs_of_pos hLogPos] using hEstimate eps hEps hEpsR
  have hReverse : norm A - norm I <= norm (I - A) := by
    have hBasic := (le_abs_self (norm A - norm I)).trans
      (abs_norm_sub_norm_le A I)
    simpa [norm_sub_rev] using hBasic
  have hANorm : norm A = Real.log (r / eps) * norm d := by
    dsimp [A]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hLogPos]
  have hLowerI : (3 / 4 : Real) * norm d * Real.log (r / eps) <=
      norm I := by
    rw [hANorm] at hReverse
    have hdNorm : 0 <= norm d := norm_nonneg d
    nlinarith [hReverse.trans hErr]
  dsimp [I] at hLowerI
  have hIntegralEq :
      intervalIntegral (fun v : Real =>
          ((Inv.inv v : Real) : Complex) *
            nicolasJRightmostRayTranslatedScaledKernelFilled rho eps v)
          eps r volume =
        intervalIntegral
          (nicolasJMellinShiftIntegrandFilled
            (nicolasRightmostRayPoint rho eps))
          0 (r - eps) volume := by
    simpa [smul_eq_mul] using
      (nicolasRightmostRay_weighted_scaledKernelFilled_interval_eq
        (rho := rho) hEps hEpsR)
  rw [hIntegralEq] at hLowerI
  exact hLowerI

theorem exists_nicolasRightmostRayCompactAwayKernel_bound
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {r : Real} (hrPos : 0 < r) (hrHalf : r < 1 / 2) :
    Exists fun M : Real => And (0 <= M)
      (forall eps u : Real,
        Membership.mem (Icc (0 : Real) (r / 2)) eps ->
        Membership.mem (Icc (r / 2) (1 : Real)) u ->
        norm (nicolasJMellinShiftIntegrandFilled
          (nicolasRightmostRayPoint rho eps) u) <= M) := by
  let K : Set (Prod Real Real) := fun p =>
    And (Membership.mem (Icc (0 : Real) (r / 2)) p.1)
      (Membership.mem (Icc (r / 2) (1 : Real)) p.2)
  let F : Prod Real Real -> Complex := fun p =>
    nicolasJMellinShiftIntegrandFilled
      (nicolasRightmostRayPoint rho p.1) p.2
  have hKCompact : IsCompact K := by
    dsimp [K]
    exact (isCompact_Icc : IsCompact (Icc (0 : Real) (r / 2))).prod
      (isCompact_Icc : IsCompact (Icc (r / 2) (1 : Real)))
  have hKNonempty : K.Nonempty := by
    refine Exists.intro ((0 : Real), r / 2) ?_
    dsimp [K]
    exact And.intro (And.intro le_rfl (by positivity))
      (And.intro le_rfl (by linarith))
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOneRe
  have hContinuous : ContinuousOn F K := by
    apply continuousOn_of_forall_continuousAt
    intro p hp
    change And (Membership.mem (Icc (0 : Real) (r / 2)) p.1)
      (Membership.mem (Icc (r / 2) (1 : Real)) p.2) at hp
    have hzZero : Not (nicolasRightmostRayPoint rho p.1 = 0) := by
      intro hEq
      have hEqIm := congrArg Complex.im hEq
      unfold nicolasRightmostRayPoint at hEqIm
      simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im,
        Complex.zero_im] at hEqIm
      apply hIm
      linarith
    let s : Complex := rho + ((p.1 + p.2 : Real) : Complex)
    have hsIm : s.im = rho.im := by
      dsimp [s]
      simp
    have hsZero : Not (s = 0) := by
      intro hEq
      have hEqIm := congrArg Complex.im hEq
      rw [hsIm, Complex.zero_im] at hEqIm
      exact hIm hEqIm
    have hsOne : Not (s = 1) := by
      intro hEq
      have hEqIm := congrArg Complex.im hEq
      rw [hsIm, Complex.one_im] at hEqIm
      exact hIm hEqIm
    have hSumPos : 0 < p.1 + p.2 := by
      linarith [hp.1.1, hp.2.1, hrPos]
    have hZeta : Not (riemannZeta s = 0) := by
      dsimp [s]
      exact hRay (p.1 + p.2) hSumPos
    have hFactor : Not (nicolasZetaPoleFactor s = 0) :=
      nicolasZetaPoleFactor_ne_zero_of_zeta_ne_zero hsOne hZeta
    have hShift :
        ((((p.2 + 1 : Real) : Complex) -
            nicolasRightmostRayPoint rho p.1)) = s := by
      dsimp [s, nicolasRightmostRayPoint]
      push_cast
      ring
    have hShiftZero : Not
        ((((p.2 + 1 : Real) : Complex) -
            nicolasRightmostRayPoint rho p.1) = 0) := by
      rw [hShift]
      exact hsZero
    have hShiftFactor : Not
        (nicolasZetaPoleFactor
          (((p.2 + 1 : Real) : Complex) -
            nicolasRightmostRayPoint rho p.1) = 0) := by
      rw [hShift]
      exact hFactor
    have hJoint := nicolasJMellinShiftIntegrandFilled_joint_continuousAt
      (u := p.2) (z := nicolasRightmostRayPoint rho p.1)
      (by linarith [hp.2.1, hrPos]) hzZero hShiftZero hShiftFactor
    have hEmbed : ContinuousAt (fun q : Prod Real Real =>
        (q.2, nicolasRightmostRayPoint rho q.1)) p := by
      unfold nicolasRightmostRayPoint
      fun_prop
    have hComp := hJoint.comp_of_eq hEmbed (by rfl)
    simpa [F, Function.comp_def] using hComp
  choose p hpK hpMax using
    hKCompact.exists_isMaxOn hKNonempty hContinuous.norm
  let M : Real := norm (F p)
  refine Exists.intro M (And.intro (norm_nonneg _) ?_)
  intro eps u hEps hU
  have hPair : K (eps, u) := by
    dsimp [K]
    exact And.intro hEps hU
  simpa [M, F] using hpMax hPair

theorem exists_nicolasRightmostRayCompactAwayIntegral_bound
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0))
    {r : Real} (hrPos : 0 < r) (hrHalf : r < 1 / 2) :
    Exists fun M : Real => And (0 <= M)
      (forall eps : Real, 0 <= eps -> eps <= r / 2 ->
        norm (intervalIntegral
          (nicolasJMellinShiftIntegrandFilled
            (nicolasRightmostRayPoint rho eps))
          (r - eps) 1 volume) <= M) := by
  choose M hMNonneg hKernel using
    exists_nicolasRightmostRayCompactAwayKernel_bound
      hZero hHalf hOneRe hRay hrPos hrHalf
  refine Exists.intro M (And.intro hMNonneg ?_)
  intro eps hEps hEpsLe
  have hLowerNonneg : 0 <= r - eps := by linarith
  have hLowerOne : r - eps <= 1 := by linarith
  have hPointwise : forall u : Real,
      Membership.mem (uIoc (r - eps) (1 : Real)) u ->
      norm (nicolasJMellinShiftIntegrandFilled
        (nicolasRightmostRayPoint rho eps) u) <= M := by
    intro u hu
    have huIoc : Membership.mem (Ioc (r - eps) (1 : Real)) u := by
      simpa [uIoc, min_eq_left hLowerOne,
        max_eq_right hLowerOne] using hu
    apply hKernel eps u
    . exact And.intro hEps hEpsLe
    . exact And.intro (by linarith [huIoc.1]) huIoc.2
  have hNorm := intervalIntegral.norm_integral_le_of_norm_le_const hPointwise
  rw [abs_of_nonneg (by linarith : 0 <= (1 : Real) - (r - eps))] at hNorm
  nlinarith

theorem exists_nicolasRightmostRayCompactIntegral_log_lowerBound
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Exists fun d : Complex => Exists fun r : Real => Exists fun M : Real =>
      And (Not (d = 0))
        (And (0 < r) (And (r < 1 / 2) (And (0 <= M)
          (forall eps : Real, 0 < eps -> eps <= r / 2 ->
            (3 / 4 : Real) * norm d * Real.log (r / eps) - M <=
              norm (intervalIntegral
                (nicolasJMellinShiftIntegrandFilled
                  (nicolasRightmostRayPoint rho eps))
                0 1 volume))))) := by
  choose d r hd hrPos hrHalf hSingular using
    exists_nicolasRightmostRayCompactSingularIntegral_lowerBound
      hZero hHalf hOneRe hRay
  choose M hMNonneg hAway using
    exists_nicolasRightmostRayCompactAwayIntegral_bound
      hZero hHalf hOneRe hRay hrPos hrHalf
  refine Exists.intro d (Exists.intro r (Exists.intro M
    (And.intro hd (And.intro hrPos (And.intro hrHalf
      (And.intro hMNonneg ?_))))))
  intro eps hEps hEpsLe
  have hEpsR : eps < r := by linarith [hrPos]
  have hLowerNonneg : 0 <= r - eps := by linarith [hEpsLe, hrPos]
  have hLowerOne : r - eps <= 1 := by linarith [hrHalf]
  let f : Real -> Complex :=
    nicolasJMellinShiftIntegrandFilled
      (nicolasRightmostRayPoint rho eps)
  have hIntegrableOn : IntegrableOn f (Ioc (0 : Real) 1) := by
    have hEventually :=
      eventually_nicolasJMellinShiftIntegrandFilled_integrableOn_compact_rightmostRay
        hZero hHalf hOneRe hRay hEps
    have hAt := hEventually.self_of_nhds
    simpa [f, nicolasRightmostRayPoint] using hAt
  have hFullIntegrable : IntervalIntegrable f volume 0 1 := by
    rw [intervalIntegrable_iff]
    simpa [uIoc, min_eq_left zero_le_one,
      max_eq_right zero_le_one] using hIntegrableOn
  have hLeftIntegrable : IntervalIntegrable f volume 0 (r - eps) := by
    apply hFullIntegrable.mono_set
    intro u hu
    have huSmall : Membership.mem (Icc (0 : Real) (r - eps)) u := by
      simpa [uIcc, min_eq_left hLowerNonneg,
        max_eq_right hLowerNonneg] using hu
    have huFull : Membership.mem (Icc (0 : Real) 1) u :=
      And.intro huSmall.1 (huSmall.2.trans hLowerOne)
    simpa [uIcc, min_eq_left zero_le_one,
      max_eq_right zero_le_one] using huFull
  have hRightIntegrable : IntervalIntegrable f volume (r - eps) 1 := by
    apply hFullIntegrable.mono_set
    intro u hu
    have huSmall : Membership.mem (Icc (r - eps) (1 : Real)) u := by
      simpa [uIcc, min_eq_left hLowerOne,
        max_eq_right hLowerOne] using hu
    have huFull : Membership.mem (Icc (0 : Real) 1) u :=
      And.intro (hLowerNonneg.trans huSmall.1) huSmall.2
    simpa [uIcc, min_eq_left zero_le_one,
      max_eq_right zero_le_one] using huFull
  let L : Complex := intervalIntegral f 0 (r - eps) volume
  let R : Complex := intervalIntegral f (r - eps) 1 volume
  let T : Complex := intervalIntegral f 0 1 volume
  have hDecomp : L + R = T := by
    dsimp [L, R, T]
    exact intervalIntegral.integral_add_adjacent_intervals
      hLeftIntegrable hRightIntegrable
  have hTriangle : norm L <= norm T + norm R := by
    calc
      norm L = norm ((L + R) - R) := by ring_nf
      _ <= norm (L + R) + norm R := norm_sub_le _ _
      _ = norm T + norm R := by rw [hDecomp]
  have hSing : (3 / 4 : Real) * norm d * Real.log (r / eps) <=
      norm L := by
    dsimp [L, f]
    exact hSingular eps hEps hEpsR
  have hAwayBound : norm R <= M := by
    dsimp [R, f]
    exact hAway eps hEps.le hEpsLe
  have hFinal : (3 / 4 : Real) * norm d * Real.log (r / eps) - M <=
      norm T := by
    linarith
  simpa [T, f] using hFinal

theorem nicolasRightmostRayCompactIntegral_norm_tendsto_atTop
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Tendsto (fun eps : Real =>
        norm (intervalIntegral
          (nicolasJMellinShiftIntegrandFilled
            (nicolasRightmostRayPoint rho eps))
          0 1 volume))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
  choose d r M hd hrPos hrHalf hMNonneg hLower using
    exists_nicolasRightmostRayCompactIntegral_log_lowerBound
      hZero hHalf hOneRe hRay
  have hInv : Tendsto (fun eps : Real => Inv.inv eps)
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
    simpa using (tendsto_inv_nhdsGT_zero :
      Tendsto (fun eps : Real => Inv.inv eps)
        (nhdsWithin 0 (Ioi (0 : Real))) atTop)
  have hRatio : Tendsto (fun eps : Real => r / eps)
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
    have hMul := Tendsto.const_mul_atTop hrPos hInv
    simpa [div_eq_mul_inv] using hMul
  have hLog : Tendsto (fun eps : Real => Real.log (r / eps))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop :=
    Real.tendsto_log_atTop.comp hRatio
  have hCoefficient : 0 < (3 / 4 : Real) * norm d :=
    mul_pos (by norm_num) (norm_pos_iff.mpr hd)
  have hScaled : Tendsto (fun eps : Real =>
      ((3 / 4 : Real) * norm d) * Real.log (r / eps))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop :=
    Tendsto.const_mul_atTop hCoefficient hLog
  have hLowerTendsto : Tendsto (fun eps : Real =>
      (3 / 4 : Real) * norm d * Real.log (r / eps) - M)
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
    simpa [mul_assoc, sub_eq_add_neg] using
      (tendsto_atTop_add_const_right
        (nhdsWithin 0 (Ioi (0 : Real))) (-M) hScaled)
  have hSmall : Filter.Eventually (fun eps : Real => eps <= r / 2)
      (nhdsWithin 0 (Ioi (0 : Real))) := by
    have hNhd : Membership.mem (nhds (0 : Real)) (Iio (r / 2)) :=
      Iio_mem_nhds (by positivity)
    have hNhdWithin : Filter.Eventually (fun eps : Real => eps < r / 2)
        (nhdsWithin 0 (Ioi (0 : Real))) :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hNhd
    filter_upwards [hNhdWithin] with eps hEps
    exact hEps.le
  have hEventualLower : Filter.Eventually (fun eps : Real =>
      (3 / 4 : Real) * norm d * Real.log (r / eps) - M <=
        norm (intervalIntegral
          (nicolasJMellinShiftIntegrandFilled
            (nicolasRightmostRayPoint rho eps))
          0 1 volume))
      (nhdsWithin 0 (Ioi (0 : Real))) := by
    filter_upwards [self_mem_nhdsWithin, hSmall] with eps hEps hEpsLe
    exact hLower eps (mem_Ioi.mp hEps) hEpsLe
  exact tendsto_atTop_mono'
    (nhdsWithin 0 (Ioi (0 : Real))) hEventualLower hLowerTendsto

theorem nicolasJShiftedComplexContinuationFilledLarge_analyticAt_rightmostRayEndpoint
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledLarge
      (nicolasRightmostRayPoint rho 0) := by
  let center : Complex := nicolasRightmostRayPoint rho 0
  have hIm : Not (rho.im = 0) :=
    riemannZeta_zero_im_ne_zero_of_re_mem_Ioo hZero
      (lt_trans (by norm_num) hHalf) hOneRe
  have hCenterIm : center.im = -rho.im := by
    dsimp [center, nicolasRightmostRayPoint]
    simp
  have hCenterNe : Not (center = 0) := by
    intro hEq
    have hZeroIm : center.im = 0 := by rw [hEq]; simp
    apply hIm
    linarith [hCenterIm, hZeroIm]
  have hCenterNorm : 0 < norm center := norm_pos_iff.mpr hCenterNe
  have hCenterRe : center.re = 1 - rho.re := by
    dsimp [center, nicolasRightmostRayPoint]
    simp
  have hReMargin : 0 < (3 / 4 : Real) - center.re := by
    rw [hCenterRe]
    linarith
  let d : Real := norm center / 2
  let R : Real := min (norm center / 2)
    (((3 / 4 : Real) - center.re) / 2)
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hRPos : 0 < R := by
    dsimp [R]
    exact lt_min (by positivity) (by positivity)
  have hGeometry : forall z : Complex,
      Membership.mem (Metric.ball center R) z ->
        And (z.re <= (3 / 4 : Real)) (d <= norm z) := by
    intro z hz
    have hzDist : dist z center < R := by
      simpa [Metric.mem_ball] using hz
    have hDistNorm : dist z center < norm center / 2 :=
      lt_of_lt_of_le hzDist (by
        dsimp [R]
        exact min_le_left _ _)
    have hDistRe : dist z center <
        ((3 / 4 : Real) - center.re) / 2 :=
      lt_of_lt_of_le hzDist (by
        dsimp [R]
        exact min_le_right _ _)
    have hReDiff : z.re - center.re <= dist z center := by
      calc
        z.re - center.re <= abs (z.re - center.re) := le_abs_self _
        _ = abs ((z - center).re) :=
          congrArg abs (Complex.sub_re z center).symm
        _ <= norm (z - center) := Complex.abs_re_le_norm _
        _ = dist z center := by rw [dist_eq_norm]
    have hTriangle : norm center <= dist center z + norm z := by
      have h := dist_triangle center z 0
      simpa [dist_zero_right] using h
    have hNorm : d <= norm z := by
      dsimp [d]
      rw [dist_comm center z] at hTriangle
      linarith
    exact And.intro (by linarith) hNorm
  apply nicolasJShiftedComplexContinuationFilledLarge_analyticAt_of_ball
    hRPos hd
  intro z hz
  exact hGeometry z (by simpa [center] using hz)

theorem nicolasJShiftedComplexContinuationFilledLarge_rightmostRay_tendsto
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1) :
    Tendsto (fun eps : Real =>
        nicolasJShiftedComplexContinuationFilledLarge
          (nicolasRightmostRayPoint rho eps))
      (nhdsWithin 0 (Ioi (0 : Real)))
      (nhds (nicolasJShiftedComplexContinuationFilledLarge
        (nicolasRightmostRayPoint rho 0))) := by
  have hOuter :=
    (nicolasJShiftedComplexContinuationFilledLarge_analyticAt_rightmostRayEndpoint
      hZero hHalf hOneRe).continuousAt.tendsto
  have hInner : Tendsto (nicolasRightmostRayPoint rho)
      (nhdsWithin 0 (Ioi (0 : Real)))
      (nhds (nicolasRightmostRayPoint rho 0)) := by
    have hContinuous : ContinuousAt (nicolasRightmostRayPoint rho) 0 := by
      unfold nicolasRightmostRayPoint
      fun_prop
    exact hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  exact hOuter.comp hInner

theorem nicolasJShiftedComplexContinuationFilled_rightmostRay_norm_tendsto_atTop
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hHalf : (1 / 2 : Real) < rho.re) (hOneRe : rho.re < 1)
    (hRay : forall v : Real, 0 < v ->
      Not (riemannZeta (rho + (v : Complex)) = 0)) :
    Tendsto (fun eps : Real =>
        norm (nicolasJShiftedComplexContinuationFilled
          (nicolasRightmostRayPoint rho eps)))
      (nhdsWithin 0 (Ioi (0 : Real))) atTop := by
  let l : Filter Real := nhdsWithin 0 (Ioi (0 : Real))
  let C : Real -> Complex := fun eps =>
    nicolasJShiftedComplexContinuationFilledCompact
      (nicolasRightmostRayPoint rho eps)
  let G : Real -> Complex := fun eps =>
    nicolasJShiftedComplexContinuationFilledLarge
      (nicolasRightmostRayPoint rho eps)
  let H : Real -> Complex := fun eps =>
    nicolasJShiftedComplexContinuationFilled
      (nicolasRightmostRayPoint rho eps)
  have hCompact : Tendsto (fun eps : Real => norm (C eps)) l atTop := by
    have hBase := nicolasRightmostRayCompactIntegral_norm_tendsto_atTop
      hZero hHalf hOneRe hRay
    simpa [l, C, nicolasJShiftedComplexContinuationFilledCompact,
      intervalIntegral.integral_of_le zero_le_one] using hBase
  let G0 : Complex := nicolasJShiftedComplexContinuationFilledLarge
    (nicolasRightmostRayPoint rho 0)
  have hLarge : Tendsto G l (nhds G0) := by
    simpa [l, G, G0] using
      nicolasJShiftedComplexContinuationFilledLarge_rightmostRay_tendsto
        hZero hHalf hOneRe
  have hLargeBound : Filter.Eventually (fun eps : Real =>
      norm (G eps) <= norm G0 + 1) l := by
    have hBall := hLarge.eventually
      (Metric.ball_mem_nhds G0 (by norm_num : (0 : Real) < 1))
    filter_upwards [hBall] with eps hEps
    have hDist : norm (G eps - G0) < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hEps
    calc
      norm (G eps) = norm ((G eps - G0) + G0) := by ring_nf
      _ <= norm (G eps - G0) + norm G0 := norm_add_le _ _
      _ <= norm G0 + 1 := by linarith
  have hEq : Filter.Eventually (fun eps : Real => H eps = C eps + G eps) l := by
    filter_upwards [self_mem_nhdsWithin] with eps hEps
    have hAt :=
      (eventually_nicolasJShiftedComplexContinuationFilled_eq_compact_add_large_rightmostRay
        hZero hHalf hOneRe hRay (mem_Ioi.mp hEps)).self_of_nhds
    simpa [H, C, G, nicolasRightmostRayPoint] using hAt
  have hLowerTendsto : Tendsto (fun eps : Real =>
      norm (C eps) - (norm G0 + 1)) l atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right l (-(norm G0 + 1)) hCompact)
  have hEventualLower : Filter.Eventually (fun eps : Real =>
      norm (C eps) - (norm G0 + 1) <= norm (H eps)) l := by
    filter_upwards [hLargeBound, hEq] with eps hGBound hAt
    have hTriangle : norm (C eps) <= norm (H eps) + norm (G eps) := by
      calc
        norm (C eps) = norm ((C eps + G eps) - G eps) := by ring_nf
        _ = norm (H eps - G eps) := by rw [hAt]
        _ <= norm (H eps) + norm (G eps) := norm_sub_le _ _
    linarith
  exact tendsto_atTop_mono' l hEventualLower hLowerTendsto

end

end Robin1984

end
end

section
/- Positive Mellin continuation for Nicolas's tail. Adapted from Jonas Whidden's Robin1984, Apache 2.0, revision e3697139babfe0f6cc7a76a08bf41a92aa7a2978. The case distinction on absolute integrability removes the quantitative prime number theorem from this argument. -/

section
/- Source module Robin1984.Mathlib.Probability.Moments.MGFAnalyticContinuation. -/
namespace ProbabilityTheory
open Filter MeasureTheory Set
open scoped ENNReal Topology
noncomputable section
theorem positive_mem_interior_integrableExpSet_of_two_sided
    {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega -> Real} {mu : Measure Omega}
    {l a r : Real}
    (hl : Membership.mem (integrableExpSet X mu) l)
    (hr : Membership.mem (integrableExpSet X mu) r)
    (hla : l < a) (har : a < r) :
    Membership.mem (interior (integrableExpSet X mu)) a := by
  rw [mem_interior_iff_mem_nhds]
  let eps : Real := min (a - l) (r - a) / 2
  have hMinPos : 0 < min (a - l) (r - a) :=
    lt_min (sub_pos.mpr hla) (sub_pos.mpr har)
  have hEpsPos : 0 < eps := by
    dsimp [eps]
    positivity
  apply mem_of_superset (Metric.ball_mem_nhds a hEpsPos)
  intro y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have hEpsLeft : eps <= a - l := by
    dsimp [eps]
    have hMinLe := min_le_left (a - l) (r - a)
    linarith
  have hEpsRight : eps <= r - a := by
    dsimp [eps]
    have hMinLe := min_le_right (a - l) (r - a)
    linarith
  have hyLeft : l <= y := by
    have hyLower := (abs_lt.mp hy).1
    linarith
  have hyRight : y <= r := by
    have hyUpper := (abs_lt.mp hy).2
    linarith
  exact convex_integrableExpSet.ordConnected.out hl hr
    (And.intro hyLeft hyRight)

theorem mem_integrableExpSet_add_of_summable_moments
    {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega -> Real} {mu : Measure Omega} {a d : Real}
    (hX : Filter.Eventually (fun w => 0 <= X w) (ae mu))
    (ha : Membership.mem
      (interior (ProbabilityTheory.integrableExpSet X mu)) a)
    (hd : 0 <= d)
    (hSummable : Summable (fun n : Nat =>
      (integral mu (fun w => X w ^ n * Real.exp (a * X w)) /
          (Nat.factorial n : Real)) * d ^ n)) :
    Membership.mem (ProbabilityTheory.integrableExpSet X mu) (a + d) := by
  let term : Nat -> Omega -> Real := fun n w =>
    (d ^ n / (Nat.factorial n : Real)) *
      (X w ^ n * Real.exp (a * X w))
  have hMomentIntegrable : forall n : Nat,
      Integrable (fun w => X w ^ n * Real.exp (a * X w)) mu := by
    intro n
    exact ProbabilityTheory.integrable_pow_mul_exp_of_mem_interior_integrableExpSet
      ha n
  have hTermIntegrable : forall n : Nat, Integrable (term n) mu := by
    intro n
    exact (hMomentIntegrable n).const_mul
      (d ^ n / (Nat.factorial n : Real))
  have hTermNonneg : forall n : Nat,
      Filter.Eventually (fun w => 0 <= term n w) (ae mu) := by
    intro n
    filter_upwards [hX] with w hw
    exact mul_nonneg
      (div_nonneg (pow_nonneg hd n) (Nat.cast_nonneg (Nat.factorial n)))
      (mul_nonneg (pow_nonneg hw n) (Real.exp_pos _).le)
  have hTermIntegral : forall n : Nat,
      integral mu (term n) =
        (integral mu (fun w => X w ^ n * Real.exp (a * X w)) /
          (Nat.factorial n : Real)) * d ^ n := by
    intro n
    dsimp [term]
    rw [integral_const_mul]
    ring
  have hTermSummable : forall w : Omega, Summable (fun n : Nat => term n w) := by
    intro w
    have hExp : Summable (fun n : Nat =>
        (d * X w) ^ n / (Nat.factorial n : Real)) :=
      NormedSpace.expSeries_div_summable (d * X w)
    have hScaled := hExp.mul_left (Real.exp (a * X w))
    apply hScaled.congr
    intro n
    dsimp [term]
    rw [mul_pow]
    ring
  have hPointwise : forall w : Omega,
      Real.exp ((a + d) * X w) = tsum (fun n : Nat => term n w) := by
    intro w
    calc
      Real.exp ((a + d) * X w) =
          Real.exp (a * X w) * Real.exp (d * X w) := by
        rw [add_mul, Real.exp_add]
      _ = Real.exp (a * X w) *
          tsum (fun n : Nat =>
            (d * X w) ^ n / (Nat.factorial n : Real)) := by
        have hExpTsum : Real.exp (d * X w) =
            tsum (fun n : Nat =>
              (d * X w) ^ n / (Nat.factorial n : Real)) := by
          apply Complex.ofReal_injective
          rw [Complex.ofReal_exp, Complex.exp]
          have hCast :
              ((tsum (fun n : Nat =>
                (d * X w) ^ n / (Nat.factorial n : Real)) : Real) : Complex) =
                tsum (fun n : Nat =>
                  ((d * X w : Real) : Complex) ^ n /
                    (Nat.factorial n : Complex)) := by
            rw [Complex.ofReal_tsum]
            apply tsum_congr
            intro n
            push_cast
            rfl
          rw [hCast]
          exact tendsto_nhds_unique
            (Complex.exp' (((d * X w : Real) : Complex))).tendsto_limit
            (NormedSpace.expSeries_div_summable
              (((d * X w : Real) : Complex))).hasSum.tendsto_sum_nat
        rw [hExpTsum]
      _ = tsum (fun n : Nat =>
          Real.exp (a * X w) *
            ((d * X w) ^ n / (Nat.factorial n : Real))) := by
        rw [<- (NormedSpace.expSeries_div_summable
          (d * X w)).tsum_mul_left]
      _ = tsum (fun n : Nat => term n w) := by
        apply tsum_congr
        intro n
        dsimp [term]
        rw [mul_pow]
        ring
  change Integrable (fun w => Real.exp ((a + d) * X w)) mu
  have hXMeasurable : AEMeasurable X mu :=
    ProbabilityTheory.aemeasurable_of_mem_interior_integrableExpSet ha
  refine And.intro
    ((Real.measurable_exp.comp_aemeasurable
      (hXMeasurable.const_mul (a + d))).aestronglyMeasurable) ?_
  rw [hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun w => (Real.exp_pos _).le))]
  calc
    lintegral mu (fun w => ENNReal.ofReal (Real.exp ((a + d) * X w))) =
        lintegral mu (fun w => tsum (fun n : Nat =>
          ENNReal.ofReal (term n w))) := by
      apply lintegral_congr_ae
      filter_upwards [hX] with w hw
      rw [hPointwise w]
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun n => by
          dsimp [term]
          exact mul_nonneg
            (div_nonneg (pow_nonneg hd n)
              (Nat.cast_nonneg (Nat.factorial n)))
            (mul_nonneg (pow_nonneg hw n) (Real.exp_pos _).le))
        (hTermSummable w)
    _ = tsum (fun n : Nat =>
        lintegral mu (fun w => ENNReal.ofReal (term n w))) := by
      rw [lintegral_tsum]
      intro n
      exact (hTermIntegrable n).aemeasurable.ennreal_ofReal
    _ = tsum (fun n : Nat => ENNReal.ofReal
        ((integral mu (fun w => X w ^ n * Real.exp (a * X w)) /
          (Nat.factorial n : Real)) * d ^ n)) := by
      apply tsum_congr
      intro n
      rw [<- ofReal_integral_eq_lintegral_ofReal
        (hTermIntegrable n) (hTermNonneg n), hTermIntegral]
    _ < Top.top := hSummable.tsum_ofReal_lt_top

theorem mem_integrableExpSet_add_of_analyticContinuationOnBall
    {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega -> Real} {mu : Measure Omega} {a d : Real}
    {H : Real -> Real} {p : FormalMultilinearSeries Real Real Real}
    {r : ENNReal}
    (hX : Filter.Eventually (fun w => 0 <= X w) (ae mu))
    (ha : Membership.mem
      (interior (ProbabilityTheory.integrableExpSet X mu)) a)
    (hH : HasFPowerSeriesOnBall H p a r)
    (hEq : Filter.EventuallyEq (nhds a) (ProbabilityTheory.mgf X mu) H)
    (hd : 0 <= d)
    (hdBall : Membership.mem (Metric.eball a r) (a + d)) :
    Membership.mem (ProbabilityTheory.integrableExpSet X mu) (a + d) := by
  let q : FormalMultilinearSeries Real Real Real :=
    FormalMultilinearSeries.ofScalars Real (fun n : Nat =>
      (integral mu (fun w => X w ^ n * Real.exp (a * X w)) /
        (Nat.factorial n : Real)))
  have hMgf : HasFPowerSeriesAt (ProbabilityTheory.mgf X mu) q a := by
    dsimp [q]
    exact ProbabilityTheory.hasFPowerSeriesAt_mgf ha
  have hHq : HasFPowerSeriesAt H q a := hMgf.congr hEq
  choose rq hHqBall using hHq
  have hTransferred : HasFPowerSeriesOnBall H q a r :=
    hHqBall.exchange_radius hH
  have hSeries := hTransferred.hasSum_sub hdBall
  have hSummable : Summable (fun n : Nat =>
      (integral mu (fun w => X w ^ n * Real.exp (a * X w)) /
        (Nat.factorial n : Real)) * d ^ n) := by
    apply hSeries.summable.congr
    intro n
    dsimp [q]
    rw [FormalMultilinearSeries.ofScalars_apply_eq]
    simp only [add_sub_cancel_left, smul_eq_mul]
  exact mem_integrableExpSet_add_of_summable_moments hX ha hd hSummable

theorem integrableExpSet_strict_crossing_of_analyticContinuationOnBall
    {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega -> Real} {mu : Measure Omega}
    {a d sigma : Real} {H : Real -> Real}
    {p : FormalMultilinearSeries Real Real Real} {r : ENNReal}
    (hX : Filter.Eventually (fun w => 0 <= X w) (ae mu))
    (ha : Membership.mem
      (interior (ProbabilityTheory.integrableExpSet X mu)) a)
    (hH : HasFPowerSeriesOnBall H p sigma r)
    (haCenter : enorm (a - sigma) < r)
    (hEq : Filter.EventuallyEq (nhds a) (ProbabilityTheory.mgf X mu) H)
    (hd : 0 < d)
    (hCross : sigma < a + d)
    (hTarget : Membership.mem
      (Metric.eball a (r - enorm (a - sigma))) (a + d)) :
    And (sigma < a + d)
      (Membership.mem (ProbabilityTheory.integrableExpSet X mu) (a + d)) := by
  have hRecentered : HasFPowerSeriesOnBall H
      (p.changeOrigin (a - sigma)) a (r - enorm (a - sigma)) := by
    have hShift := hH.changeOrigin haCenter
    convert hShift using 1
    . ring
    . simp [enorm_eq_nnnorm]
  exact And.intro hCross
    (mem_integrableExpSet_add_of_analyticContinuationOnBall
      hX ha hRecentered hEq hd.le hTarget)

theorem exists_integrableExpSet_gt_of_analyticContinuationAt
    {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega -> Real} {mu : Measure Omega}
    {sigma : Real} {H : Real -> Real}
    (hX : Filter.Eventually (fun w => 0 <= X w) (ae mu))
    (hBelow : forall a : Real, a < sigma ->
      Membership.mem
        (interior (ProbabilityTheory.integrableExpSet X mu)) a)
    (hH : AnalyticAt Real H sigma)
    (hEq : forall a : Real, a < sigma ->
      ProbabilityTheory.mgf X mu a = H a) :
    Exists fun t : Real => And (sigma < t)
      (Membership.mem (ProbabilityTheory.integrableExpSet X mu) t) := by
  choose p hp using hH
  choose r hBall using hp
  let r0 : ENNReal := min r 1
  have hr0Pos : 0 < r0 := by
    exact lt_min hBall.r_pos zero_lt_one
  have hr0Top : Not (r0 = Top.top) := by
    exact ne_of_lt (lt_of_le_of_lt (min_le_right r 1) ENNReal.one_lt_top)
  have hSmallBall : HasFPowerSeriesOnBall H p sigma r0 :=
    hBall.mono hr0Pos (min_le_left r 1)
  let R : Real := r0.toReal
  have hRPos : 0 < R := ENNReal.toReal_pos hr0Pos.ne' hr0Top
  have hRNonneg : 0 <= R := hRPos.le
  have hr0Eq : ENNReal.ofReal R = r0 := by
    exact ENNReal.ofReal_toReal hr0Top
  let eps : Real := R / 4
  let a : Real := sigma - eps
  let d : Real := 2 * eps
  have hEpsPos : 0 < eps := by
    dsimp [eps]
    positivity
  have hAPos : a < sigma := by
    dsimp [a]
    linarith
  have ha : Membership.mem
      (interior (ProbabilityTheory.integrableExpSet X mu)) a :=
    hBelow a hAPos
  have hEqNhd : Filter.EventuallyEq (nhds a)
      (ProbabilityTheory.mgf X mu) H := by
    filter_upwards [Iio_mem_nhds hAPos] with x hx
    exact hEq x hx
  have haCenter : enorm (a - sigma) < r0 := by
    rw [<- hr0Eq]
    rw [Real.enorm_eq_ofReal_abs]
    rw [ENNReal.ofReal_lt_ofReal_iff hRPos]
    dsimp [a, eps]
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hdPos : 0 < d := by
    dsimp [d]
    positivity
  have hCross : sigma < a + d := by
    dsimp [a, d]
    linarith
  have hTarget : Membership.mem
      (Metric.eball a (r0 - enorm (a - sigma))) (a + d) := by
    rw [Metric.mem_eball, edist_dist]
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hdPos.le]
    rw [Real.enorm_eq_ofReal_abs]
    rw [abs_of_nonpos (by dsimp [a]; linarith : a - sigma <= 0)]
    rw [neg_sub]
    rw [<- hr0Eq, <- ENNReal.ofReal_sub R
      (by dsimp [a]; linarith : 0 <= sigma - a)]
    rw [ENNReal.ofReal_lt_ofReal_iff]
    . dsimp [a, d, eps]
      linarith
    . dsimp [a, eps]
      linarith
  have hStrict :=
    integrableExpSet_strict_crossing_of_analyticContinuationOnBall
      hX ha hSmallBall haCenter hEqNhd hdPos hCross hTarget
  exact Exists.intro (a + d) hStrict

end
end ProbabilityTheory

end

section
/- Source module Robin1984.Mathlib.NumberTheory.LSeries.RiemannZetaReal. -/
namespace RiemannZeta
open Filter MeasureTheory ProbabilityTheory Set
noncomputable section
end
end RiemannZeta

end

section
/- Source module Robin1984.NicolasLandau.NicolasOscillation. -/
namespace Robin1984
open Asymptotics Filter MeasureTheory Set
noncomputable section
end
end Robin1984

end

section
/- Source module Robin1984.NicolasLandau.NicolasLandau. -/
namespace Robin1984
open Asymptotics Filter MeasureTheory Set
noncomputable section
end
end Robin1984

end

section
/- Source module Robin1984.NicolasLandau.NicolasLandauPositiveTail. -/
namespace Robin1984
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
noncomputable section
def nicolasLandauRpowMellinContinuation (X b a : Real) : Real :=
  X ^ (a - b) / (b - a)

def nicolasJShiftedRealContinuation (a : Real) : Real :=
  Complex.re (integral (volume.restrict (Ioi (0 : Real)))
    (nicolasJMellinShiftIntegrand (a : Complex)))

theorem nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled s := by
  have hsZero : Not (s = 0) := by
    intro hZero
    rw [hZero] at hs
    norm_num at hs
  have hsOne : Not (s = 1) := by
    intro hOne
    rw [hOne] at hs
    norm_num at hs
  have hZeta : Not (riemannZeta s = 0) :=
    riemannZeta_ne_zero_of_one_lt_re hs
  have hFactor := nicolasZetaPoleFactor_ne_zero_of_zeta_ne_zero hsOne hZeta
  unfold nicolasPsiMellinTailContinuationFilled
  exact (nicolasPsiMellinContinuationFilled_analyticAt hsZero hFactor).sub
    (nicolasPsiMellinStartup_three_analyticAt s)

theorem norm_nicolasJShiftNumeratorFilled_le
    {u : Real} (hu : 1 < u) {z : Complex}
    (hz : Membership.mem (Metric.closedBall (0 : Complex) (1 / 4 : Real)) z) :
    norm (nicolasJShiftNumeratorFilled u z) <=
      3 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (1 / 4 : Real)) := by
  have hzNorm : norm z <= (1 / 4 : Real) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hzRe : z.re <= (1 / 4 : Real) :=
    (Complex.re_le_norm z).trans hzNorm
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs0 : 1 < s0.re := by
    dsimp [s0]
    linarith
  have hs1 : 1 < s1.re := by
    dsimp [s1, s0]
    linarith
  have hDen1 : (3 / 4 : Real) < s1.re - 1 := by
    dsimp [s1, s0]
    linarith
  have hShiftRaw := norm_nicolasPsiMellinTailContinuationFilled_le hs1
  have hShiftNumerator : (3 : Real) ^ (1 - s1.re) <=
      (3 : Real) ^ (-u + (1 / 4 : Real)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    dsimp [s1, s0]
    linarith
  have hShiftPowerNonneg : 0 <= (3 : Real) ^ (1 - s1.re) :=
    Real.rpow_nonneg (by norm_num) _
  have hShiftFraction : (3 : Real) ^ (1 - s1.re) / (s1.re - 1) <=
      2 * (3 : Real) ^ (-u + (1 / 4 : Real)) := by
    calc
      (3 : Real) ^ (1 - s1.re) / (s1.re - 1) <=
          (3 : Real) ^ (1 - s1.re) / (3 / 4 : Real) :=
        div_le_div_of_nonneg_left hShiftPowerNonneg (by norm_num) hDen1.le
      _ <= 2 * (3 : Real) ^ (1 - s1.re) := by
        nlinarith
      _ <= 2 * (3 : Real) ^ (-u + (1 / 4 : Real)) :=
        mul_le_mul_of_nonneg_left hShiftNumerator (by norm_num)
  have hShift : norm (nicolasPsiMellinTailContinuationFilled s1) <=
      2 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (1 / 4 : Real)) := by
    calc
      norm (nicolasPsiMellinTailContinuationFilled s1) <=
          (Real.log 4 + 5) *
            ((3 : Real) ^ (1 - s1.re) / (s1.re - 1)) := hShiftRaw
      _ <= (Real.log 4 + 5) *
          (2 * (3 : Real) ^ (-u + (1 / 4 : Real))) :=
        mul_le_mul_of_nonneg_left hShiftFraction (by positivity)
      _ = 2 * (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (1 / 4 : Real)) := by ring
  have hBaseRaw := norm_nicolasPsiMellinTailContinuationFilled_le hs0
  have hBase : norm (nicolasPsiMellinTailContinuationFilled s0) <=
      (Real.log 4 + 5) * (3 : Real) ^ (-u) := by
    have huPos : 0 < u := lt_trans zero_lt_one hu
    have hPowNonneg : 0 <= (3 : Real) ^ (-u) :=
      Real.rpow_nonneg (by norm_num) _
    have hS0Exponent : 1 - s0.re = -u := by
      dsimp [s0]
      ring
    have hS0Denominator : s0.re - 1 = u := by
      dsimp [s0]
      ring
    rw [hS0Exponent, hS0Denominator] at hBaseRaw
    calc
      norm (nicolasPsiMellinTailContinuationFilled s0) <=
          (Real.log 4 + 5) * ((3 : Real) ^ (-u) / u) := hBaseRaw
      _ <= (Real.log 4 + 5) * ((3 : Real) ^ (-u) / 1) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left hPowNonneg zero_lt_one hu.le)
          (by positivity)
      _ = (Real.log 4 + 5) * (3 : Real) ^ (-u) := by ring
  have hPowerNorm : norm ((3 : Complex) ^ z) =
      (3 : Real) ^ z.re := by
    change norm (((3 : Real) : Complex) ^ z) =
      (3 : Real) ^ z.re
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
  have hPowerProduct : norm ((3 : Complex) ^ z *
      nicolasPsiMellinTailContinuationFilled s0) <=
      (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (1 / 4 : Real)) := by
    rw [norm_mul, hPowerNorm]
    calc
      (3 : Real) ^ z.re *
          norm (nicolasPsiMellinTailContinuationFilled s0) <=
          (3 : Real) ^ z.re *
            ((Real.log 4 + 5) * (3 : Real) ^ (-u)) :=
        mul_le_mul_of_nonneg_left hBase
          (Real.rpow_nonneg (by norm_num) _)
      _ = (Real.log 4 + 5) *
          ((3 : Real) ^ z.re * (3 : Real) ^ (-u)) := by ring
      _ = (Real.log 4 + 5) * (3 : Real) ^ (z.re + (-u)) := by
        rw [Real.rpow_add (by norm_num : (0 : Real) < 3)]
      _ = (Real.log 4 + 5) * (3 : Real) ^ (z.re - u) := by
        congr 2
      _ <= (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (1 / 4 : Real)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith
  unfold nicolasJShiftNumeratorFilled
  change norm (nicolasPsiMellinTailContinuationFilled s1 -
      (3 : Complex) ^ z * nicolasPsiMellinTailContinuationFilled s0) <= _
  calc
    norm (nicolasPsiMellinTailContinuationFilled s1 -
        (3 : Complex) ^ z * nicolasPsiMellinTailContinuationFilled s0) <=
        norm (nicolasPsiMellinTailContinuationFilled s1) +
          norm ((3 : Complex) ^ z *
            nicolasPsiMellinTailContinuationFilled s0) := norm_sub_le _ _
    _ <= 2 * (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (1 / 4 : Real)) +
        (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (1 / 4 : Real)) :=
      add_le_add hShift hPowerProduct
    _ = 3 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (1 / 4 : Real)) := by ring

theorem nicolasJShiftNumeratorFilled_differentiableOn_quarter
    {u : Real} (hu : 1 < u) :
    DifferentiableOn Complex (nicolasJShiftNumeratorFilled u)
      (Metric.ball (0 : Complex) (1 / 4 : Real)) := by
  intro z hz
  have hzNorm : norm z < (1 / 4 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzRe : z.re < (1 / 4 : Real) :=
    (Complex.re_le_norm z).trans_lt hzNorm
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs1 : 1 < s1.re := by
    dsimp [s1, s0]
    linarith
  have hTail : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled s1 :=
    nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re hs1
  have hAffine : AnalyticAt Complex (fun w : Complex => s0 - w) z :=
    analyticAt_const.sub analyticAt_id
  have hShift : AnalyticAt Complex (fun w : Complex =>
      nicolasPsiMellinTailContinuationFilled (s0 - w)) z := by
    have hComp := hTail.comp_of_eq hAffine (by dsimp [s1])
    apply hComp.congr
    exact Eventually.of_forall (fun _ => rfl)
  have hPowerDifferentiable : Differentiable Complex
      (fun w : Complex => (3 : Complex) ^ w) := by
    intro w
    exact DifferentiableAt.const_cpow differentiableAt_id
      (Or.inl (by norm_num))
  have hPower : AnalyticAt Complex
      (fun w : Complex => (3 : Complex) ^ w) z :=
    hPowerDifferentiable.analyticAt z
  have hTailConst : AnalyticAt Complex (fun _ : Complex =>
      nicolasPsiMellinTailContinuationFilled s0) z := analyticAt_const
  unfold nicolasJShiftNumeratorFilled
  change DifferentiableWithinAt Complex (fun w : Complex =>
      nicolasPsiMellinTailContinuationFilled (s0 - w) -
        (3 : Complex) ^ w *
          nicolasPsiMellinTailContinuationFilled s0)
    (Metric.ball (0 : Complex) (1 / 4 : Real)) z
  exact (hShift.sub (hPower.mul hTailConst)).differentiableAt.differentiableWithinAt

theorem nicolasJShiftNumeratorFilled_analyticAt_zero
    {u : Real} (hu : 0 < u) :
    AnalyticAt Complex (nicolasJShiftNumeratorFilled u) 0 := by
  let s : Complex := ((u + 1 : Real) : Complex)
  have hs : 1 < s.re := by
    dsimp [s]
    simp
    linarith
  have hTail : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled s :=
    nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re hs
  have hAffine : AnalyticAt Complex (fun z : Complex => s - z) 0 :=
    analyticAt_const.sub analyticAt_id
  have hShift : AnalyticAt Complex
      (fun z : Complex =>
        nicolasPsiMellinTailContinuationFilled (s - z)) 0 :=
    by
      have hComp := hTail.comp_of_eq hAffine (by simp)
      apply hComp.congr
      exact Eventually.of_forall (fun _ => rfl)
  have hPowerDifferentiable : Differentiable Complex
      (fun z : Complex => (3 : Complex) ^ z) := by
    intro z
    exact DifferentiableAt.const_cpow differentiableAt_id
      (Or.inl (by norm_num))
  have hPower : AnalyticAt Complex
      (fun z : Complex => (3 : Complex) ^ z) 0 :=
    hPowerDifferentiable.analyticAt 0
  have hTailConst : AnalyticAt Complex
      (fun _ : Complex => nicolasPsiMellinTailContinuationFilled s) 0 :=
    analyticAt_const
  unfold nicolasJShiftNumeratorFilled
  change AnalyticAt Complex (fun z : Complex =>
    nicolasPsiMellinTailContinuationFilled (s - z) -
      (3 : Complex) ^ z * nicolasPsiMellinTailContinuationFilled s) 0
  exact hShift.sub (hPower.mul hTailConst)

theorem norm_nicolasJMellinShiftIntegrandFilled_le
    {u : Real} (hu : 1 < u) {z : Complex}
    (hz : Membership.mem (Metric.ball (0 : Complex) (1 / 4 : Real)) z) :
    norm (nicolasJMellinShiftIntegrandFilled z u) <=
      12 * (Real.log 4 + 5) * (u + 1) *
        (3 : Real) ^ (-u + (1 / 4 : Real)) := by
  let R : Real := 1 / 4
  let M : Real := 3 * (Real.log 4 + 5) *
    (3 : Real) ^ (-u + (1 / 4 : Real))
  have hMNonneg : 0 <= M := by
    dsimp [M]
    positivity
  have hMaps : MapsTo (nicolasJShiftNumeratorFilled u)
      (Metric.ball (0 : Complex) R)
      (Metric.closedBall (nicolasJShiftNumeratorFilled u 0) M) := by
    intro w hw
    rw [nicolasJShiftNumeratorFilled_zero]
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_nicolasJShiftNumeratorFilled_le hu
      (Metric.ball_subset_closedBall hw)
  have hDslope := Complex.norm_dslope_le_div_of_mapsTo_ball
    (nicolasJShiftNumeratorFilled_differentiableOn_quarter hu)
    hMaps hz
  have huOnePos : 0 < u + 1 := by linarith
  unfold nicolasJMellinShiftIntegrandFilled
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos huOnePos]
  calc
    (u + 1) * norm (dslope (nicolasJShiftNumeratorFilled u) 0 z) <=
        (u + 1) * (M / R) :=
      mul_le_mul_of_nonneg_left hDslope huOnePos.le
    _ = 12 * (Real.log 4 + 5) * (u + 1) *
        (3 : Real) ^ (-u + (1 / 4 : Real)) := by
      dsimp [M, R]
      ring

def nicolasJLargeMajorant (u : Real) : Real :=
  12 * (Real.log 4 + 5) * (u + 1) *
    (3 : Real) ^ (-u + (1 / 4 : Real))

theorem nicolasJLargeMajorant_integrableOn :
    IntegrableOn nicolasJLargeMajorant (Ioi (1 : Real)) := by
  have hLog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hExp : IntegrableOn
      (fun u : Real => Real.exp (-(Real.log 3) * u))
      (Ioi (1 : Real)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : Real)) (s := (0 : Real)) (b := Real.log 3)
      (by norm_num) (by norm_num) hLog
    have hSubset : Ioi (1 : Real) <= Ioi (0 : Real) := by
      intro u hu
      exact zero_lt_one.trans (mem_Ioi.mp hu)
    apply (h.mono_set hSubset).congr_fun _ measurableSet_Ioi
    intro u hu
    simp
  have hUExp : IntegrableOn
      (fun u : Real => u * Real.exp (-(Real.log 3) * u))
      (Ioi (1 : Real)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : Real)) (s := (1 : Real)) (b := Real.log 3)
      (by norm_num) (by norm_num) hLog
    have hSubset : Ioi (1 : Real) <= Ioi (0 : Real) := by
      intro u hu
      exact zero_lt_one.trans (mem_Ioi.mp hu)
    apply (h.mono_set hSubset).congr_fun _ measurableSet_Ioi
    intro u hu
    simp
  have hLinear : IntegrableOn
      (fun u : Real => (u + 1) * Real.exp (-(Real.log 3) * u))
      (Ioi (1 : Real)) := by
    apply (hUExp.add hExp).congr_fun _ measurableSet_Ioi
    intro u hu
    change u * Real.exp (-(Real.log 3) * u) +
      Real.exp (-(Real.log 3) * u) =
        (u + 1) * Real.exp (-(Real.log 3) * u)
    ring
  have hScaled : IntegrableOn
      (fun u : Real =>
        (12 * (Real.log 4 + 5) * Real.exp (Real.log 3 / 4)) *
          ((u + 1) * Real.exp (-(Real.log 3) * u)))
      (Ioi (1 : Real)) :=
    hLinear.const_mul
      (12 * (Real.log 4 + 5) * Real.exp (Real.log 3 / 4))
  apply hScaled.congr_fun _ measurableSet_Ioi
  intro u hu
  unfold nicolasJLargeMajorant
  rw [Real.rpow_def_of_pos (by norm_num : (0 : Real) < 3)]
  rw [show Real.log 3 * (-u + (1 / 4 : Real)) =
      Real.log 3 / 4 + (-(Real.log 3) * u) by ring]
  rw [Real.exp_add]
  ring

theorem nicolasJMellinShiftIntegrandFilled_analyticAt_zero
    {u : Real} (hu : 0 < u) :
    AnalyticAt Complex (fun z : Complex =>
      nicolasJMellinShiftIntegrandFilled z u) 0 := by
  have hNumerator := nicolasJShiftNumeratorFilled_analyticAt_zero hu
  have hPunctured : Filter.Eventually
      (fun z : Complex => DifferentiableAt Complex
        (dslope (nicolasJShiftNumeratorFilled u) 0) z)
      (nhdsWithin 0 (Set.compl {(0 : Complex)})) := by
    filter_upwards
        [hNumerator.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
          self_mem_nhdsWithin] with z hzAnalytic hzNe
    exact (differentiableAt_dslope_of_ne
      (Set.mem_compl_singleton_iff.mp hzNe)).2 hzAnalytic.differentiableAt
  have hDslopeContinuous : ContinuousAt
      (dslope (nicolasJShiftNumeratorFilled u) 0) 0 :=
    continuousAt_dslope_same.2 hNumerator.differentiableAt
  have hDslope : AnalyticAt Complex
      (dslope (nicolasJShiftNumeratorFilled u) 0) 0 :=
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      hPunctured hDslopeContinuous
  unfold nicolasJMellinShiftIntegrandFilled
  exact analyticAt_const.mul hDslope

theorem nicolasJMellinShiftIntegrandFilled_differentiableOn_quarter
    {u : Real} (hu : 1 < u) :
    DifferentiableOn Complex
      (fun z : Complex => nicolasJMellinShiftIntegrandFilled z u)
      (Metric.ball (0 : Complex) (1 / 4 : Real)) := by
  intro z hz
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact (nicolasJMellinShiftIntegrandFilled_analyticAt_zero
      (by linarith)).differentiableAt.differentiableWithinAt
  case neg =>
    have hNumeratorAt : DifferentiableAt Complex
        (nicolasJShiftNumeratorFilled u) z :=
      (nicolasJShiftNumeratorFilled_differentiableOn_quarter hu z hz).differentiableAt
        (Metric.isOpen_ball.mem_nhds hz)
    have hDslopeAt : DifferentiableAt Complex
        (dslope (nicolasJShiftNumeratorFilled u) 0) z :=
      (differentiableAt_dslope_of_ne hzZero).2 hNumeratorAt
    unfold nicolasJMellinShiftIntegrandFilled
    exact (analyticAt_const.differentiableAt.mul hDslopeAt).differentiableWithinAt

theorem norm_deriv_nicolasJMellinShiftIntegrandFilled_le
    {u : Real} (hu : 1 < u) {z : Complex}
    (hz : Membership.mem (Metric.ball (0 : Complex) (1 / 8 : Real)) z) :
    norm (deriv (fun w : Complex =>
      nicolasJMellinShiftIntegrandFilled w u) z) <=
      16 * nicolasJLargeMajorant u := by
  let f : Complex -> Complex := fun w : Complex =>
    nicolasJMellinShiftIntegrandFilled w u
  let R : Real := 1 / 8
  let M : Real := nicolasJLargeMajorant u
  have hSmallSubset : Metric.ball z R <=
      Metric.ball (0 : Complex) (1 / 4 : Real) := by
    intro w hw
    rw [Metric.mem_ball] at hw hz
    rw [Metric.mem_ball]
    calc
      dist w 0 <= dist w z + dist z 0 := dist_triangle w z 0
      _ < (1 / 8 : Real) + (1 / 8 : Real) := add_lt_add hw hz
      _ = (1 / 4 : Real) := by norm_num
  have hzQuarter : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z := by
    apply hSmallSubset
    exact Metric.mem_ball_self (by norm_num)
  have hDiff : DifferentiableOn Complex f (Metric.ball z R) :=
    (nicolasJMellinShiftIntegrandFilled_differentiableOn_quarter hu).mono
      hSmallSubset
  have hMaps : MapsTo f (Metric.ball z R)
      (Metric.closedBall (f z) (2 * M)) := by
    intro w hw
    have hwQuarter := hSmallSubset hw
    have hwBound : norm (f w) <= M := by
      dsimp [f, M]
      simpa [nicolasJLargeMajorant] using
        norm_nicolasJMellinShiftIntegrandFilled_le hu hwQuarter
    have hzBound : norm (f z) <= M := by
      dsimp [f, M]
      simpa [nicolasJLargeMajorant] using
        norm_nicolasJMellinShiftIntegrandFilled_le hu hzQuarter
    rw [Metric.mem_closedBall]
    calc
      dist (f w) (f z) <= norm (f w) + norm (f z) := by
        simpa [dist_eq_norm] using norm_sub_le (f w) (f z)
      _ <= M + M := add_le_add hwBound hzBound
      _ = 2 * M := by ring
  have hCauchy := Complex.norm_deriv_le_div_of_mapsTo_ball
    hDiff hMaps (by norm_num : 0 < R)
  change norm (deriv f z) <= 16 * M
  calc
    norm (deriv f z) <= (2 * M) / R := hCauchy
    _ = 16 * M := by
      dsimp [R]
      ring

theorem nicolasJShiftNumeratorFilled_continuousOn_u
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z) :
    ContinuousOn (fun u : Real => nicolasJShiftNumeratorFilled u z)
      (Ioi (1 : Real)) := by
  let s0 : Real -> Complex := fun u : Real => ((u + 1 : Real) : Complex)
  let s1 : Real -> Complex := fun u : Real => s0 u - z
  have hS0 : Continuous s0 := by
    dsimp [s0]
    fun_prop
  have hS1 : Continuous s1 := by
    dsimp [s1]
    exact hS0.sub continuous_const
  intro u hu
  have huOne : 1 < u := mem_Ioi.mp hu
  have hzNorm : norm z < (1 / 4 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzRe : z.re < (1 / 4 : Real) :=
    (Complex.re_le_norm z).trans_lt hzNorm
  have hs0 : 1 < (s0 u).re := by
    dsimp [s0]
    linarith
  have hs1 : 1 < (s1 u).re := by
    dsimp [s1, s0]
    linarith
  have hTail0 : ContinuousAt (fun v : Real =>
      nicolasPsiMellinTailContinuationFilled (s0 v)) u :=
    (nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re hs0).continuousAt.comp
      hS0.continuousAt
  have hTail1 : ContinuousAt (fun v : Real =>
      nicolasPsiMellinTailContinuationFilled (s1 v)) u :=
    (nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re hs1).continuousAt.comp
      hS1.continuousAt
  unfold nicolasJShiftNumeratorFilled
  change ContinuousWithinAt (fun v : Real =>
    nicolasPsiMellinTailContinuationFilled (s1 v) -
      (3 : Complex) ^ z *
        nicolasPsiMellinTailContinuationFilled (s0 v))
    (Ioi (1 : Real)) u
  exact (hTail1.sub (continuousAt_const.mul hTail0)).continuousWithinAt

theorem nicolasJMellinShiftIntegrandFilled_continuousOn_u_of_ne
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z)
    (hzZero : Not (z = 0)) :
    ContinuousOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
  have hNumeratorZ := nicolasJShiftNumeratorFilled_continuousOn_u hz
  have hZeroMem : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) (0 : Complex) :=
    Metric.mem_ball_self (by norm_num)
  have hNumeratorZero :=
    nicolasJShiftNumeratorFilled_continuousOn_u hZeroMem
  have hU : Continuous (fun u : Real => ((u + 1 : Real) : Complex)) := by
    fun_prop
  have hInv : Continuous (fun _ : Real => Inv.inv (z - 0)) :=
    continuous_const
  have hEq : (fun u : Real => nicolasJMellinShiftIntegrandFilled z u) =
      (fun u : Real => ((u + 1 : Real) : Complex) *
        Inv.inv (z - 0) *
          (nicolasJShiftNumeratorFilled u z -
            nicolasJShiftNumeratorFilled u 0)) := by
    funext u
    unfold nicolasJMellinShiftIntegrandFilled
    rw [dslope_of_ne _ hzZero]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub]
    ring
  rw [hEq]
  exact (hU.continuousOn.mul hInv.continuousOn).mul
    (hNumeratorZ.sub hNumeratorZero)

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_of_ne
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z)
    (hzZero : Not (z = 0)) :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (volume.restrict (Ioi (1 : Real))) :=
  (nicolasJMellinShiftIntegrandFilled_continuousOn_u_of_ne
    hz hzZero).aestronglyMeasurable measurableSet_Ioi

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_zero :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled 0 u)
      (volume.restrict (Ioi (1 : Real))) := by
  let zseq : Nat -> Complex := fun n : Nat =>
    (((1 : Real) / (8 * ((n : Real) + 1)) : Real) : Complex)
  have hZPos : forall n : Nat,
      0 < (1 : Real) / (8 * ((n : Real) + 1)) := by
    intro n
    positivity
  have hZMem : forall n : Nat, Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) (zseq n) := by
    intro n
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [zseq]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hZPos n)]
    have hn : 0 <= (n : Real) := by positivity
    apply one_div_lt_one_div_of_lt (by norm_num : (0 : Real) < 4)
    nlinarith
  have hZNe : forall n : Nat, Not (zseq n = 0) := by
    intro n
    dsimp [zseq]
    exact Complex.ofReal_ne_zero.mpr
      (div_ne_zero (by norm_num) (by positivity))
  have hRecip : Tendsto
      (fun n : Nat => (1 : Real) / ((n : Real) + 1))
      atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hScaled : Tendsto
      (fun n : Nat => (1 / 8 : Real) *
        ((1 : Real) / ((n : Real) + 1)))
      atTop (nhds ((1 / 8 : Real) * 0)) :=
    tendsto_const_nhds.mul hRecip
  have hReal : Tendsto
      (fun n : Nat => (1 : Real) / (8 * ((n : Real) + 1)))
      atTop (nhds 0) := by
    have hFunctions :
        (fun n : Nat => (1 : Real) / (8 * ((n : Real) + 1))) =
          (fun n : Nat => (1 / 8 : Real) *
            ((1 : Real) / ((n : Real) + 1))) := by
      funext n
      field_simp
    rw [hFunctions]
    simpa using hScaled
  have hZ : Tendsto zseq atTop (nhds (0 : Complex)) := by
    have hCast := Complex.continuous_ofReal.continuousAt.tendsto.comp hReal
    change Tendsto
      (fun n : Nat =>
        (((1 : Real) / (8 * ((n : Real) + 1)) : Real) : Complex))
      atTop (nhds (0 : Complex)) at hCast
    change Tendsto
      (fun n : Nat =>
        (((1 : Real) / (8 * ((n : Real) + 1)) : Real) : Complex))
      atTop (nhds (0 : Complex))
    exact hCast
  have hMeas : forall n : Nat, AEMeasurable
      (fun u : Real => nicolasJMellinShiftIntegrandFilled (zseq n) u)
      (volume.restrict (Ioi (1 : Real))) := by
    intro n
    exact (nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_of_ne
      (hZMem n) (hZNe n)).aemeasurable
  have hTendsto : Filter.Eventually
      (fun u : Real => Tendsto
        (fun n : Nat => nicolasJMellinShiftIntegrandFilled (zseq n) u)
        atTop (nhds (nicolasJMellinShiftIntegrandFilled 0 u)))
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have huPos : 0 < u := zero_lt_one.trans hu
    exact (nicolasJMellinShiftIntegrandFilled_analyticAt_zero
      huPos).continuousAt.tendsto.comp hZ
  exact (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z) :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (volume.restrict (Ioi (1 : Real))) := by
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_zero
  case neg =>
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_of_ne
      hz hzZero

theorem nicolasJMellinShiftIntegrandFilled_integrableOn_large
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 8 : Real)) z) :
    IntegrableOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
  have hzQuarter : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z := by
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  apply Integrable.mono' nicolasJLargeMajorant_integrableOn
    (nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable hzQuarter)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simpa [nicolasJLargeMajorant] using
    norm_nicolasJMellinShiftIntegrandFilled_le (mem_Ioi.mp hu) hzQuarter

def nicolasJLargeDerivativeMajorant (u : Real) : Real :=
  16 * nicolasJLargeMajorant u

theorem nicolasJLargeDerivativeMajorant_integrableOn :
    IntegrableOn nicolasJLargeDerivativeMajorant (Ioi (1 : Real)) := by
  unfold nicolasJLargeDerivativeMajorant
  exact nicolasJLargeMajorant_integrableOn.const_mul 16

theorem deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 8 : Real)) z) :
    AEStronglyMeasurable (fun u : Real =>
      deriv (fun w : Complex =>
        nicolasJMellinShiftIntegrandFilled w u) z)
      (volume.restrict (Ioi (1 : Real))) := by
  let slopeSeq : Nat -> Real -> Complex := fun n : Nat => fun u : Real =>
    slope (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u)
      z (z + nicolasJDerivativeStep n)
  have hzNorm : norm z < (1 / 8 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzQuarter : Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real)) z := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hShiftQuarter : forall n : Nat, Membership.mem
      (Metric.ball (0 : Complex) (1 / 4 : Real))
      (z + nicolasJDerivativeStep n) := by
    intro n
    rw [Metric.mem_ball, dist_zero_right]
    calc
      norm (z + nicolasJDerivativeStep n) <=
          norm z + norm (nicolasJDerivativeStep n) := norm_add_le _ _
      _ < (1 / 8 : Real) + (1 / 8 : Real) :=
        add_lt_add_of_lt_of_le hzNorm (norm_nicolasJDerivativeStep_lt n)
      _ = (1 / 4 : Real) := by norm_num
  have hMeas : forall n : Nat, AEMeasurable (slopeSeq n)
      (volume.restrict (Ioi (1 : Real))) := by
    intro n
    have hShift :=
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable
        (hShiftQuarter n)
    have hBase :=
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable hzQuarter
    have hEq : slopeSeq n = fun u : Real =>
        Inv.inv ((z + nicolasJDerivativeStep n) - z) *
          (nicolasJMellinShiftIntegrandFilled
              (z + nicolasJDerivativeStep n) u -
            nicolasJMellinShiftIntegrandFilled z u) := by
      funext u
      dsimp [slopeSeq]
      unfold slope
      simp only [smul_eq_mul, vsub_eq_sub]
    rw [hEq]
    exact ((hShift.sub hBase).const_mul
      (Inv.inv ((z + nicolasJDerivativeStep n) - z))).aemeasurable
  have hStepWithin : Tendsto nicolasJDerivativeStep atTop
      (nhdsWithin (0 : Complex) (Set.compl {(0 : Complex)})) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact And.intro nicolasJDerivativeStep_tendsto_zero
      (Eventually.of_forall (fun n : Nat =>
        Set.mem_compl_singleton_iff.mpr
          (nicolasJDerivativeStep_ne_zero n)))
  have hTendsto : Filter.Eventually
      (fun u : Real => Tendsto (fun n : Nat => slopeSeq n u) atTop
        (nhds (deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)))
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have huOne : 1 < u := mem_Ioi.mp hu
    have hDiffAt : DifferentiableAt Complex
        (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u) z :=
      (nicolasJMellinShiftIntegrandFilled_differentiableOn_quarter
        huOne z hzQuarter).differentiableAt
          (Metric.isOpen_ball.mem_nhds hzQuarter)
    have hSlope := hDiffAt.hasDerivAt.tendsto_slope_zero.comp hStepWithin
    change Tendsto (fun n : Nat =>
      Inv.inv (nicolasJDerivativeStep n) *
        (nicolasJMellinShiftIntegrandFilled
            (z + nicolasJDerivativeStep n) u -
          nicolasJMellinShiftIntegrandFilled z u))
      atTop (nhds (deriv (fun w : Complex =>
        nicolasJMellinShiftIntegrandFilled w u) z)) at hSlope
    dsimp [slopeSeq]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub, add_sub_cancel_left]
    exact hSlope
  exact (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable

theorem nicolasJShiftedComplexContinuationFilledLarge_hasDerivAt
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 8 : Real)) z) :
    HasDerivAt nicolasJShiftedComplexContinuationFilledLarge
      (integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
        deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)) z := by
  let s : Set Complex := Metric.ball (0 : Complex) (1 / 8 : Real)
  let F : Complex -> Real -> Complex := fun w : Complex => fun u : Real =>
    nicolasJMellinShiftIntegrandFilled w u
  let F' : Complex -> Real -> Complex := fun w : Complex => fun u : Real =>
    deriv (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w
  have hsNhd : Membership.mem (nhds z) s := by
    dsimp [s]
    exact Metric.isOpen_ball.mem_nhds hz
  have hFMeas : Filter.Eventually
      (fun w : Complex => AEStronglyMeasurable (F w)
        (volume.restrict (Ioi (1 : Real)))) (nhds z) := by
    filter_upwards [hsNhd] with w hw
    have hwQuarter : Membership.mem
        (Metric.ball (0 : Complex) (1 / 4 : Real)) w := by
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable
      hwQuarter
  have hFInt : Integrable (F z)
      (volume.restrict (Ioi (1 : Real))) := by
    exact nicolasJMellinShiftIntegrandFilled_integrableOn_large hz
  have hF'Meas : AEStronglyMeasurable (F' z)
      (volume.restrict (Ioi (1 : Real))) := by
    exact deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable hz
  have hBound : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        norm (F' w u) <= nicolasJLargeDerivativeMajorant u)
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    dsimp [F', s]
    unfold nicolasJLargeDerivativeMajorant
    exact norm_deriv_nicolasJMellinShiftIntegrandFilled_le
      (mem_Ioi.mp hu) hw
  have hDiff : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        HasDerivAt (fun v : Complex => F v u) (F' w u) w)
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    have hwQuarter : Membership.mem
        (Metric.ball (0 : Complex) (1 / 4 : Real)) w := by
      dsimp [s] at hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have hAt : DifferentiableAt Complex
        (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w :=
      (nicolasJMellinShiftIntegrandFilled_differentiableOn_quarter
        (mem_Ioi.mp hu) w hwQuarter).differentiableAt
          (Metric.isOpen_ball.mem_nhds hwQuarter)
    dsimp [F, F']
    exact hAt.hasDerivAt
  have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := nicolasJLargeDerivativeMajorant)
    hsNhd hFMeas hFInt hF'Meas hBound
    nicolasJLargeDerivativeMajorant_integrableOn hDiff
  unfold nicolasJShiftedComplexContinuationFilledLarge
  simpa [F, F'] using hMain.2

theorem nicolasJShiftedComplexContinuationFilledLarge_differentiableOn :
    DifferentiableOn Complex nicolasJShiftedComplexContinuationFilledLarge
      (Metric.ball (0 : Complex) (1 / 8 : Real)) := by
  intro z hz
  exact (nicolasJShiftedComplexContinuationFilledLarge_hasDerivAt
    hz).differentiableAt.differentiableWithinAt

theorem exists_nicolasPsiMellinTailContinuationFilled_analytic_ball_one :
    Exists fun r : Real => And (0 < r)
      (forall s : Complex, Membership.mem
        (Metric.ball (1 : Complex) r) s ->
          AnalyticAt Complex nicolasPsiMellinTailContinuationFilled s) := by
  have hEventually :=
    nicolasPsiMellinTailContinuationFilled_analyticAt_one.eventually_analyticAt
  choose r hrPos hrSubset using Metric.mem_nhds_iff.1 hEventually
  refine Exists.intro r (And.intro hrPos ?_)
  intro s hs
  exact hrSubset hs

def nicolasJShiftedRealContinuationFilled (a : Real) : Real :=
  Complex.re (nicolasJShiftedComplexContinuationFilled (a : Complex))

theorem nicolasJShiftedRealContinuationFilled_eq_raw
    {a : Real} (ha : a < 0) :
    nicolasJShiftedRealContinuationFilled a =
      nicolasJShiftedRealContinuation a := by
  unfold nicolasJShiftedRealContinuationFilled
    nicolasJShiftedComplexContinuationFilled
    nicolasJShiftedRealContinuation
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  exact nicolasJMellinShiftIntegrandFilled_eq_raw
    (by simpa using ha) hu

theorem nicolasLandauRpowTailMellin_eq_continuation
    {X b a : Real} (hX : 0 < X) (ha : a < b) :
    integral (volume.restrict (Ioi X)) (fun x : Real =>
        x ^ (a - 1) * x ^ (-b)) =
      nicolasLandauRpowMellinContinuation X b a := by
  calc
    integral (volume.restrict (Ioi X)) (fun x : Real =>
        x ^ (a - 1) * x ^ (-b)) =
        integral (volume.restrict (Ioi X)) (fun x : Real =>
          x ^ (a - b - 1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hxPos : 0 < x := hX.trans hx
      change x ^ (a - 1) * x ^ (-b) = x ^ (a - b - 1)
      rw [<- Real.rpow_add hxPos]
      congr 1
      ring
    _ = -X ^ (a - b - 1 + 1) / (a - b - 1 + 1) := by
      exact integral_Ioi_rpow_of_lt (by linarith) hX
    _ = nicolasLandauRpowMellinContinuation X b a := by
      unfold nicolasLandauRpowMellinContinuation
      have hab : Not (a - b = 0) := sub_ne_zero.mpr (ne_of_lt ha)
      have hba : Not (b - a = 0) := sub_ne_zero.mpr (Ne.symm (ne_of_lt ha))
      rw [show a - b - 1 + 1 = a - b by ring]
      field_simp [hab, hba]
      ring

theorem nicolasLandauRpowMellinContinuation_analyticAt
    {X b sigma : Real} (hX : 0 < X) (hSigma : sigma < b) :
    AnalyticAt Real (nicolasLandauRpowMellinContinuation X b) sigma := by
  have hFunction : nicolasLandauRpowMellinContinuation X b =
      fun a : Real => Real.exp (Real.log X * (a - b)) / (b - a) := by
    funext a
    unfold nicolasLandauRpowMellinContinuation
    rw [Real.rpow_def_of_pos hX]
  rw [hFunction]
  have hNumerator : AnalyticAt Real
      (fun a : Real => Real.exp (Real.log X * (a - b))) sigma := by
    fun_prop
  have hDenominator : AnalyticAt Real (fun a : Real => b - a) sigma := by
    fun_prop
  exact hNumerator.div hDenominator (sub_ne_zero.mpr (ne_of_gt hSigma))

end
end Robin1984

end

section
/- Source module Robin1984.Analytic.RiemannZetaRealNonzero. -/
namespace Robin1984
open Filter MeasureTheory Set
noncomputable section
theorem norm_nicolasJShiftNumeratorFilled_le_threeQuarter
    {u : Real} (hu : 1 < u) {z : Complex}
    (hz : Membership.mem (Metric.closedBall (0 : Complex) (3 / 4 : Real)) z) :
    norm (nicolasJShiftNumeratorFilled u z) <=
      5 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
  have hzNorm : norm z <= (3 / 4 : Real) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hzRe : z.re <= (3 / 4 : Real) :=
    (Complex.re_le_norm z).trans hzNorm
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs0 : 1 < s0.re := by
    dsimp [s0]
    linarith
  have hs1 : 1 < s1.re := by
    dsimp [s1, s0]
    linarith
  have hDen1 : (1 / 4 : Real) < s1.re - 1 := by
    dsimp [s1, s0]
    linarith
  have hShiftRaw := norm_nicolasPsiMellinTailContinuationFilled_le hs1
  have hShiftNumerator : (3 : Real) ^ (1 - s1.re) <=
      (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    dsimp [s1, s0]
    linarith
  have hShiftPowerNonneg : 0 <= (3 : Real) ^ (1 - s1.re) :=
    Real.rpow_nonneg (by norm_num) _
  have hShiftFraction : (3 : Real) ^ (1 - s1.re) / (s1.re - 1) <=
      4 * (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    calc
      (3 : Real) ^ (1 - s1.re) / (s1.re - 1) <=
          (3 : Real) ^ (1 - s1.re) / (1 / 4 : Real) :=
        div_le_div_of_nonneg_left hShiftPowerNonneg (by norm_num) hDen1.le
      _ = 4 * (3 : Real) ^ (1 - s1.re) := by ring
      _ <= 4 * (3 : Real) ^ (-u + (3 / 4 : Real)) :=
        mul_le_mul_of_nonneg_left hShiftNumerator (by norm_num)
  have hShift : norm (nicolasPsiMellinTailContinuationFilled s1) <=
      4 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    calc
      norm (nicolasPsiMellinTailContinuationFilled s1) <=
          (Real.log 4 + 5) *
            ((3 : Real) ^ (1 - s1.re) / (s1.re - 1)) := hShiftRaw
      _ <= (Real.log 4 + 5) *
          (4 * (3 : Real) ^ (-u + (3 / 4 : Real))) :=
        mul_le_mul_of_nonneg_left hShiftFraction (by positivity)
      _ = 4 * (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) := by ring
  have hBaseRaw := norm_nicolasPsiMellinTailContinuationFilled_le hs0
  have hBase : norm (nicolasPsiMellinTailContinuationFilled s0) <=
      (Real.log 4 + 5) * (3 : Real) ^ (-u) := by
    have huPos : 0 < u := lt_trans zero_lt_one hu
    have hPowNonneg : 0 <= (3 : Real) ^ (-u) :=
      Real.rpow_nonneg (by norm_num) _
    have hS0Exponent : 1 - s0.re = -u := by
      dsimp [s0]
      ring
    have hS0Denominator : s0.re - 1 = u := by
      dsimp [s0]
      ring
    rw [hS0Exponent, hS0Denominator] at hBaseRaw
    calc
      norm (nicolasPsiMellinTailContinuationFilled s0) <=
          (Real.log 4 + 5) * ((3 : Real) ^ (-u) / u) := hBaseRaw
      _ <= (Real.log 4 + 5) * ((3 : Real) ^ (-u) / 1) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left hPowNonneg zero_lt_one hu.le)
          (by positivity)
      _ = (Real.log 4 + 5) * (3 : Real) ^ (-u) := by ring
  have hPowerNorm : norm ((3 : Complex) ^ z) =
      (3 : Real) ^ z.re := by
    change norm (((3 : Real) : Complex) ^ z) =
      (3 : Real) ^ z.re
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
  have hPowerProduct : norm ((3 : Complex) ^ z *
      nicolasPsiMellinTailContinuationFilled s0) <=
      (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    rw [norm_mul, hPowerNorm]
    calc
      (3 : Real) ^ z.re *
          norm (nicolasPsiMellinTailContinuationFilled s0) <=
          (3 : Real) ^ z.re *
            ((Real.log 4 + 5) * (3 : Real) ^ (-u)) :=
        mul_le_mul_of_nonneg_left hBase
          (Real.rpow_nonneg (by norm_num) _)
      _ = (Real.log 4 + 5) *
          ((3 : Real) ^ z.re * (3 : Real) ^ (-u)) := by ring
      _ = (Real.log 4 + 5) * (3 : Real) ^ (z.re + (-u)) := by
        rw [Real.rpow_add (by norm_num : (0 : Real) < 3)]
      _ = (Real.log 4 + 5) * (3 : Real) ^ (z.re - u) := by
        congr 2
      _ <= (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith
  unfold nicolasJShiftNumeratorFilled
  change norm (nicolasPsiMellinTailContinuationFilled s1 -
      (3 : Complex) ^ z * nicolasPsiMellinTailContinuationFilled s0) <= _
  calc
    norm (nicolasPsiMellinTailContinuationFilled s1 -
        (3 : Complex) ^ z * nicolasPsiMellinTailContinuationFilled s0) <=
        norm (nicolasPsiMellinTailContinuationFilled s1) +
          norm ((3 : Complex) ^ z *
            nicolasPsiMellinTailContinuationFilled s0) := norm_sub_le _ _
    _ <= 4 * (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) +
        (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) :=
      add_le_add hShift hPowerProduct
    _ = 5 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by ring

theorem nicolasJShiftNumeratorFilled_differentiableOn_threeQuarter
    {u : Real} (hu : 1 < u) :
    DifferentiableOn Complex (nicolasJShiftNumeratorFilled u)
      (Metric.ball (0 : Complex) (3 / 4 : Real)) := by
  intro z hz
  have hzNorm : norm z < (3 / 4 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzRe : z.re < (3 / 4 : Real) :=
    (Complex.re_le_norm z).trans_lt hzNorm
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs1 : 1 < s1.re := by
    dsimp [s1, s0]
    linarith
  have hTail : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled s1 :=
    nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re hs1
  have hAffine : AnalyticAt Complex (fun w : Complex => s0 - w) z :=
    analyticAt_const.sub analyticAt_id
  have hShift : AnalyticAt Complex (fun w : Complex =>
      nicolasPsiMellinTailContinuationFilled (s0 - w)) z := by
    have hComp := hTail.comp_of_eq hAffine (by dsimp [s1])
    apply hComp.congr
    exact Eventually.of_forall (fun _ => rfl)
  have hPowerDifferentiable : Differentiable Complex
      (fun w : Complex => (3 : Complex) ^ w) := by
    intro w
    exact DifferentiableAt.const_cpow differentiableAt_id
      (Or.inl (by norm_num))
  have hPower : AnalyticAt Complex
      (fun w : Complex => (3 : Complex) ^ w) z :=
    hPowerDifferentiable.analyticAt z
  have hTailConst : AnalyticAt Complex (fun _ : Complex =>
      nicolasPsiMellinTailContinuationFilled s0) z := analyticAt_const
  unfold nicolasJShiftNumeratorFilled
  change DifferentiableWithinAt Complex (fun w : Complex =>
      nicolasPsiMellinTailContinuationFilled (s0 - w) -
        (3 : Complex) ^ w *
          nicolasPsiMellinTailContinuationFilled s0)
    (Metric.ball (0 : Complex) (3 / 4 : Real)) z
  exact (hShift.sub (hPower.mul hTailConst)).differentiableAt.differentiableWithinAt

theorem norm_nicolasJMellinShiftIntegrandFilled_le_threeQuarter
    {u : Real} (hu : 1 < u) {z : Complex}
    (hz : Membership.mem (Metric.ball (0 : Complex) (3 / 4 : Real)) z) :
    norm (nicolasJMellinShiftIntegrandFilled z u) <=
      (20 / 3 : Real) * (Real.log 4 + 5) * (u + 1) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
  let R : Real := 3 / 4
  let M : Real := 5 * (Real.log 4 + 5) *
    (3 : Real) ^ (-u + (3 / 4 : Real))
  have hMaps : MapsTo (nicolasJShiftNumeratorFilled u)
      (Metric.ball (0 : Complex) R)
      (Metric.closedBall (nicolasJShiftNumeratorFilled u 0) M) := by
    intro w hw
    rw [nicolasJShiftNumeratorFilled_zero]
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_nicolasJShiftNumeratorFilled_le_threeQuarter hu
      (Metric.ball_subset_closedBall hw)
  have hDslope := Complex.norm_dslope_le_div_of_mapsTo_ball
    (nicolasJShiftNumeratorFilled_differentiableOn_threeQuarter hu)
    hMaps hz
  have huOnePos : 0 < u + 1 := by linarith
  unfold nicolasJMellinShiftIntegrandFilled
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos huOnePos]
  calc
    (u + 1) * norm (dslope (nicolasJShiftNumeratorFilled u) 0 z) <=
        (u + 1) * (M / R) :=
      mul_le_mul_of_nonneg_left hDslope huOnePos.le
    _ = (20 / 3 : Real) * (Real.log 4 + 5) * (u + 1) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
      dsimp [M, R]
      ring

theorem nicolasJMellinShiftIntegrandFilled_differentiableOn_threeQuarter
    {u : Real} (hu : 1 < u) :
    DifferentiableOn Complex
      (fun z : Complex => nicolasJMellinShiftIntegrandFilled z u)
      (Metric.ball (0 : Complex) (3 / 4 : Real)) := by
  intro z hz
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact (nicolasJMellinShiftIntegrandFilled_analyticAt_zero
      (by linarith)).differentiableAt.differentiableWithinAt
  case neg =>
    have hNumeratorAt : DifferentiableAt Complex
        (nicolasJShiftNumeratorFilled u) z :=
      (nicolasJShiftNumeratorFilled_differentiableOn_threeQuarter
        hu z hz).differentiableAt
        (Metric.isOpen_ball.mem_nhds hz)
    have hDslopeAt : DifferentiableAt Complex
        (dslope (nicolasJShiftNumeratorFilled u) 0) z :=
      (differentiableAt_dslope_of_ne hzZero).2 hNumeratorAt
    unfold nicolasJMellinShiftIntegrandFilled
    exact (analyticAt_const.differentiableAt.mul hDslopeAt).differentiableWithinAt

theorem norm_deriv_nicolasJMellinShiftIntegrandFilled_le_half
    {u : Real} (hu : 1 < u) {z : Complex}
    (hz : Membership.mem (Metric.ball (0 : Complex) (1 / 2 : Real)) z) :
    norm (deriv (fun w : Complex =>
      nicolasJMellinShiftIntegrandFilled w u) z) <=
      8 * nicolasJLargeMajorantHalf u := by
  let f : Complex -> Complex := fun w : Complex =>
    nicolasJMellinShiftIntegrandFilled w u
  let R : Real := 1 / 4
  let M : Real := nicolasJLargeMajorantHalf u
  have hSmallSubset : Metric.ball z R <=
      Metric.ball (0 : Complex) (3 / 4 : Real) := by
    intro w hw
    rw [Metric.mem_ball] at hw hz
    rw [Metric.mem_ball]
    calc
      dist w 0 <= dist w z + dist z 0 := dist_triangle w z 0
      _ < (1 / 4 : Real) + (1 / 2 : Real) := add_lt_add hw hz
      _ = (3 / 4 : Real) := by norm_num
  have hzOuter : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) z := by
    apply hSmallSubset
    exact Metric.mem_ball_self (by norm_num)
  have hDiff : DifferentiableOn Complex f (Metric.ball z R) :=
    (nicolasJMellinShiftIntegrandFilled_differentiableOn_threeQuarter hu).mono
      hSmallSubset
  have hMaps : MapsTo f (Metric.ball z R)
      (Metric.closedBall (f z) (2 * M)) := by
    intro w hw
    have hwOuter := hSmallSubset hw
    have hwBound : norm (f w) <= M := by
      dsimp [f, M]
      simpa [nicolasJLargeMajorantHalf] using
        norm_nicolasJMellinShiftIntegrandFilled_le_threeQuarter hu hwOuter
    have hzBound : norm (f z) <= M := by
      dsimp [f, M]
      simpa [nicolasJLargeMajorantHalf] using
        norm_nicolasJMellinShiftIntegrandFilled_le_threeQuarter hu hzOuter
    rw [Metric.mem_closedBall]
    calc
      dist (f w) (f z) <= norm (f w) + norm (f z) := by
        simpa [dist_eq_norm] using norm_sub_le (f w) (f z)
      _ <= M + M := add_le_add hwBound hzBound
      _ = 2 * M := by ring
  have hCauchy := Complex.norm_deriv_le_div_of_mapsTo_ball
    hDiff hMaps (by norm_num : 0 < R)
  change norm (deriv f z) <= 8 * M
  calc
    norm (deriv f z) <= (2 * M) / R := hCauchy
    _ = 8 * M := by
      dsimp [R]
      ring

def nicolasJLargeDerivativeMajorantHalf (u : Real) : Real :=
  8 * nicolasJLargeMajorantHalf u

theorem nicolasJLargeDerivativeMajorantHalf_integrableOn :
    IntegrableOn nicolasJLargeDerivativeMajorantHalf (Ioi (1 : Real)) := by
  unfold nicolasJLargeDerivativeMajorantHalf
  exact nicolasJLargeMajorantHalf_integrableOn.const_mul 8

theorem nicolasJShiftNumeratorFilled_continuousOn_u_threeQuarter
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) z) :
    ContinuousOn (fun u : Real => nicolasJShiftNumeratorFilled u z)
      (Ioi (1 : Real)) := by
  let s0 : Real -> Complex := fun u : Real => ((u + 1 : Real) : Complex)
  let s1 : Real -> Complex := fun u : Real => s0 u - z
  have hS0 : Continuous s0 := by
    dsimp [s0]
    fun_prop
  have hS1 : Continuous s1 := by
    dsimp [s1]
    exact hS0.sub continuous_const
  intro u hu
  have huOne : 1 < u := mem_Ioi.mp hu
  have hzNorm : norm z < (3 / 4 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzRe : z.re < (3 / 4 : Real) :=
    (Complex.re_le_norm z).trans_lt hzNorm
  have hs0 : 1 < (s0 u).re := by
    dsimp [s0]
    linarith
  have hs1 : 1 < (s1 u).re := by
    dsimp [s1, s0]
    linarith
  have hTail0 : ContinuousAt (fun v : Real =>
      nicolasPsiMellinTailContinuationFilled (s0 v)) u :=
    (nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re hs0).continuousAt.comp
      hS0.continuousAt
  have hTail1 : ContinuousAt (fun v : Real =>
      nicolasPsiMellinTailContinuationFilled (s1 v)) u :=
    (nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re hs1).continuousAt.comp
      hS1.continuousAt
  unfold nicolasJShiftNumeratorFilled
  change ContinuousWithinAt (fun v : Real =>
    nicolasPsiMellinTailContinuationFilled (s1 v) -
      (3 : Complex) ^ z *
        nicolasPsiMellinTailContinuationFilled (s0 v))
    (Ioi (1 : Real)) u
  exact (hTail1.sub (continuousAt_const.mul hTail0)).continuousWithinAt

theorem nicolasJMellinShiftIntegrandFilled_continuousOn_u_threeQuarter_of_ne
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) z)
    (hzZero : Not (z = 0)) :
    ContinuousOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
  have hNumeratorZ :=
    nicolasJShiftNumeratorFilled_continuousOn_u_threeQuarter hz
  have hZeroMem : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) (0 : Complex) :=
    Metric.mem_ball_self (by norm_num)
  have hNumeratorZero :=
    nicolasJShiftNumeratorFilled_continuousOn_u_threeQuarter hZeroMem
  have hU : Continuous (fun u : Real => ((u + 1 : Real) : Complex)) := by
    fun_prop
  have hInv : Continuous (fun _ : Real => Inv.inv (z - 0)) :=
    continuous_const
  have hEq : (fun u : Real => nicolasJMellinShiftIntegrandFilled z u) =
      (fun u : Real => ((u + 1 : Real) : Complex) *
        Inv.inv (z - 0) *
          (nicolasJShiftNumeratorFilled u z -
            nicolasJShiftNumeratorFilled u 0)) := by
    funext u
    unfold nicolasJMellinShiftIntegrandFilled
    rw [dslope_of_ne _ hzZero]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub]
    ring
  rw [hEq]
  exact (hU.continuousOn.mul hInv.continuousOn).mul
    (hNumeratorZ.sub hNumeratorZero)

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_half
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 2 : Real)) z) :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (volume.restrict (Ioi (1 : Real))) := by
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_zero
  case neg =>
    have hzOuter : Membership.mem
        (Metric.ball (0 : Complex) (3 / 4 : Real)) z := by
      rw [Metric.mem_ball, dist_zero_right] at hz
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    exact
      (nicolasJMellinShiftIntegrandFilled_continuousOn_u_threeQuarter_of_ne
        hzOuter hzZero).aestronglyMeasurable measurableSet_Ioi

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_threeQuarter
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) z) :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (volume.restrict (Ioi (1 : Real))) := by
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_zero
  case neg =>
    exact
      (nicolasJMellinShiftIntegrandFilled_continuousOn_u_threeQuarter_of_ne
        hz hzZero).aestronglyMeasurable measurableSet_Ioi

theorem nicolasJMellinShiftIntegrandFilled_integrableOn_large_half
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 2 : Real)) z) :
    IntegrableOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioi (1 : Real)) := by
  have hzOuter : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) z := by
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  apply Integrable.mono' nicolasJLargeMajorantHalf_integrableOn
    (nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_half hz)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simpa [nicolasJLargeMajorantHalf] using
    norm_nicolasJMellinShiftIntegrandFilled_le_threeQuarter
      (mem_Ioi.mp hu) hzOuter

theorem deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_half
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 2 : Real)) z) :
    AEStronglyMeasurable (fun u : Real =>
      deriv (fun w : Complex =>
        nicolasJMellinShiftIntegrandFilled w u) z)
      (volume.restrict (Ioi (1 : Real))) := by
  let slopeSeq : Nat -> Real -> Complex := fun n : Nat => fun u : Real =>
    slope (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u)
      z (z + nicolasJDerivativeStep n)
  have hzNorm : norm z < (1 / 2 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzOuter : Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real)) z := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hShiftOuter : forall n : Nat, Membership.mem
      (Metric.ball (0 : Complex) (3 / 4 : Real))
      (z + nicolasJDerivativeStep n) := by
    intro n
    rw [Metric.mem_ball, dist_zero_right]
    calc
      norm (z + nicolasJDerivativeStep n) <=
          norm z + norm (nicolasJDerivativeStep n) := norm_add_le _ _
      _ < (1 / 2 : Real) + (1 / 8 : Real) :=
        add_lt_add_of_lt_of_le hzNorm (norm_nicolasJDerivativeStep_lt n)
      _ < (3 / 4 : Real) := by norm_num
  have hMeas : forall n : Nat, AEMeasurable (slopeSeq n)
      (volume.restrict (Ioi (1 : Real))) := by
    intro n
    have hShift :=
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_threeQuarter
        (hShiftOuter n)
    have hBase :=
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_threeQuarter
        hzOuter
    have hEq : slopeSeq n = fun u : Real =>
        Inv.inv ((z + nicolasJDerivativeStep n) - z) *
          (nicolasJMellinShiftIntegrandFilled
              (z + nicolasJDerivativeStep n) u -
            nicolasJMellinShiftIntegrandFilled z u) := by
      funext u
      dsimp [slopeSeq]
      unfold slope
      simp only [smul_eq_mul, vsub_eq_sub]
    rw [hEq]
    exact ((hShift.sub hBase).const_mul
      (Inv.inv ((z + nicolasJDerivativeStep n) - z))).aemeasurable
  have hStepWithin : Tendsto nicolasJDerivativeStep atTop
      (nhdsWithin (0 : Complex) (Set.compl {(0 : Complex)})) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact And.intro nicolasJDerivativeStep_tendsto_zero
      (Eventually.of_forall (fun n : Nat =>
        Set.mem_compl_singleton_iff.mpr
          (nicolasJDerivativeStep_ne_zero n)))
  have hTendsto : Filter.Eventually
      (fun u : Real => Tendsto (fun n : Nat => slopeSeq n u) atTop
        (nhds (deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)))
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have huOne : 1 < u := mem_Ioi.mp hu
    have hDiffAt : DifferentiableAt Complex
        (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u) z :=
      (nicolasJMellinShiftIntegrandFilled_differentiableOn_threeQuarter
        huOne z hzOuter).differentiableAt
          (Metric.isOpen_ball.mem_nhds hzOuter)
    have hSlope := hDiffAt.hasDerivAt.tendsto_slope_zero.comp hStepWithin
    change Tendsto (fun n : Nat =>
      Inv.inv (nicolasJDerivativeStep n) *
        (nicolasJMellinShiftIntegrandFilled
            (z + nicolasJDerivativeStep n) u -
          nicolasJMellinShiftIntegrandFilled z u))
      atTop (nhds (deriv (fun w : Complex =>
        nicolasJMellinShiftIntegrandFilled w u) z)) at hSlope
    dsimp [slopeSeq]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub, add_sub_cancel_left]
    exact hSlope
  exact
    (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable

theorem nicolasJShiftedComplexContinuationFilledLarge_hasDerivAt_half
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (1 / 2 : Real)) z) :
    HasDerivAt nicolasJShiftedComplexContinuationFilledLarge
      (integral (volume.restrict (Ioi (1 : Real))) (fun u : Real =>
        deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)) z := by
  let s : Set Complex := Metric.ball (0 : Complex) (1 / 2 : Real)
  let F : Complex -> Real -> Complex := fun w : Complex => fun u : Real =>
    nicolasJMellinShiftIntegrandFilled w u
  let F' : Complex -> Real -> Complex := fun w : Complex => fun u : Real =>
    deriv (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w
  have hsNhd : Membership.mem (nhds z) s := by
    dsimp [s]
    exact Metric.isOpen_ball.mem_nhds hz
  have hFMeas : Filter.Eventually
      (fun w : Complex => AEStronglyMeasurable (F w)
        (volume.restrict (Ioi (1 : Real)))) (nhds z) := by
    filter_upwards [hsNhd] with w hw
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_half hw
  have hFInt : Integrable (F z)
      (volume.restrict (Ioi (1 : Real))) := by
    exact nicolasJMellinShiftIntegrandFilled_integrableOn_large_half hz
  have hF'Meas : AEStronglyMeasurable (F' z)
      (volume.restrict (Ioi (1 : Real))) := by
    exact deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_half hz
  have hBound : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        norm (F' w u) <= nicolasJLargeDerivativeMajorantHalf u)
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    dsimp [F', s]
    unfold nicolasJLargeDerivativeMajorantHalf
    exact norm_deriv_nicolasJMellinShiftIntegrandFilled_le_half
      (mem_Ioi.mp hu) hw
  have hDiff : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        HasDerivAt (fun v : Complex => F v u) (F' w u) w)
      (ae (volume.restrict (Ioi (1 : Real)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    have hwOuter : Membership.mem
        (Metric.ball (0 : Complex) (3 / 4 : Real)) w := by
      dsimp [s] at hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have hAt : DifferentiableAt Complex
        (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w :=
      (nicolasJMellinShiftIntegrandFilled_differentiableOn_threeQuarter
        (mem_Ioi.mp hu) w hwOuter).differentiableAt
          (Metric.isOpen_ball.mem_nhds hwOuter)
    dsimp [F, F']
    exact hAt.hasDerivAt
  have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F')
    (bound := nicolasJLargeDerivativeMajorantHalf)
    hsNhd hFMeas hFInt hF'Meas hBound
    nicolasJLargeDerivativeMajorantHalf_integrableOn hDiff
  unfold nicolasJShiftedComplexContinuationFilledLarge
  simpa [F, F'] using hMain.2

theorem nicolasJShiftedComplexContinuationFilledLarge_differentiableOn_half :
    DifferentiableOn Complex nicolasJShiftedComplexContinuationFilledLarge
      (Metric.ball (0 : Complex) (1 / 2 : Real)) := by
  intro z hz
  exact (nicolasJShiftedComplexContinuationFilledLarge_hasDerivAt_half
    hz).differentiableAt.differentiableWithinAt

theorem nicolasJShiftedComplexContinuationFilledLarge_analyticAt_pos_real
    {sigma : Real} (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 / 2) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledLarge
      (sigma : Complex) := by
  apply
    nicolasJShiftedComplexContinuationFilledLarge_differentiableOn_half.analyticAt
  apply Metric.isOpen_ball.mem_nhds
  rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hSigmaPos]
  exact hSigma

end
end Robin1984

end

section
/- Source module Robin1984.NicolasLandau.LandauMellinPrinciple. -/
namespace Robin1984
alias exists_integrableExpSet_gt_of_analyticContinuationAt :=
  ProbabilityTheory.exists_integrableExpSet_gt_of_analyticContinuationAt

end Robin1984

end

section
/- Source module Robin1984.NicolasLandau.NicolasLandauCompactBlock. -/
namespace Robin1984
open Filter MeasureTheory Set
open scoped ENNReal Topology
noncomputable section
def nicolasFilledOneRadius : Real :=
  Classical.choose
    exists_nicolasPsiMellinTailContinuationFilled_analytic_ball_one

theorem nicolasFilledOneRadius_pos : 0 < nicolasFilledOneRadius :=
  (Classical.choose_spec
    exists_nicolasPsiMellinTailContinuationFilled_analytic_ball_one).1

theorem nicolasFilledOneRadius_analytic
    {s : Complex}
    (hs : Membership.mem
      (Metric.ball (1 : Complex) nicolasFilledOneRadius) s) :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled s :=
  (Classical.choose_spec
    exists_nicolasPsiMellinTailContinuationFilled_analytic_ball_one).2 s hs

def nicolasCompactZRadius : Real :=
  min (nicolasFilledOneRadius / 16) (1 / 64)

theorem nicolasCompactZRadius_pos : 0 < nicolasCompactZRadius := by
  unfold nicolasCompactZRadius
  exact lt_min (div_pos nicolasFilledOneRadius_pos (by norm_num))
    (by norm_num)

theorem nicolasCompactZRadius_le_oneRadius_div_sixteen :
    nicolasCompactZRadius <= nicolasFilledOneRadius / 16 := by
  unfold nicolasCompactZRadius
  exact min_le_left _ _

theorem nicolasCompactZRadius_le_one_sixty_four :
    nicolasCompactZRadius <= 1 / 64 := by
  unfold nicolasCompactZRadius
  exact min_le_right _ _

theorem nicolasPsiMellinTailContinuationFilled_analyticAt_compact_base
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u) :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled
      (((u + 1 : Real) : Complex)) := by
  by_cases huZero : u = 0
  case pos =>
    subst u
    simpa using nicolasPsiMellinTailContinuationFilled_analyticAt_one
  case neg =>
    apply nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re
    simp only [Complex.ofReal_re]
    have huPos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm huZero)
    linarith

theorem nicolasPsiMellinTailContinuationFilled_analyticAt_compact_shift
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u)
    {z : Complex}
    (hz : norm z < 4 * nicolasCompactZRadius) :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled
      (((u + 1 : Real) : Complex) - z) := by
  have hRadius := nicolasFilledOneRadius_pos
  have hFourRadius :
      4 * nicolasCompactZRadius <= nicolasFilledOneRadius / 4 := by
    calc
      4 * nicolasCompactZRadius <=
          4 * (nicolasFilledOneRadius / 16) :=
        mul_le_mul_of_nonneg_left
          nicolasCompactZRadius_le_oneRadius_div_sixteen (by norm_num)
      _ = nicolasFilledOneRadius / 4 := by ring
  have hzRadius : norm z < nicolasFilledOneRadius / 4 :=
    hz.trans_le hFourRadius
  by_cases huSmall : u < nicolasFilledOneRadius / 2
  case pos =>
    apply nicolasFilledOneRadius_analytic
    rw [Metric.mem_ball, dist_eq_norm]
    have hDifference :
        (((u + 1 : Real) : Complex) - z) - (1 : Complex) =
          (u : Complex) - z := by
      push_cast
      ring
    rw [hDifference]
    calc
      norm ((u : Complex) - z) <= norm (u : Complex) + norm z :=
        norm_sub_le _ _
      _ = u + norm z := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
      _ < nicolasFilledOneRadius / 2 +
          nicolasFilledOneRadius / 4 := add_lt_add huSmall hzRadius
      _ < nicolasFilledOneRadius := by linarith
  case neg =>
    apply nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re
    have hzRe : z.re <= norm z := Complex.re_le_norm z
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith

theorem nicolasJShiftNumeratorFilled_analyticAt_compact
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u)
    {z : Complex}
    (hz : norm z < 4 * nicolasCompactZRadius) :
    AnalyticAt Complex (nicolasJShiftNumeratorFilled u) z := by
  let s : Complex := ((u + 1 : Real) : Complex)
  have hTailShift : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled (s - z) := by
    dsimp [s]
    exact nicolasPsiMellinTailContinuationFilled_analyticAt_compact_shift
      hu hz
  have hAffine : AnalyticAt Complex (fun w : Complex => s - w) z :=
    analyticAt_const.sub analyticAt_id
  have hShift : AnalyticAt Complex (fun w : Complex =>
      nicolasPsiMellinTailContinuationFilled (s - w)) z := by
    have hComp := hTailShift.comp_of_eq hAffine rfl
    apply hComp.congr
    exact Eventually.of_forall (fun _ => rfl)
  have hPowerDifferentiable : Differentiable Complex
      (fun w : Complex => (3 : Complex) ^ w) := by
    intro w
    exact DifferentiableAt.const_cpow differentiableAt_id
      (Or.inl (by norm_num))
  have hPower : AnalyticAt Complex
      (fun w : Complex => (3 : Complex) ^ w) z :=
    hPowerDifferentiable.analyticAt z
  have hTailBase : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled s := by
    dsimp [s]
    exact nicolasPsiMellinTailContinuationFilled_analyticAt_compact_base hu
  have hTailConst : AnalyticAt Complex (fun _ : Complex =>
      nicolasPsiMellinTailContinuationFilled s) z := analyticAt_const
  unfold nicolasJShiftNumeratorFilled
  change AnalyticAt Complex (fun w : Complex =>
    nicolasPsiMellinTailContinuationFilled (s - w) -
      (3 : Complex) ^ w * nicolasPsiMellinTailContinuationFilled s) z
  exact hShift.sub (hPower.mul hTailConst)

def nicolasCompactNumeratorDomain : Set (Prod Real Complex) :=
  Set.prod (Icc (0 : Real) 1)
    (Metric.closedBall (0 : Complex) (3 * nicolasCompactZRadius))

theorem nicolasJShiftNumeratorFilled_continuousOn_compact :
    ContinuousOn (fun p : Prod Real Complex =>
      nicolasJShiftNumeratorFilled p.1 p.2)
      nicolasCompactNumeratorDomain := by
  intro p hp
  have hu : Membership.mem (Icc (0 : Real) 1) p.1 := hp.1
  have hzClosed : Membership.mem
      (Metric.closedBall (0 : Complex) (3 * nicolasCompactZRadius)) p.2 :=
    hp.2
  have hzNorm : norm p.2 <= 3 * nicolasCompactZRadius := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hzClosed
  have hzStrict : norm p.2 < 4 * nicolasCompactZRadius := by
    have hRadius := nicolasCompactZRadius_pos
    linarith
  let s0 : Prod Real Complex -> Complex := fun q =>
    (((q.1 + 1 : Real) : Complex))
  let s1 : Prod Real Complex -> Complex := fun q => s0 q - q.2
  have hs0Continuous : ContinuousAt s0 p := by
    dsimp [s0]
    fun_prop
  have hs1Continuous : ContinuousAt s1 p := by
    dsimp [s1]
    exact hs0Continuous.sub continuousAt_snd
  have hTailBase : ContinuousAt
      (fun q : Prod Real Complex =>
        nicolasPsiMellinTailContinuationFilled (s0 q)) p := by
    exact
      (nicolasPsiMellinTailContinuationFilled_analyticAt_compact_base hu).continuousAt.comp_of_eq
        hs0Continuous rfl
  have hTailShift : ContinuousAt
      (fun q : Prod Real Complex =>
        nicolasPsiMellinTailContinuationFilled (s1 q)) p := by
    exact
      (nicolasPsiMellinTailContinuationFilled_analyticAt_compact_shift
        hu hzStrict).continuousAt.comp_of_eq hs1Continuous rfl
  have hPower : ContinuousAt
      (fun q : Prod Real Complex => (3 : Complex) ^ q.2) p := by
    exact continuousAt_snd.const_cpow (Or.inl (by norm_num))
  unfold nicolasJShiftNumeratorFilled
  change ContinuousWithinAt (fun q : Prod Real Complex =>
    nicolasPsiMellinTailContinuationFilled (s1 q) -
      (3 : Complex) ^ q.2 *
        nicolasPsiMellinTailContinuationFilled (s0 q))
    nicolasCompactNumeratorDomain p
  exact (hTailShift.sub (hPower.mul hTailBase)).continuousWithinAt

theorem nicolasCompactNumeratorDomain_isCompact :
    IsCompact nicolasCompactNumeratorDomain := by
  unfold nicolasCompactNumeratorDomain
  exact isCompact_Icc.prod (isCompact_closedBall _ _)

theorem exists_nicolasCompactNumeratorBound :
    Exists fun C : Real =>
      forall u : Real,
        Membership.mem (Icc (0 : Real) 1) u ->
        forall z : Complex,
          Membership.mem
            (Metric.closedBall (0 : Complex)
              (3 * nicolasCompactZRadius)) z ->
          norm (nicolasJShiftNumeratorFilled u z) <= C := by
  let f : Prod Real Complex -> Real := fun p =>
    norm (nicolasJShiftNumeratorFilled p.1 p.2)
  have hf : ContinuousOn f nicolasCompactNumeratorDomain := by
    dsimp [f]
    exact nicolasJShiftNumeratorFilled_continuousOn_compact.norm
  have hBound : BddAbove (f '' nicolasCompactNumeratorDomain) :=
    nicolasCompactNumeratorDomain_isCompact.bddAbove_image
      hf
  choose C hC using hBound
  refine Exists.intro C ?_
  intro u hu z hz
  have hMember : Membership.mem (f '' nicolasCompactNumeratorDomain)
      (f (u, z)) := by
    apply mem_image_of_mem
    change And
      (Membership.mem (Icc (0 : Real) 1) u)
      (Membership.mem
        (Metric.closedBall (0 : Complex) (3 * nicolasCompactZRadius)) z)
    exact And.intro hu hz
  have hValue := hC hMember
  dsimp [f] at hValue
  exact hValue

def nicolasCompactNumeratorBound : Real :=
  max (Classical.choose exists_nicolasCompactNumeratorBound) 0

theorem nicolasCompactNumeratorBound_nonneg :
    0 <= nicolasCompactNumeratorBound := by
  unfold nicolasCompactNumeratorBound
  exact le_max_right _ _

theorem norm_nicolasJShiftNumeratorFilled_le_compact
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u)
    {z : Complex}
    (hz : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) z) :
    norm (nicolasJShiftNumeratorFilled u z) <=
      nicolasCompactNumeratorBound := by
  have hChosen :=
    (Classical.choose_spec exists_nicolasCompactNumeratorBound) u hu z hz
  exact hChosen.trans (le_max_left _ _)

theorem nicolasJShiftNumeratorFilled_differentiableOn_compact
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u) :
    DifferentiableOn Complex (nicolasJShiftNumeratorFilled u)
      (Metric.ball (0 : Complex) (3 * nicolasCompactZRadius)) := by
  intro z hz
  have hzNorm : norm z < 3 * nicolasCompactZRadius := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzFour : norm z < 4 * nicolasCompactZRadius := by
    have hRadius := nicolasCompactZRadius_pos
    linarith
  exact
    (nicolasJShiftNumeratorFilled_analyticAt_compact hu hzFour).differentiableAt.differentiableWithinAt

theorem norm_nicolasJMellinShiftIntegrandFilled_le_compact
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u)
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (3 * nicolasCompactZRadius)) z) :
    norm (nicolasJMellinShiftIntegrandFilled z u) <=
      2 * (nicolasCompactNumeratorBound /
        (3 * nicolasCompactZRadius)) := by
  let R : Real := 3 * nicolasCompactZRadius
  let M : Real := nicolasCompactNumeratorBound
  have hRPos : 0 < R := by
    dsimp [R]
    exact mul_pos (by norm_num) nicolasCompactZRadius_pos
  have hMNonneg : 0 <= M := by
    dsimp [M]
    exact nicolasCompactNumeratorBound_nonneg
  have hMaps : MapsTo (nicolasJShiftNumeratorFilled u)
      (Metric.ball (0 : Complex) R)
      (Metric.closedBall (nicolasJShiftNumeratorFilled u 0) M) := by
    intro w hw
    rw [nicolasJShiftNumeratorFilled_zero]
    rw [Metric.mem_closedBall, dist_zero_right]
    apply norm_nicolasJShiftNumeratorFilled_le_compact hu
    exact Metric.ball_subset_closedBall hw
  have hDslope := Complex.norm_dslope_le_div_of_mapsTo_ball
    (nicolasJShiftNumeratorFilled_differentiableOn_compact hu)
    hMaps hz
  have huOnePos : 0 < u + 1 := by linarith [hu.1]
  have huOneLe : u + 1 <= 2 := by linarith [hu.2]
  have hQuotientNonneg : 0 <= M / R := div_nonneg hMNonneg hRPos.le
  unfold nicolasJMellinShiftIntegrandFilled
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos huOnePos]
  calc
    (u + 1) * norm (dslope (nicolasJShiftNumeratorFilled u) 0 z) <=
        (u + 1) * (M / R) :=
      mul_le_mul_of_nonneg_left hDslope huOnePos.le
    _ <= 2 * (M / R) :=
      mul_le_mul_of_nonneg_right huOneLe hQuotientNonneg
    _ = 2 * (nicolasCompactNumeratorBound /
        (3 * nicolasCompactZRadius)) := by
      dsimp [M, R]

def nicolasCompactIntegrandBound : Real :=
  2 * (nicolasCompactNumeratorBound /
    (3 * nicolasCompactZRadius))

theorem nicolasJMellinShiftIntegrandFilled_differentiableOn_compact
    {u : Real} (hu : Membership.mem (Ioc (0 : Real) 1) u) :
    DifferentiableOn Complex
      (fun z : Complex => nicolasJMellinShiftIntegrandFilled z u)
      (Metric.ball (0 : Complex) (3 * nicolasCompactZRadius)) := by
  have huClosed : Membership.mem (Icc (0 : Real) 1) u :=
    And.intro hu.1.le hu.2
  intro z hz
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact (nicolasJMellinShiftIntegrandFilled_analyticAt_zero
      hu.1).differentiableAt.differentiableWithinAt
  case neg =>
    have hNumeratorAt : DifferentiableAt Complex
        (nicolasJShiftNumeratorFilled u) z :=
      (nicolasJShiftNumeratorFilled_differentiableOn_compact
        huClosed z hz).differentiableAt
          (Metric.isOpen_ball.mem_nhds hz)
    have hDslopeAt : DifferentiableAt Complex
        (dslope (nicolasJShiftNumeratorFilled u) 0) z :=
      (differentiableAt_dslope_of_ne hzZero).2 hNumeratorAt
    unfold nicolasJMellinShiftIntegrandFilled
    exact (analyticAt_const.differentiableAt.mul hDslopeAt).differentiableWithinAt

theorem norm_deriv_nicolasJMellinShiftIntegrandFilled_le_compact
    {u : Real} (hu : Membership.mem (Ioc (0 : Real) 1) u)
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) nicolasCompactZRadius) z) :
    norm (deriv (fun w : Complex =>
      nicolasJMellinShiftIntegrandFilled w u) z) <=
      (2 * nicolasCompactIntegrandBound) /
        nicolasCompactZRadius := by
  let f : Complex -> Complex := fun w : Complex =>
    nicolasJMellinShiftIntegrandFilled w u
  let R : Real := nicolasCompactZRadius
  let M : Real := nicolasCompactIntegrandBound
  have hRPos : 0 < R := by
    dsimp [R]
    exact nicolasCompactZRadius_pos
  have hSmallSubset : Metric.ball z R <=
      Metric.ball (0 : Complex) (3 * R) := by
    intro w hw
    rw [Metric.mem_ball] at hw hz
    rw [Metric.mem_ball]
    calc
      dist w 0 <= dist w z + dist z 0 := dist_triangle w z 0
      _ < R + R := add_lt_add hw hz
      _ < 3 * R := by linarith
  have hzLarge : Membership.mem
      (Metric.ball (0 : Complex) (3 * R)) z := by
    apply hSmallSubset
    exact Metric.mem_ball_self hRPos
  have hDiff : DifferentiableOn Complex f (Metric.ball z R) :=
    (nicolasJMellinShiftIntegrandFilled_differentiableOn_compact hu).mono
      hSmallSubset
  have hMaps : MapsTo f (Metric.ball z R)
      (Metric.closedBall (f z) (2 * M)) := by
    intro w hw
    have hwLarge := hSmallSubset hw
    have hwBound : norm (f w) <= M := by
      dsimp [f, M, R] at hwLarge
      dsimp [f, M]
      simpa [nicolasCompactIntegrandBound] using
        norm_nicolasJMellinShiftIntegrandFilled_le_compact
          (And.intro hu.1.le hu.2) hwLarge
    have hzBound : norm (f z) <= M := by
      dsimp [f, M, R] at hzLarge
      dsimp [f, M]
      simpa [nicolasCompactIntegrandBound] using
        norm_nicolasJMellinShiftIntegrandFilled_le_compact
          (And.intro hu.1.le hu.2) hzLarge
    rw [Metric.mem_closedBall]
    calc
      dist (f w) (f z) <= norm (f w) + norm (f z) := by
        simpa [dist_eq_norm] using norm_sub_le (f w) (f z)
      _ <= M + M := add_le_add hwBound hzBound
      _ = 2 * M := by ring
  have hCauchy := Complex.norm_deriv_le_div_of_mapsTo_ball
    hDiff hMaps hRPos
  change norm (deriv f z) <= (2 * M) / R
  exact hCauchy

theorem nicolasJShiftNumeratorFilled_continuousOn_compact_u
    {z : Complex}
    (hz : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) z) :
    ContinuousOn (fun u : Real => nicolasJShiftNumeratorFilled u z)
      (Icc (0 : Real) 1) := by
  intro u hu
  have hJoint :=
    nicolasJShiftNumeratorFilled_continuousOn_compact (u, z)
      (And.intro hu hz)
  have hPair : ContinuousWithinAt (fun v : Real => (v, z))
      (Icc (0 : Real) 1) u :=
    (continuousAt_id.prodMk continuousAt_const).continuousWithinAt
  have hMaps : MapsTo (fun v : Real => (v, z))
      (Icc (0 : Real) 1) nicolasCompactNumeratorDomain := by
    intro v hv
    exact And.intro hv hz
  have hComp := ContinuousWithinAt.comp
    (f := fun v : Real => (v, z))
    (g := fun p : Prod Real Complex =>
      nicolasJShiftNumeratorFilled p.1 p.2)
    hJoint hPair hMaps
  simpa [Function.comp_def] using hComp

theorem nicolasJMellinShiftIntegrandFilled_continuousOn_compact_u_of_ne
    {z : Complex}
    (hz : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) z)
    (hzZero : Not (z = 0)) :
    ContinuousOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (Icc (0 : Real) 1) := by
  have hZeroMem : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) (0 : Complex) := by
    rw [Metric.mem_closedBall, dist_self]
    exact (mul_pos (by norm_num) nicolasCompactZRadius_pos).le
  have hNumeratorZ :=
    nicolasJShiftNumeratorFilled_continuousOn_compact_u hz
  have hNumeratorZero :=
    nicolasJShiftNumeratorFilled_continuousOn_compact_u hZeroMem
  have hU : Continuous (fun u : Real => ((u + 1 : Real) : Complex)) := by
    fun_prop
  have hInv : Continuous (fun _ : Real => Inv.inv (z - 0)) :=
    continuous_const
  have hEq : (fun u : Real => nicolasJMellinShiftIntegrandFilled z u) =
      (fun u : Real => ((u + 1 : Real) : Complex) *
        Inv.inv (z - 0) *
          (nicolasJShiftNumeratorFilled u z -
            nicolasJShiftNumeratorFilled u 0)) := by
    funext u
    unfold nicolasJMellinShiftIntegrandFilled
    rw [dslope_of_ne _ hzZero]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub]
    ring
  rw [hEq]
  exact (hU.continuousOn.mul hInv.continuousOn).mul
    (hNumeratorZ.sub hNumeratorZero)

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact_of_ne
    {z : Complex}
    (hz : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) z)
    (hzZero : Not (z = 0)) :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (volume.restrict (Ioc (0 : Real) 1)) := by
  have hContinuous :=
    nicolasJMellinShiftIntegrandFilled_continuousOn_compact_u_of_ne
      hz hzZero
  have hSubset : Ioc (0 : Real) 1 <= Icc (0 : Real) 1 := by
    intro u hu
    exact And.intro hu.1.le hu.2
  exact (hContinuous.mono hSubset).aestronglyMeasurable measurableSet_Ioc

def nicolasCompactDerivativeStep (n : Nat) : Complex :=
  (((nicolasCompactZRadius / 2) *
    ((1 : Real) / ((n : Real) + 1)) : Real) : Complex)

theorem nicolasCompactDerivativeStep_ne_zero (n : Nat) :
    Not (nicolasCompactDerivativeStep n = 0) := by
  unfold nicolasCompactDerivativeStep
  apply Complex.ofReal_ne_zero.mpr
  exact mul_ne_zero
    (div_ne_zero (ne_of_gt nicolasCompactZRadius_pos) (by norm_num))
    (div_ne_zero (by norm_num) (by positivity))

theorem norm_nicolasCompactDerivativeStep_lt (n : Nat) :
    norm (nicolasCompactDerivativeStep n) < nicolasCompactZRadius := by
  have hRadius := nicolasCompactZRadius_pos
  have hRecipPos : 0 < (1 : Real) / ((n : Real) + 1) := by
    positivity
  have hRecipLe : (1 : Real) / ((n : Real) + 1) <= 1 := by
    apply (div_le_one (by positivity)).2
    norm_num
  unfold nicolasCompactDerivativeStep
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (div_pos hRadius (by norm_num)) hRecipPos)]
  calc
    nicolasCompactZRadius / 2 * ((1 : Real) / ((n : Real) + 1)) <=
        nicolasCompactZRadius / 2 * 1 :=
      mul_le_mul_of_nonneg_left hRecipLe
        (div_nonneg hRadius.le (by norm_num))
    _ < nicolasCompactZRadius := by linarith

theorem nicolasCompactDerivativeStep_tendsto_zero :
    Tendsto nicolasCompactDerivativeStep atTop (nhds (0 : Complex)) := by
  have hRecip : Tendsto
      (fun n : Nat => (1 : Real) / ((n : Real) + 1))
      atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hScaled : Tendsto
      (fun n : Nat => (nicolasCompactZRadius / 2) *
        ((1 : Real) / ((n : Real) + 1)))
      atTop (nhds ((nicolasCompactZRadius / 2) * 0)) :=
    tendsto_const_nhds.mul hRecip
  have hCast := Complex.continuous_ofReal.continuousAt.tendsto.comp hScaled
  have hFunctions :
      Function.comp Complex.ofReal (fun n : Nat =>
        (nicolasCompactZRadius / 2) *
          ((1 : Real) / ((n : Real) + 1))) =
        nicolasCompactDerivativeStep := by
    funext n
    rfl
  have hTarget : Tendsto
      (Function.comp Complex.ofReal (fun n : Nat =>
        (nicolasCompactZRadius / 2) *
          ((1 : Real) / ((n : Real) + 1))))
      atTop (nhds (0 : Complex)) := by
    simpa using hCast
  rw [hFunctions] at hTarget
  exact hTarget

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact_zero :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled 0 u)
      (volume.restrict (Ioc (0 : Real) 1)) := by
  have hZMem : forall n : Nat,
      Membership.mem
        (Metric.closedBall (0 : Complex)
          (3 * nicolasCompactZRadius))
        (nicolasCompactDerivativeStep n) := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    have hStep := norm_nicolasCompactDerivativeStep_lt n
    have hRadius := nicolasCompactZRadius_pos
    linarith
  have hMeas : forall n : Nat, AEMeasurable
      (fun u : Real => nicolasJMellinShiftIntegrandFilled
        (nicolasCompactDerivativeStep n) u)
      (volume.restrict (Ioc (0 : Real) 1)) := by
    intro n
    exact
      (nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact_of_ne
        (hZMem n) (nicolasCompactDerivativeStep_ne_zero n)).aemeasurable
  have hTendsto : Filter.Eventually
      (fun u : Real => Tendsto
        (fun n : Nat => nicolasJMellinShiftIntegrandFilled
          (nicolasCompactDerivativeStep n) u)
        atTop (nhds (nicolasJMellinShiftIntegrandFilled 0 u)))
      (ae (volume.restrict (Ioc (0 : Real) 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (nicolasJMellinShiftIntegrandFilled_analyticAt_zero
      hu.1).continuousAt.tendsto.comp
        nicolasCompactDerivativeStep_tendsto_zero
  exact
    (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable

theorem nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
    {z : Complex}
    (hz : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) z) :
    AEStronglyMeasurable (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u)
      (volume.restrict (Ioc (0 : Real) 1)) := by
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact_zero
  case neg =>
    exact
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact_of_ne
        hz hzZero

theorem nicolasJMellinShiftIntegrandFilled_integrableOn_compact
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) (3 * nicolasCompactZRadius)) z) :
    IntegrableOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Ioc (0 : Real) 1) := by
  have hMajorant : IntegrableOn
      (fun _ : Real => nicolasCompactIntegrandBound)
      (Ioc (0 : Real) 1) := integrableOn_const measure_Ioc_lt_top.ne
  apply Integrable.mono' hMajorant
    (nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
      (Metric.ball_subset_closedBall hz))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  simpa [nicolasCompactIntegrandBound] using
    norm_nicolasJMellinShiftIntegrandFilled_le_compact
      (And.intro hu.1.le hu.2) hz

def nicolasCompactDerivativeMajorant : Real :=
  (2 * nicolasCompactIntegrandBound) /
    nicolasCompactZRadius

theorem nicolasCompactDerivativeMajorant_integrableOn :
    IntegrableOn (fun _ : Real => nicolasCompactDerivativeMajorant)
      (Ioc (0 : Real) 1) :=
  integrableOn_const measure_Ioc_lt_top.ne

theorem deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) nicolasCompactZRadius) z) :
    AEStronglyMeasurable (fun u : Real =>
      deriv (fun w : Complex =>
        nicolasJMellinShiftIntegrandFilled w u) z)
      (volume.restrict (Ioc (0 : Real) 1)) := by
  let slopeSeq : Nat -> Real -> Complex := fun n : Nat => fun u : Real =>
    slope (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u)
      z (z + nicolasCompactDerivativeStep n)
  have hzNorm : norm z < nicolasCompactZRadius := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzLarge : Membership.mem
      (Metric.closedBall (0 : Complex)
        (3 * nicolasCompactZRadius)) z := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hRadius := nicolasCompactZRadius_pos
    linarith
  have hShiftLarge : forall n : Nat,
      Membership.mem
        (Metric.closedBall (0 : Complex)
          (3 * nicolasCompactZRadius))
        (z + nicolasCompactDerivativeStep n) := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (calc
        norm (z + nicolasCompactDerivativeStep n) <=
            norm z + norm (nicolasCompactDerivativeStep n) := norm_add_le _ _
        _ < nicolasCompactZRadius + nicolasCompactZRadius :=
          add_lt_add hzNorm (norm_nicolasCompactDerivativeStep_lt n)
        _ < 3 * nicolasCompactZRadius := by
          linarith [nicolasCompactZRadius_pos]).le
  have hMeas : forall n : Nat, AEMeasurable (slopeSeq n)
      (volume.restrict (Ioc (0 : Real) 1)) := by
    intro n
    have hShift :=
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
        (hShiftLarge n)
    have hBase :=
      nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
        hzLarge
    have hEq : slopeSeq n = fun u : Real =>
        Inv.inv ((z + nicolasCompactDerivativeStep n) - z) *
          (nicolasJMellinShiftIntegrandFilled
              (z + nicolasCompactDerivativeStep n) u -
            nicolasJMellinShiftIntegrandFilled z u) := by
      funext u
      dsimp [slopeSeq]
      unfold slope
      simp only [smul_eq_mul, vsub_eq_sub]
    rw [hEq]
    exact ((hShift.sub hBase).const_mul
      (Inv.inv ((z + nicolasCompactDerivativeStep n) - z))).aemeasurable
  have hStepWithin : Tendsto nicolasCompactDerivativeStep atTop
      (nhdsWithin (0 : Complex) (Set.compl {(0 : Complex)})) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact And.intro nicolasCompactDerivativeStep_tendsto_zero
      (Eventually.of_forall (fun n : Nat =>
        Set.mem_compl_singleton_iff.mpr
          (nicolasCompactDerivativeStep_ne_zero n)))
  have hTendsto : Filter.Eventually
      (fun u : Real => Tendsto (fun n : Nat => slopeSeq n u) atTop
        (nhds (deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)))
      (ae (volume.restrict (Ioc (0 : Real) 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hzLargeBall : Membership.mem
        (Metric.ball (0 : Complex)
          (3 * nicolasCompactZRadius)) z := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith [nicolasCompactZRadius_pos]
    have hDiffAt : DifferentiableAt Complex
        (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u) z :=
      (nicolasJMellinShiftIntegrandFilled_differentiableOn_compact
        hu z hzLargeBall).differentiableAt
          (Metric.isOpen_ball.mem_nhds hzLargeBall)
    have hSlope := hDiffAt.hasDerivAt.tendsto_slope_zero.comp hStepWithin
    change Tendsto (fun n : Nat =>
      Inv.inv (nicolasCompactDerivativeStep n) *
        (nicolasJMellinShiftIntegrandFilled
            (z + nicolasCompactDerivativeStep n) u -
          nicolasJMellinShiftIntegrandFilled z u))
      atTop (nhds (deriv (fun w : Complex =>
        nicolasJMellinShiftIntegrandFilled w u) z)) at hSlope
    dsimp [slopeSeq]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub, add_sub_cancel_left]
    exact hSlope
  exact
    (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable

theorem nicolasJShiftedComplexContinuationFilledCompact_hasDerivAt
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) nicolasCompactZRadius) z) :
    HasDerivAt nicolasJShiftedComplexContinuationFilledCompact
      (integral (volume.restrict (Ioc (0 : Real) 1)) (fun u : Real =>
        deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)) z := by
  let s : Set Complex :=
    Metric.ball (0 : Complex) nicolasCompactZRadius
  let F : Complex -> Real -> Complex := fun w : Complex => fun u : Real =>
    nicolasJMellinShiftIntegrandFilled w u
  let F' : Complex -> Real -> Complex := fun w : Complex => fun u : Real =>
    deriv (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w
  have hsNhd : Membership.mem (nhds z) s := by
    dsimp [s]
    exact Metric.isOpen_ball.mem_nhds hz
  have hFMeas : Filter.Eventually
      (fun w : Complex => AEStronglyMeasurable (F w)
        (volume.restrict (Ioc (0 : Real) 1))) (nhds z) := by
    filter_upwards [hsNhd] with w hw
    have hwLarge : Membership.mem
        (Metric.closedBall (0 : Complex)
          (3 * nicolasCompactZRadius)) w := by
      dsimp [s] at hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith [nicolasCompactZRadius_pos]
    exact nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
      hwLarge
  have hzLarge : Membership.mem
      (Metric.ball (0 : Complex)
        (3 * nicolasCompactZRadius)) z := by
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith [nicolasCompactZRadius_pos]
  have hFInt : Integrable (F z)
      (volume.restrict (Ioc (0 : Real) 1)) := by
    exact nicolasJMellinShiftIntegrandFilled_integrableOn_compact hzLarge
  have hF'Meas : AEStronglyMeasurable (F' z)
      (volume.restrict (Ioc (0 : Real) 1)) := by
    exact deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compact
      hz
  have hBound : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        norm (F' w u) <= nicolasCompactDerivativeMajorant)
      (ae (volume.restrict (Ioc (0 : Real) 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    intro w hw
    dsimp [F', s] at hw
    dsimp [F']
    unfold nicolasCompactDerivativeMajorant
    exact norm_deriv_nicolasJMellinShiftIntegrandFilled_le_compact hu hw
  have hDiff : Filter.Eventually
      (fun u : Real => forall w : Complex, Membership.mem s w ->
        HasDerivAt (fun v : Complex => F v u) (F' w u) w)
      (ae (volume.restrict (Ioc (0 : Real) 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    intro w hw
    have hwLarge : Membership.mem
        (Metric.ball (0 : Complex)
          (3 * nicolasCompactZRadius)) w := by
      dsimp [s] at hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [Metric.mem_ball, dist_zero_right]
      linarith [nicolasCompactZRadius_pos]
    have hAt : DifferentiableAt Complex
        (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w :=
      (nicolasJMellinShiftIntegrandFilled_differentiableOn_compact
        hu w hwLarge).differentiableAt
          (Metric.isOpen_ball.mem_nhds hwLarge)
    dsimp [F, F']
    exact hAt.hasDerivAt
  have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F')
    (bound := fun _ : Real => nicolasCompactDerivativeMajorant)
    hsNhd hFMeas hFInt hF'Meas hBound
    nicolasCompactDerivativeMajorant_integrableOn hDiff
  unfold nicolasJShiftedComplexContinuationFilledCompact
  simpa [F, F'] using hMain.2

theorem nicolasJShiftedComplexContinuationFilledCompact_differentiableOn :
    DifferentiableOn Complex nicolasJShiftedComplexContinuationFilledCompact
      (Metric.ball (0 : Complex) nicolasCompactZRadius) := by
  intro z hz
  exact
    (nicolasJShiftedComplexContinuationFilledCompact_hasDerivAt
      hz).differentiableAt.differentiableWithinAt

theorem nicolasJShiftedComplexContinuationFilled_eq_compact_add_large
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (0 : Complex) nicolasCompactZRadius) z) :
    nicolasJShiftedComplexContinuationFilled z =
      nicolasJShiftedComplexContinuationFilledCompact z +
        nicolasJShiftedComplexContinuationFilledLarge z := by
  have hzNorm : norm z < nicolasCompactZRadius := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzCompact : Membership.mem
      (Metric.ball (0 : Complex)
        (3 * nicolasCompactZRadius)) z := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith [nicolasCompactZRadius_pos]
  have hzLarge : Membership.mem
      (Metric.ball (0 : Complex) (1 / 8 : Real)) z := by
    rw [Metric.mem_ball, dist_zero_right]
    have hRadiusBound := nicolasCompactZRadius_le_one_sixty_four
    linarith
  have hCompactInt :=
    nicolasJMellinShiftIntegrandFilled_integrableOn_compact hzCompact
  have hLargeInt :=
    nicolasJMellinShiftIntegrandFilled_integrableOn_large hzLarge
  unfold nicolasJShiftedComplexContinuationFilled
    nicolasJShiftedComplexContinuationFilledCompact
    nicolasJShiftedComplexContinuationFilledLarge
  rw [<- Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : Real) <= 1),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
  . exact hCompactInt
  . exact hLargeInt

theorem nicolasJShiftedComplexContinuationFilled_differentiableOn_compactRadius :
    DifferentiableOn Complex nicolasJShiftedComplexContinuationFilled
      (Metric.ball (0 : Complex) nicolasCompactZRadius) := by
  have hLargeSubset : Metric.ball (0 : Complex) nicolasCompactZRadius <=
      Metric.ball (0 : Complex) (1 / 8 : Real) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    have hRadiusBound := nicolasCompactZRadius_le_one_sixty_four
    linarith
  have hSum : DifferentiableOn Complex
      (fun z : Complex =>
        nicolasJShiftedComplexContinuationFilledCompact z +
          nicolasJShiftedComplexContinuationFilledLarge z)
      (Metric.ball (0 : Complex) nicolasCompactZRadius) :=
    nicolasJShiftedComplexContinuationFilledCompact_differentiableOn.add
      (nicolasJShiftedComplexContinuationFilledLarge_differentiableOn.mono
        hLargeSubset)
  exact hSum.congr (fun z hz =>
    nicolasJShiftedComplexContinuationFilled_eq_compact_add_large hz)

theorem nicolasJShiftedComplexContinuationFilled_analyticAt_zero :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilled 0 := by
  apply
    nicolasJShiftedComplexContinuationFilled_differentiableOn_compactRadius.analyticAt
  exact Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self nicolasCompactZRadius_pos)

theorem realAnalyticAt_re_comp_of_complexAnalyticAt
    {f : Complex -> Complex} {a : Real}
    (hf : AnalyticAt Complex f (a : Complex)) :
    AnalyticAt Real (fun x : Real => Complex.re (f (x : Complex))) a := by
  have hRestricted : AnalyticAt Real f (a : Complex) :=
    hf.restrictScalars
  have hInput : AnalyticAt Real
      (Function.comp f Complex.ofRealCLM) a :=
    hRestricted.compContinuousLinearMap
  change AnalyticAt Real
    (Function.comp Complex.reCLM
      (Function.comp f Complex.ofRealCLM)) a
  choose p hp using hInput
  choose r hr using hp
  refine Exists.intro (Complex.reCLM.compFormalMultilinearSeries p) ?_
  exact Exists.intro r (Complex.reCLM.comp_hasFPowerSeriesOnBall hr)

theorem nicolasJShiftedRealContinuationFilled_analyticAt_zero :
    AnalyticAt Real nicolasJShiftedRealContinuationFilled 0 := by
  unfold nicolasJShiftedRealContinuationFilled
  exact realAnalyticAt_re_comp_of_complexAnalyticAt
    nicolasJShiftedComplexContinuationFilled_analyticAt_zero

end
end Robin1984

end

section
/- Source module Robin1984.NicolasLandau.NicolasLandauFrontier. -/
namespace Robin1984
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
noncomputable section
theorem positive_mem_interior_integrableExpSet_of_two_sided
    {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega -> Real} {mu : Measure Omega}
    {l a r : Real}
    (hl : Membership.mem (integrableExpSet X mu) l)
    (hr : Membership.mem (integrableExpSet X mu) r)
    (hla : l < a) (har : a < r) :
    Membership.mem (interior (integrableExpSet X mu)) a :=
  ProbabilityTheory.positive_mem_interior_integrableExpSet_of_two_sided
    hl hr hla har

theorem Iio_subset_interior_integrableExpSet_of_analyticContinuation
    {Omega : Type*} [MeasurableSpace Omega]
    {X : Omega -> Real} {mu : Measure Omega}
    {b : Real} {H : Real -> Real}
    (hX : Filter.Eventually (fun w => 0 <= X w) (ae mu))
    (hNeg : forall a : Real, a < 0 ->
      Membership.mem (interior (integrableExpSet X mu)) a)
    (hH : forall sigma : Real, sigma < b -> AnalyticAt Real H sigma)
    (hEqNeg : forall a : Real, a < 0 -> mgf X mu a = H a) :
    Iio b <= interior (integrableExpSet X mu) := by
  intro sigma hSigma
  let E : Set Real := integrableExpSet X mu
  let A : Set Real := Set.inter E (Iic sigma)
  let l0 : Real := min (-1) (sigma - 1)
  have hl0Neg : l0 < 0 := by
    dsimp [l0]
    exact lt_of_le_of_lt (min_le_left (-1 : Real) (sigma - 1)) (by norm_num)
  have hl0Sigma : l0 <= sigma := by
    dsimp [l0]
    have hLe := min_le_right (-1 : Real) (sigma - 1)
    linarith
  have hl0E : Membership.mem E l0 := by
    exact interior_subset (hNeg l0 hl0Neg)
  have hANonempty : A.Nonempty :=
    Exists.intro l0 (And.intro hl0E hl0Sigma)
  have hABdd : BddAbove A := by
    exact Exists.intro sigma (fun y hy => hy.2)
  let c : Real := sSup A
  have hcSigma : c <= sigma := by
    dsimp [c]
    exact csSup_le hANonempty (fun y hy => hy.2)
  have hcB : c < b := lt_of_le_of_lt hcSigma hSigma
  have hBelow : forall a : Real, a < c ->
      Membership.mem (interior E) a := by
    intro a ha
    choose r hrA har using (lt_csSup_iff hABdd hANonempty).1 ha
    let l : Real := min (a - 1) (-1)
    have hlNeg : l < 0 := by
      dsimp [l]
      exact lt_of_le_of_lt (min_le_right (a - 1) (-1 : Real)) (by norm_num)
    have hla : l < a := by
      dsimp [l]
      have hLe := min_le_left (a - 1) (-1 : Real)
      linarith
    have hlE : Membership.mem E l := interior_subset (hNeg l hlNeg)
    exact positive_mem_interior_integrableExpSet_of_two_sided
      hlE hrA.1 hla har
  have hMgfAnalytic : AnalyticOnNhd Real (mgf X mu) (Iio c) := by
    intro a ha
    exact analyticAt_mgf (hBelow a ha)
  have hContinuationAnalytic : AnalyticOnNhd Real H (Iio c) := by
    intro a ha
    exact hH a (lt_trans ha hcB)
  let z0 : Real := min (-1) (c - 1)
  have hz0Neg : z0 < 0 := by
    dsimp [z0]
    exact lt_of_le_of_lt (min_le_left (-1 : Real) (c - 1)) (by norm_num)
  have hz0C : z0 < c := by
    dsimp [z0]
    have hLe := min_le_right (-1 : Real) (c - 1)
    linarith
  have hEqNhd : Filter.EventuallyEq (nhds z0) (mgf X mu) H := by
    filter_upwards [Iio_mem_nhds hz0Neg] with a ha
    exact hEqNeg a ha
  have hEqOn : EqOn (mgf X mu) H (Iio c) :=
    hMgfAnalytic.eqOn_of_preconnected_of_eventuallyEq
      hContinuationAnalytic (convex_Iio c).isPreconnected hz0C hEqNhd
  have hEqBelow : forall a : Real, a < c -> mgf X mu a = H a := by
    intro a ha
    exact hEqOn ha
  choose t hct htE using
    exists_integrableExpSet_gt_of_analyticContinuationAt
      hX hBelow (hH c hcB) hEqBelow
  by_cases hSigmaT : sigma < t
  . let l : Real := min (sigma - 1) (-1)
    have hlNeg : l < 0 := by
      dsimp [l]
      exact lt_of_le_of_lt
        (min_le_right (sigma - 1) (-1 : Real)) (by norm_num)
    have hlSigma : l < sigma := by
      dsimp [l]
      have hLe := min_le_left (sigma - 1) (-1 : Real)
      linarith
    have hlE : Membership.mem E l := interior_subset (hNeg l hlNeg)
    exact positive_mem_interior_integrableExpSet_of_two_sided
      hlE htE hlSigma hSigmaT
  . have htSigma : t <= sigma := le_of_not_gt hSigmaT
    have htA : Membership.mem A t := And.intro htE htSigma
    have htc : t <= c := by
      dsimp [c]
      exact le_csSup hABdd htA
    exact (not_lt_of_ge htc hct).elim

end
end Robin1984

end

section
/- Source module Robin1984.NicolasLandau.NicolasLandauPositiveStrip. -/
namespace Robin1984
open Filter MeasureTheory ProbabilityTheory Set
noncomputable section
theorem eventually_nicolasZetaPoleFactor_ne_zero_shift_pos_real
    {sigma : Real} (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 / 2) :
    Filter.Eventually (fun z : Complex => forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        Not (nicolasZetaPoleFactor
          (((u + 1 : Real) : Complex) - z) = 0))
      (nhds (sigma : Complex)) := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro u hu
  have hCenterPos : 0 < u + 1 - sigma := by
    linarith [hu.1]
  have hCenter : Not (nicolasZetaPoleFactor
      ((((u + 1 - sigma : Real) : Complex))) = 0) :=
    nicolasZetaPoleFactor_ne_zero_of_pos_real hCenterPos
  let G : Prod Complex Real -> Complex := fun p =>
    nicolasZetaPoleFactor (((p.2 + 1 : Real) : Complex) - p.1)
  have hGContinuous : Continuous G := by
    dsimp [G]
    exact nicolasZetaPoleFactor_differentiable.continuous.comp (by fun_prop)
  have hGCenter : Not (G ((sigma : Complex), u) = 0) := by
    dsimp [G]
    simpa using hCenter
  exact hGContinuous.continuousAt.eventually_ne hGCenter

theorem exists_nicolasPositiveCompactTubeRadius
    {sigma : Real} (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 / 2) :
    Exists fun R : Real => And (0 < R)
      (forall z : Complex,
        Membership.mem (Metric.ball (sigma : Complex) R) z ->
          And (Not (z = 0))
            (And (dist z (sigma : Complex) < 1 / 4)
              (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
                Not (nicolasZetaPoleFactor
                  (((u + 1 : Real) : Complex) - z) = 0)))) := by
  have hTube := eventually_nicolasZetaPoleFactor_ne_zero_shift_pos_real
    hSigmaPos hSigma
  have hSigmaNe : Not ((sigma : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr hSigmaPos.ne'
  have hZero : Filter.Eventually (fun z : Complex => Not (z = 0))
      (nhds (sigma : Complex)) :=
    continuousAt_id.eventually_ne hSigmaNe
  have hNear : Filter.Eventually (fun z : Complex =>
      dist z (sigma : Complex) < 1 / 4) (nhds (sigma : Complex)) := by
    exact Metric.ball_mem_nhds (sigma : Complex) (by norm_num)
  have hAll := (hTube.and hZero).and hNear
  choose R hRPos hR using Metric.mem_nhds_iff.1 hAll
  refine Exists.intro R (And.intro hRPos ?_)
  intro z hz
  have hAt := hR hz
  exact And.intro hAt.1.2 (And.intro hAt.2 hAt.1.1)

theorem exists_nicolasPositiveCompactKernelBound
    {sigma : Real} (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 / 2) :
    Exists fun R : Real => Exists fun M : Real =>
      And (0 < R) (And (0 <= M)
        (And
          (forall z : Complex,
            Membership.mem (Metric.ball (sigma : Complex) R) z ->
              And (Not (z = 0))
                (And (dist z (sigma : Complex) < 1 / 4)
                  (forall u : Real,
                    Membership.mem (Icc (0 : Real) 1) u ->
                      Not (nicolasZetaPoleFactor
                        (((u + 1 : Real) : Complex) - z) = 0))))
          (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
            forall z : Complex,
              Membership.mem
                (Metric.closedBall (sigma : Complex) (R / 2)) z ->
                norm (nicolasJMellinShiftIntegrandFilled z u) <= M))) := by
  choose R hRPos hR using
    exists_nicolasPositiveCompactTubeRadius hSigmaPos hSigma
  let K : Set (Prod Real Complex) := fun p =>
    And (Membership.mem (Icc (0 : Real) 1) p.1)
      (Membership.mem
        (Metric.closedBall (sigma : Complex) (R / 2)) p.2)
  let F : Prod Real Complex -> Complex := fun p =>
    nicolasJMellinShiftIntegrandFilled p.2 p.1
  have hKCompact : IsCompact K := by
    dsimp [K]
    exact (isCompact_Icc : IsCompact (Icc (0 : Real) 1)).prod
      (isCompact_closedBall (sigma : Complex) (R / 2))
  have hKNonempty : K.Nonempty := by
    refine Exists.intro ((0 : Real), (sigma : Complex)) ?_
    dsimp [K]
    exact And.intro (And.intro le_rfl zero_le_one)
      (Metric.mem_closedBall_self (by linarith))
  have hContinuous : ContinuousOn F K := by
    apply continuousOn_of_forall_continuousAt
    intro p hp
    have hpU : Membership.mem (Icc (0 : Real) 1) p.1 := hp.1
    have hpZClosed : Membership.mem
        (Metric.closedBall (sigma : Complex) (R / 2)) p.2 := hp.2
    have hpZBall : Membership.mem
        (Metric.ball (sigma : Complex) R) p.2 := by
      rw [Metric.mem_closedBall] at hpZClosed
      rw [Metric.mem_ball]
      linarith
    have hpGood := hR p.2 hpZBall
    have hReDiff : abs (p.2.re - sigma) <=
        dist p.2 (sigma : Complex) := by
      rw [dist_eq_norm]
      simpa using Complex.abs_re_le_norm (p.2 - (sigma : Complex))
    have hpZRe : p.2.re < sigma + 1 / 4 := by
      have hAbs : abs (p.2.re - sigma) < 1 / 4 :=
        lt_of_le_of_lt hReDiff hpGood.2.1
      have hUpper : p.2.re - sigma < 1 / 4 :=
        lt_of_le_of_lt (le_abs_self _) hAbs
      linarith
    have hShiftZero : Not
        ((((p.1 + 1 : Real) : Complex) - p.2) = 0) := by
      intro hZero
      have hReZero := congrArg Complex.re hZero
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hReZero
      linarith [hpU.1]
    exact nicolasJMellinShiftIntegrandFilled_joint_continuousAt
      hpU.1 hpGood.1 hShiftZero (hpGood.2.2 p.1 hpU)
  choose p hpK hpMax using hKCompact.exists_isMaxOn hKNonempty hContinuous.norm
  let M : Real := norm (F p)
  refine Exists.intro R (Exists.intro M
    (And.intro hRPos (And.intro (norm_nonneg _) (And.intro hR ?_))))
  intro u hu z hz
  have hPair : K (u, z) := by
    dsimp [K]
    exact And.intro hu hz
  have hBound := hpMax hPair
  simpa [M, F] using hBound

theorem nicolasJMellinShiftIntegrandFilled_continuousOn_u_of_compactTube
    {sigma R : Real} (hSigma : sigma < 1 / 2) (hRPos : 0 < R)
    (hGood : forall z : Complex,
      Membership.mem (Metric.ball (sigma : Complex) R) z ->
        And (Not (z = 0))
          (And (dist z (sigma : Complex) < 1 / 4)
            (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
              Not (nicolasZetaPoleFactor
                (((u + 1 : Real) : Complex) - z) = 0))))
    {z : Complex}
    (hz : Membership.mem
      (Metric.closedBall (sigma : Complex) (R / 2)) z) :
    ContinuousOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Icc (0 : Real) 1) := by
  have hzBall : Membership.mem
      (Metric.ball (sigma : Complex) R) z := by
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    linarith
  have hzGood := hGood z hzBall
  have hReDiff : abs (z.re - sigma) <= dist z (sigma : Complex) := by
    rw [dist_eq_norm]
    simpa using Complex.abs_re_le_norm (z - (sigma : Complex))
  have hzRe : z.re < sigma + 1 / 4 := by
    have hAbs : abs (z.re - sigma) < 1 / 4 :=
      lt_of_le_of_lt hReDiff hzGood.2.1
    have hUpper : z.re - sigma < 1 / 4 :=
      lt_of_le_of_lt (le_abs_self _) hAbs
    linarith
  intro u hu
  have hShiftZero : Not ((((u + 1 : Real) : Complex) - z) = 0) := by
    intro hZero
    have hReZero := congrArg Complex.re hZero
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hReZero
    linarith [hu.1]
  have hJoint := nicolasJMellinShiftIntegrandFilled_joint_continuousAt
    hu.1 hzGood.1 hShiftZero (hzGood.2.2 u hu)
  have hEmbed : ContinuousAt (fun v : Real => (v, z)) u := by
    fun_prop
  have hComp := hJoint.comp_of_eq hEmbed (by rfl)
  have hAt : ContinuousAt (fun v : Real =>
      nicolasJMellinShiftIntegrandFilled z v) u := by
    simpa [Function.comp_def] using hComp
  exact hAt.continuousWithinAt

theorem nicolasJMellinShiftIntegrandFilled_analyticAt_of_compactTube
    {sigma R : Real} (hSigma : sigma < 1 / 2) (hRPos : 0 < R)
    (hGood : forall z : Complex,
      Membership.mem (Metric.ball (sigma : Complex) R) z ->
        And (Not (z = 0))
          (And (dist z (sigma : Complex) < 1 / 4)
            (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
              Not (nicolasZetaPoleFactor
                (((u + 1 : Real) : Complex) - z) = 0))))
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u)
    {z : Complex}
    (hz : Membership.mem
      (Metric.closedBall (sigma : Complex) (R / 2)) z) :
    AnalyticAt Complex (fun w : Complex =>
      nicolasJMellinShiftIntegrandFilled w u) z := by
  have hzBall : Membership.mem
      (Metric.ball (sigma : Complex) R) z := by
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    linarith
  have hzGood := hGood z hzBall
  have hReDiff : abs (z.re - sigma) <= dist z (sigma : Complex) := by
    rw [dist_eq_norm]
    simpa using Complex.abs_re_le_norm (z - (sigma : Complex))
  have hzRe : z.re < sigma + 1 / 4 := by
    have hAbs : abs (z.re - sigma) < 1 / 4 :=
      lt_of_le_of_lt hReDiff hzGood.2.1
    have hUpper : z.re - sigma < 1 / 4 :=
      lt_of_le_of_lt (le_abs_self _) hAbs
    linarith
  have hShiftZero : Not ((((u + 1 : Real) : Complex) - z) = 0) := by
    intro hZero
    have hReZero := congrArg Complex.re hZero
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hReZero
    linarith [hu.1]
  exact
    nicolasJMellinShiftIntegrandFilled_analyticAt_of_ne_zero_of_factor_ne_zero
      hu.1 hzGood.1 hShiftZero (hzGood.2.2 u hu)

theorem deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compactTube
    {sigma R : Real} (hSigma : sigma < 1 / 2) (hRPos : 0 < R)
    (hGood : forall z : Complex,
      Membership.mem (Metric.ball (sigma : Complex) R) z ->
        And (Not (z = 0))
          (And (dist z (sigma : Complex) < 1 / 4)
            (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
              Not (nicolasZetaPoleFactor
                (((u + 1 : Real) : Complex) - z) = 0))))
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (sigma : Complex) (R / 4)) z) :
    AEStronglyMeasurable (fun u : Real =>
      deriv (fun w : Complex =>
        nicolasJMellinShiftIntegrandFilled w u) z)
      (volume.restrict (Ioc (0 : Real) 1)) := by
  let slopeSeq : Nat -> Real -> Complex := fun n : Nat => fun u : Real =>
    slope (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u)
      z (z + nicolasCompactStripDerivativeStep R n)
  have hzDist : dist z (sigma : Complex) < R / 4 := by
    simpa [Metric.mem_ball] using hz
  have hzClosed : Membership.mem
      (Metric.closedBall (sigma : Complex) (R / 2)) z := by
    rw [Metric.mem_closedBall]
    linarith
  have hShiftClosed : forall n : Nat, Membership.mem
      (Metric.closedBall (sigma : Complex) (R / 2))
      (z + nicolasCompactStripDerivativeStep R n) := by
    intro n
    rw [Metric.mem_closedBall]
    calc
      dist (z + nicolasCompactStripDerivativeStep R n) (sigma : Complex) <=
          dist (z + nicolasCompactStripDerivativeStep R n) z +
            dist z (sigma : Complex) :=
        dist_triangle _ z _
      _ = norm (nicolasCompactStripDerivativeStep R n) +
            dist z (sigma : Complex) := by
        rw [dist_eq_norm]
        simp
      _ <= R / 8 + R / 4 :=
        (add_lt_add_of_le_of_lt
          (norm_nicolasCompactStripDerivativeStep_le hRPos n) hzDist).le
      _ <= R / 2 := by linarith
  have hMeas : forall n : Nat, AEMeasurable (slopeSeq n)
      (volume.restrict (Ioc (0 : Real) 1)) := by
    intro n
    have hShift :=
      (nicolasJMellinShiftIntegrandFilled_continuousOn_u_of_compactTube
        hSigma hRPos hGood (hShiftClosed n)).mono Ioc_subset_Icc_self
    have hBase :=
      (nicolasJMellinShiftIntegrandFilled_continuousOn_u_of_compactTube
        hSigma hRPos hGood hzClosed).mono Ioc_subset_Icc_self
    have hShiftMeas : AEStronglyMeasurable
        (fun u : Real => nicolasJMellinShiftIntegrandFilled
          (z + nicolasCompactStripDerivativeStep R n) u)
        (volume.restrict (Ioc (0 : Real) 1)) :=
      hShift.aestronglyMeasurable measurableSet_Ioc
    have hBaseMeas : AEStronglyMeasurable
        (fun u : Real => nicolasJMellinShiftIntegrandFilled z u)
        (volume.restrict (Ioc (0 : Real) 1)) :=
      hBase.aestronglyMeasurable measurableSet_Ioc
    have hEq : slopeSeq n = fun u : Real =>
        Inv.inv ((z + nicolasCompactStripDerivativeStep R n) - z) *
          (nicolasJMellinShiftIntegrandFilled
              (z + nicolasCompactStripDerivativeStep R n) u -
            nicolasJMellinShiftIntegrandFilled z u) := by
      funext u
      dsimp [slopeSeq]
      unfold slope
      simp only [smul_eq_mul, vsub_eq_sub]
    rw [hEq]
    exact ((hShiftMeas.sub hBaseMeas).const_mul
      (Inv.inv ((z + nicolasCompactStripDerivativeStep R n) - z))).aemeasurable
  have hStepWithin : Tendsto (nicolasCompactStripDerivativeStep R) atTop
      (nhdsWithin (0 : Complex) (Set.compl {(0 : Complex)})) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact And.intro (nicolasCompactStripDerivativeStep_tendsto_zero R)
      (Eventually.of_forall (fun n : Nat =>
        Set.mem_compl_singleton_iff.mpr
          (nicolasCompactStripDerivativeStep_ne_zero hRPos n)))
  have hTendsto : Filter.Eventually
      (fun u : Real => Tendsto (fun n : Nat => slopeSeq n u) atTop
        (nhds (deriv (fun w : Complex =>
          nicolasJMellinShiftIntegrandFilled w u) z)))
      (ae (volume.restrict (Ioc (0 : Real) 1))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have huIcc : Membership.mem (Icc (0 : Real) 1) u :=
      Ioc_subset_Icc_self hu
    have hDiffAt : DifferentiableAt Complex
        (fun w : Complex => nicolasJMellinShiftIntegrandFilled w u) z :=
      (nicolasJMellinShiftIntegrandFilled_analyticAt_of_compactTube
        hSigma hRPos hGood huIcc hzClosed).differentiableAt
    have hSlope := hDiffAt.hasDerivAt.tendsto_slope_zero.comp hStepWithin
    change Tendsto (fun n : Nat =>
      Inv.inv (nicolasCompactStripDerivativeStep R n) *
        (nicolasJMellinShiftIntegrandFilled
            (z + nicolasCompactStripDerivativeStep R n) u -
          nicolasJMellinShiftIntegrandFilled z u))
      atTop (nhds (deriv (fun w : Complex =>
        nicolasJMellinShiftIntegrandFilled w u) z)) at hSlope
    dsimp [slopeSeq]
    unfold slope
    simp only [smul_eq_mul, vsub_eq_sub, add_sub_cancel_left]
    exact hSlope
  exact
    (aemeasurable_of_tendsto_metrizable_ae' hMeas hTendsto).aestronglyMeasurable

theorem norm_deriv_nicolasJMellinShiftIntegrandFilled_le_compactTube
    {sigma R M : Real} (hSigma : sigma < 1 / 2) (hRPos : 0 < R)
    (_hMNonneg : 0 <= M)
    (hGood : forall z : Complex,
      Membership.mem (Metric.ball (sigma : Complex) R) z ->
        And (Not (z = 0))
          (And (dist z (sigma : Complex) < 1 / 4)
            (forall u : Real, Membership.mem (Icc (0 : Real) 1) u ->
              Not (nicolasZetaPoleFactor
                (((u + 1 : Real) : Complex) - z) = 0))))
    (hKernelBound : forall u : Real,
      Membership.mem (Icc (0 : Real) 1) u ->
        forall z : Complex,
          Membership.mem
            (Metric.closedBall (sigma : Complex) (R / 2)) z ->
            norm (nicolasJMellinShiftIntegrandFilled z u) <= M)
    {u : Real} (hu : Membership.mem (Icc (0 : Real) 1) u)
    {z : Complex}
    (hz : Membership.mem
      (Metric.ball (sigma : Complex) (R / 4)) z) :
    norm (deriv (fun w : Complex =>
      nicolasJMellinShiftIntegrandFilled w u) z) <= 8 * M / R := by
  let f : Complex -> Complex := fun w =>
    nicolasJMellinShiftIntegrandFilled w u
  let r : Real := R / 4
  have hzDist : dist z (sigma : Complex) < R / 4 := by
    simpa [Metric.mem_ball] using hz
  have hSmallSubset : Metric.ball z r <=
      Metric.closedBall (sigma : Complex) (R / 2) := by
    intro w hw
    rw [Metric.mem_ball] at hw
    rw [Metric.mem_closedBall]
    calc
      dist w (sigma : Complex) <= dist w z + dist z (sigma : Complex) :=
        dist_triangle _ z _
      _ <= R / 4 + R / 4 := by
        dsimp [r] at hw
        exact (add_lt_add hw hzDist).le
      _ <= R / 2 := by linarith
  have hzClosed : Membership.mem
      (Metric.closedBall (sigma : Complex) (R / 2)) z := by
    apply hSmallSubset
    exact Metric.mem_ball_self (by dsimp [r]; linarith)
  have hDiff : DifferentiableOn Complex f (Metric.ball z r) := by
    intro w hw
    exact
      (nicolasJMellinShiftIntegrandFilled_analyticAt_of_compactTube
        hSigma hRPos hGood hu (hSmallSubset hw)).differentiableAt.differentiableWithinAt
  have hMaps : MapsTo f (Metric.ball z r)
      (Metric.closedBall (f z) (2 * M)) := by
    intro w hw
    have hwBound : norm (f w) <= M := by
      dsimp [f]
      exact hKernelBound u hu w (hSmallSubset hw)
    have hzBound : norm (f z) <= M := by
      dsimp [f]
      exact hKernelBound u hu z hzClosed
    rw [Metric.mem_closedBall]
    calc
      dist (f w) (f z) <= norm (f w) + norm (f z) := by
        simpa [dist_eq_norm] using norm_sub_le (f w) (f z)
      _ <= M + M := add_le_add hwBound hzBound
      _ = 2 * M := by ring
  have hCauchy := Complex.norm_deriv_le_div_of_mapsTo_ball
    hDiff hMaps (by dsimp [r]; linarith)
  change norm (deriv f z) <= 8 * M / R
  calc
    norm (deriv f z) <= (2 * M) / r := hCauchy
    _ = 8 * M / R := by
      dsimp [r]
      field_simp [hRPos.ne']
      ring

theorem nicolasJShiftedComplexContinuationFilledCompact_analyticAt_pos_real
    {sigma : Real} (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 / 2) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilledCompact
      (sigma : Complex) := by
  choose R M hRPos hMNonneg hGood hKernelBound using
    exists_nicolasPositiveCompactKernelBound hSigmaPos hSigma
  let s : Set Complex := Metric.ball (sigma : Complex) (R / 4)
  have hHasDeriv : forall z : Complex, Membership.mem s z ->
      HasDerivAt nicolasJShiftedComplexContinuationFilledCompact
        (integral (volume.restrict (Ioc (0 : Real) 1)) (fun u : Real =>
          deriv (fun w : Complex =>
            nicolasJMellinShiftIntegrandFilled w u) z)) z := by
    intro z hz
    let F : Complex -> Real -> Complex := fun w => fun u =>
      nicolasJMellinShiftIntegrandFilled w u
    let F' : Complex -> Real -> Complex := fun w => fun u =>
      deriv (fun v : Complex => nicolasJMellinShiftIntegrandFilled v u) w
    have hsNhd : Membership.mem (nhds z) s := by
      dsimp [s] at hz
      exact Metric.isOpen_ball.mem_nhds hz
    have hFMeas : Filter.Eventually
        (fun w : Complex => AEStronglyMeasurable (F w)
          (volume.restrict (Ioc (0 : Real) 1))) (nhds z) := by
      filter_upwards [hsNhd] with w hw
      have hwDist : dist w (sigma : Complex) < R / 4 := by
        simpa [s, Metric.mem_ball] using hw
      have hwClosed : Membership.mem
          (Metric.closedBall (sigma : Complex) (R / 2)) w := by
        rw [Metric.mem_closedBall]
        linarith
      have hCont :=
        (nicolasJMellinShiftIntegrandFilled_continuousOn_u_of_compactTube
          hSigma hRPos hGood hwClosed).mono Ioc_subset_Icc_self
      dsimp [F]
      exact hCont.aestronglyMeasurable measurableSet_Ioc
    have hzDist : dist z (sigma : Complex) < R / 4 := by
      simpa [s, Metric.mem_ball] using hz
    have hzClosed : Membership.mem
        (Metric.closedBall (sigma : Complex) (R / 2)) z := by
      rw [Metric.mem_closedBall]
      linarith
    have hFInt : Integrable (F z)
        (volume.restrict (Ioc (0 : Real) 1)) := by
      have hCont :=
        nicolasJMellinShiftIntegrandFilled_continuousOn_u_of_compactTube
          hSigma hRPos hGood hzClosed
      have hInt : IntegrableOn (fun u : Real =>
          nicolasJMellinShiftIntegrandFilled z u) (Icc (0 : Real) 1) :=
        by
          apply ContinuousOn.integrableOn_compact isCompact_Icc
          exact hCont
      exact (hInt.mono_set Ioc_subset_Icc_self)
    have hF'Meas : AEStronglyMeasurable (F' z)
        (volume.restrict (Ioc (0 : Real) 1)) := by
      dsimp [F']
      exact
        deriv_nicolasJMellinShiftIntegrandFilled_aestronglyMeasurable_compactTube
          hSigma hRPos hGood (by simpa [s] using hz)
    have hBound : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          norm (F' w u) <= 8 * M / R)
        (ae (volume.restrict (Ioc (0 : Real) 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      intro w hw
      have huIcc : Membership.mem (Icc (0 : Real) 1) u :=
        Ioc_subset_Icc_self hu
      dsimp [F']
      exact norm_deriv_nicolasJMellinShiftIntegrandFilled_le_compactTube
        hSigma hRPos hMNonneg hGood hKernelBound huIcc
          (by simpa [s] using hw)
    have hBoundInt : IntegrableOn (fun _ : Real => 8 * M / R)
        (Ioc (0 : Real) 1) := by
      have hInt : IntegrableOn (fun _ : Real => 8 * M / R)
          (Icc (0 : Real) 1) := by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        exact continuousOn_const
      exact hInt.mono_set Ioc_subset_Icc_self
    have hDiff : Filter.Eventually
        (fun u : Real => forall w : Complex, Membership.mem s w ->
          HasDerivAt (fun v : Complex => F v u) (F' w u) w)
        (ae (volume.restrict (Ioc (0 : Real) 1))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      intro w hw
      have huIcc : Membership.mem (Icc (0 : Real) 1) u :=
        Ioc_subset_Icc_self hu
      have hwDist : dist w (sigma : Complex) < R / 4 := by
        simpa [s, Metric.mem_ball] using hw
      have hwClosed : Membership.mem
          (Metric.closedBall (sigma : Complex) (R / 2)) w := by
        rw [Metric.mem_closedBall]
        linarith
      have hAt :=
        nicolasJMellinShiftIntegrandFilled_analyticAt_of_compactTube
          hSigma hRPos hGood huIcc hwClosed
      dsimp [F, F']
      exact hAt.differentiableAt.hasDerivAt
    have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (bound := fun _ : Real => 8 * M / R)
      hsNhd hFMeas hFInt hF'Meas hBound hBoundInt hDiff
    unfold nicolasJShiftedComplexContinuationFilledCompact
    simpa [F, F'] using hMain.2
  have hDiffOn : DifferentiableOn Complex
      nicolasJShiftedComplexContinuationFilledCompact s := by
    intro z hz
    exact (hHasDeriv z hz).differentiableAt.differentiableWithinAt
  apply hDiffOn.analyticAt
  dsimp [s]
  exact Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self (by linarith : 0 < R / 4))

theorem eventually_nicolasJMellinShiftIntegrandFilled_integrableOn_compact_pos_real
    {sigma : Real} (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 / 2) :
    Filter.Eventually (fun z : Complex =>
      IntegrableOn (fun u : Real =>
        nicolasJMellinShiftIntegrandFilled z u) (Ioc (0 : Real) 1))
      (nhds (sigma : Complex)) := by
  choose R hRPos hGood using
    exists_nicolasPositiveCompactTubeRadius hSigmaPos hSigma
  have hBall : Membership.mem (nhds (sigma : Complex))
      (Metric.ball (sigma : Complex) (R / 2)) :=
    Metric.ball_mem_nhds _ (by linarith)
  filter_upwards [hBall] with z hz
  have hzClosed : Membership.mem
      (Metric.closedBall (sigma : Complex) (R / 2)) z :=
    Metric.ball_subset_closedBall hz
  have hCont :=
    nicolasJMellinShiftIntegrandFilled_continuousOn_u_of_compactTube
      hSigma hRPos hGood hzClosed
  have hInt : IntegrableOn (fun u : Real =>
      nicolasJMellinShiftIntegrandFilled z u) (Icc (0 : Real) 1) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact hCont
  exact hInt.mono_set Ioc_subset_Icc_self

theorem eventually_nicolasJShiftedComplexContinuationFilled_eq_compact_add_large
    {sigma : Real} (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 / 2) :
    Filter.EventuallyEq (nhds (sigma : Complex))
      nicolasJShiftedComplexContinuationFilled
      (fun z : Complex =>
        nicolasJShiftedComplexContinuationFilledCompact z +
          nicolasJShiftedComplexContinuationFilledLarge z) := by
  have hCompact :=
    eventually_nicolasJMellinShiftIntegrandFilled_integrableOn_compact_pos_real
      hSigmaPos hSigma
  have hSigmaHalf : Membership.mem
      (Metric.ball (0 : Complex) (1 / 2 : Real)) (sigma : Complex) := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hSigmaPos]
    exact hSigma
  have hHalf : Membership.mem (nhds (sigma : Complex))
      (Metric.ball (0 : Complex) (1 / 2 : Real)) :=
    Metric.isOpen_ball.mem_nhds hSigmaHalf
  filter_upwards [hCompact, hHalf] with z hCompactInt hzHalf
  have hLargeInt :=
    nicolasJMellinShiftIntegrandFilled_integrableOn_large_half hzHalf
  unfold nicolasJShiftedComplexContinuationFilled
    nicolasJShiftedComplexContinuationFilledCompact
    nicolasJShiftedComplexContinuationFilledLarge
  rw [<- Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : Real) <= 1),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
  . exact hCompactInt
  . exact hLargeInt

theorem nicolasJShiftedComplexContinuationFilled_analyticAt_pos_real
    {sigma : Real} (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 / 2) :
    AnalyticAt Complex nicolasJShiftedComplexContinuationFilled
      (sigma : Complex) := by
  have hCompact :=
    nicolasJShiftedComplexContinuationFilledCompact_analyticAt_pos_real
      hSigmaPos hSigma
  have hLarge :=
    nicolasJShiftedComplexContinuationFilledLarge_analyticAt_pos_real
      hSigmaPos hSigma
  have hSum : AnalyticAt Complex (fun z : Complex =>
      nicolasJShiftedComplexContinuationFilledCompact z +
        nicolasJShiftedComplexContinuationFilledLarge z) (sigma : Complex) :=
    hCompact.add hLarge
  have hEq :=
    eventually_nicolasJShiftedComplexContinuationFilled_eq_compact_add_large
      hSigmaPos hSigma
  exact (analyticAt_congr hEq).mpr hSum

theorem nicolasJShiftedRealContinuationFilled_analyticAt_pos
    {sigma : Real} (hSigmaPos : 0 < sigma) (hSigma : sigma < 1 / 2) :
    AnalyticAt Real nicolasJShiftedRealContinuationFilled sigma := by
  unfold nicolasJShiftedRealContinuationFilled
  exact realAnalyticAt_re_comp_of_complexAnalyticAt
    (nicolasJShiftedComplexContinuationFilled_analyticAt_pos_real
      hSigmaPos hSigma)

end
end Robin1984

end

section
/- Source module Robin1984.NicolasLandau.NicolasLandauComplexFrontier. -/
namespace Robin1984
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
noncomputable section
end
end Robin1984

end

section
/- Source module Robin1984.NicolasLandau.NicolasLandauRightmostRay. -/
namespace Robin1984
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
noncomputable section
def nicolasLandauRpowComplexContinuation
    (X b : Real) (z : Complex) : Complex :=
  (X : Complex) ^ (z - (b : Complex)) / ((b : Complex) - z)

theorem nicolasLandauRpowComplexTailMellin_eq_continuation
    {X b : Real} (hX : 0 < X) {z : Complex} (hz : z.re < b) :
    integral (volume.restrict (Ioi X)) (fun x : Real =>
        (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex)) =
      nicolasLandauRpowComplexContinuation X b z := by
  have hExponent : (z - (b : Complex) - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    linarith
  calc
    integral (volume.restrict (Ioi X)) (fun x : Real =>
        (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex)) =
        integral (volume.restrict (Ioi X)) (fun x : Real =>
          (x : Complex) ^ (z - (b : Complex) - 1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hxPos : 0 < x := hX.trans hx
      have hxNe : Not ((x : Complex) = 0) :=
        Complex.ofReal_ne_zero.mpr hxPos.ne'
      change (x : Complex) ^ (z - 1) *
          ((x ^ (-b) : Real) : Complex) =
        (x : Complex) ^ (z - (b : Complex) - 1)
      rw [Complex.ofReal_cpow hxPos.le]
      rw [<- Complex.cpow_add _ _ hxNe]
      congr 1
      push_cast
      ring
    _ = -(X : Complex) ^ (z - (b : Complex) - 1 + 1) /
          (z - (b : Complex) - 1 + 1) :=
      integral_Ioi_cpow_of_lt hExponent hX
    _ = nicolasLandauRpowComplexContinuation X b z := by
      unfold nicolasLandauRpowComplexContinuation
      have hDen : Not (z - (b : Complex) = 0) := by
        intro hEq
        have hRe := congrArg Complex.re hEq
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hRe
        linarith
      have hDen' : Not ((b : Complex) - z = 0) := by
        exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hDen))
      field_simp [hDen, hDen']
      ring

theorem nicolasLandauRpowComplexContinuation_analyticAt
    {X b : Real} (hX : 0 < X) {z : Complex}
    (hz : Not (z = (b : Complex))) :
    AnalyticAt Complex (nicolasLandauRpowComplexContinuation X b) z := by
  have hXNe : Not ((X : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr hX.ne'
  have hNumerator : AnalyticAt Complex (fun w : Complex =>
      (X : Complex) ^ (w - (b : Complex))) z := by
    have hDiff : Differentiable Complex (fun w : Complex =>
        (X : Complex) ^ (w - (b : Complex))) := by
      intro w
      exact (differentiableAt_id.sub_const (b : Complex)).const_cpow
        (Or.inl hXNe)
    exact hDiff.analyticAt z
  have hDenominator : AnalyticAt Complex
      (fun w : Complex => (b : Complex) - w) z := by
    fun_prop
  unfold nicolasLandauRpowComplexContinuation
  exact hNumerator.div hDenominator (sub_ne_zero.mpr (Ne.symm hz))

theorem nicolasLandauRpowComplexTailMellin_integrableOn
    {X b : Real} (hX : 0 < X) {z : Complex} (hz : z.re < b) :
    IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex))
      (Ioi X) := by
  have hExponent : (z - (b : Complex) - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hBase := integrableOn_Ioi_cpow_of_lt hExponent hX
  apply hBase.congr_fun
  . intro x hx
    have hxPos : 0 < x := hX.trans hx
    have hxNe : Not ((x : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr hxPos.ne'
    change (x : Complex) ^ (z - (b : Complex) - 1) =
      (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex)
    rw [Complex.ofReal_cpow hxPos.le]
    rw [<- Complex.cpow_add _ _ hxNe]
    congr 1
    push_cast
    ring
  . exact measurableSet_Ioi

end
end Robin1984
open MeasureTheory Set Filter ProbabilityTheory Real Robin1984
open scoped Topology
namespace LagariasPositive
end LagariasPositive

end

open Real MeasureTheory Set

namespace LagariasPositive

/- If the complete psi-error tail fails absolute integrability, then the
Bochner convention assigns zero to its integral at every later cutoff. -/
end LagariasPositive

open Real MeasureTheory Set Filter
open scoped Topology

namespace LagariasPositive

end LagariasPositive
end

section
open Real Set MeasureTheory Filter
open scoped Topology

namespace RobinConverse

private theorem wedge_integrable {q : ℝ → ℝ} (hm : Measurable q)
    {C : ℝ} (hC : 0 ≤ C) (hq : ∀ t : ℝ, 3 < t → |q t| ≤ C / t)
    {z : ℂ} (hz : z.re < 0) :
    Integrable ({p : ℝ × ℝ | p.2 < p.1}.indicator
      (fun p : ℝ × ℝ => (p.1 : ℂ) ^ (z - 1) * (q p.2 : ℂ)))
      ((volume.restrict (Ioi (3 : ℝ))).prod (volume.restrict (Ioi (3 : ℝ)))) := by
  let a := z.re / 2
  have ha : a < 0 := by dsimp [a]; linarith
  have hI : IntegrableOn (fun t : ℝ => t ^ (a - 1)) (Ioi 3) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  apply ((hI.const_mul C).mul_prod hI).mono'
  · apply Measurable.aestronglyMeasurable
    apply Measurable.indicator _ (measurableSet_lt measurable_snd measurable_fst)
    exact ((Complex.continuous_ofReal.measurable.comp measurable_fst).pow_const _).mul
      (Complex.continuous_ofReal.measurable.comp (hm.comp measurable_snd))
  · have he : ∀ᵐ p ∂(volume.restrict (Ioi (3:ℝ))).prod (volume.restrict (Ioi (3:ℝ))),
        p ∈ Ioi (3:ℝ) ×ˢ Ioi (3:ℝ) := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi) 
    filter_upwards [he] with p hp
    rcases p with ⟨x,t⟩
    obtain ⟨hx,ht⟩ := hp
    have tx : 0 < x := lt_trans (by norm_num) hx
    have tt : 0 < t := lt_trans (by norm_num) ht
    by_cases htx : t < x
    · rw [Set.indicator_of_mem (show (x,t) ∈ {p : ℝ × ℝ | p.2 < p.1} from htx)]
      change ‖(x:ℂ) ^ (z - 1) * (q t:ℂ)‖ ≤ C * x ^ (a - 1) * t ^ (a - 1)
      rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos tx,Complex.sub_re,Complex.one_re,
        Complex.norm_real,Real.norm_eq_abs]
      have split : z.re - 1 = (a - 1) + a := by dsimp [a]; ring
      rw [split,Real.rpow_add tx,Real.rpow_sub tt a 1,Real.rpow_one]
      calc
        _ ≤ (x ^ (a - 1) * t ^ a) * (C/t) := by
          apply mul_le_mul _ (hq t ht) (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos tt htx.le ha.le) (by positivity)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem (show (x,t) ∉ {p : ℝ × ℝ | p.2 < p.1} from htx),norm_zero]
      change 0 ≤ C * x ^ (a-1) * t ^ (a-1)
      positivity

/-- Mellin transformation of a finite-interval primitive on the negative half-plane.
The wedge t<x supplies the decay required for the interchange of integrals. -/
theorem primitive_mellin {J q : ℝ → ℝ} (hm : Measurable q)
    {C : ℝ} (hC : 0 ≤ C) (hq : ∀ t : ℝ, 3 < t → |q t| ≤ C / t)
    (hJ : ∀ x : ℝ, 3 ≤ x → J 3 - J x = ∫ t in (3:ℝ)..x, q t)
    {z : ℂ} (hz : z.re < 0) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (z - 1) * (J x : ℂ)) (Ioi 3) ∧
    z * (∫ x in Ioi (3:ℝ), (x : ℂ) ^ (z - 1) * (J x : ℂ)) =
      (∫ t in Ioi (3:ℝ), (t : ℂ) ^ z * (q t : ℂ)) - (3:ℂ)^z * (J 3 : ℂ) := by
  let μ : Measure ℝ := volume.restrict (Ioi 3)
  let F := {p : ℝ × ℝ | p.2 < p.1}.indicator
    (fun p : ℝ × ℝ => (p.1 : ℂ) ^ (z - 1) * (q p.2 : ℂ))
  have hi : Integrable F (μ.prod μ) := wedge_integrable hm hC hq hz
  have hz' : (z-1).re < -1 := by simp only [Complex.sub_re,Complex.one_re]; linarith
  have zn : z ≠ 0 := fun e => by subst z; simp at hz
  have I (t : ℝ) (ht : 0 < t) :
      (∫ x in Ioi t, (x : ℂ)^(z-1)) = -(t:ℂ)^z / z := by
    rw [integral_Ioi_cpow_of_lt hz' ht, sub_add_cancel]
  have L (x : ℝ) (hx : 3 < x) :
      (∫ t, F (x,t) ∂μ) = (x:ℂ)^(z-1) * ((J 3:ℂ) - (J x:ℂ)) := by
    change (∫ t in Ioi (3:ℝ), (Iio x).indicator
      (fun t : ℝ => (x:ℂ)^(z-1) * (q t:ℂ)) t) = _
    rw [setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, ← integral_Ioc_eq_integral_Ioo,
      integral_const_mul, ← intervalIntegral.integral_of_le hx.le, intervalIntegral.integral_ofReal,
      ← hJ x hx.le, Complex.ofReal_sub]
  have R (t : ℝ) (ht : 3 < t) :
      (∫ x, F (x,t) ∂μ) = (-(t:ℂ)^z / z) * (q t:ℂ) := by
    change (∫ x in Ioi (3:ℝ), (Ioi t).indicator
      (fun x : ℝ => (x:ℂ)^(z-1) * (q t:ℂ)) x) = _
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi ht.le), integral_mul_const, I t (by linarith)]
  have swap : (∫ x, ∫ t, F (x,t) ∂μ ∂μ) = ∫ t, ∫ x, F (x,t) ∂μ ∂μ :=
    integral_integral_swap (f := fun x t => F (x,t)) hi
  have wI : Integrable (fun x : ℝ => (x:ℂ)^(z-1) * (J 3:ℂ)) μ :=
    (integrableOn_Ioi_cpow_of_lt hz' (by norm_num : 0<(3:ℝ))).mul_const _
  have rep : ∀ᵐ (x : ℝ) ∂μ, (x:ℂ)^(z-1) * (J 3:ℂ) - (∫ t, F (x,t) ∂μ) =
      (x:ℂ)^(z-1) * (J x:ℂ) := by
    filter_upwards [ae_restrict_mem (μ:=volume) (s:=Ioi (3:ℝ)) measurableSet_Ioi] with x hx
    rw [L x hx]; ring
  refine ⟨(wI.sub hi.integral_prod_left).congr rep, ?_⟩
  rw [← integral_congr_ae rep, integral_sub wI hi.integral_prod_left, swap]
  have vr : (∫ t, ∫ x, F (x,t) ∂μ ∂μ) = (-1/z) * ∫ t in Ioi (3:ℝ), (t:ℂ)^z * (q t:ℂ) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change (∫ x, F (x,t) ∂μ) = _
    rw [R t ht]
    ring
  rw [vr]
  change z * ((∫ x in Ioi (3:ℝ), (x:ℂ)^(z-1) * (J 3:ℂ)) - _) = _
  rw [integral_mul_const, I 3 (by norm_num)]
  push_cast
  field_simp
  ring

end RobinConverse
end

section
/- On the half-line, a vanishing function has a vanishing Abel mean for the
power-law probability kernels s*x^(-s-1), as s approaches zero from above. -/
namespace RobinConverse
open Set Real Filter MeasureTheory
open scoped Topology

theorem abel_mellin_limit {J : ℝ → ℝ}
    (hJ : Tendsto J atTop (𝓝 0))
    (compact : ∀ T : ℝ, 3 ≤ T → IntegrableOn J (Ioc 3 T))
    (weights : ∀ s : ℝ, 0 < s →
      IntegrableOn (fun x : ℝ => x ^ (-s-1) * J x) (Ioi 3)) :
    Tendsto (fun s : ℝ => s * ∫ x in Ioi (3:ℝ), x ^ (-s-1) * J x) (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 hJ) (ε/2) (by linarith))
  let T := max 3 N
  have ht : 3 ≤ T := le_max_left _ _
  let B := ∫ x in Ioc (3:ℝ) T, ‖J x‖
  have hb : 0 ≤ B := integral_nonneg (fun _ => norm_nonneg _)
  have small : 0 < ε / (2 * (1+B)) := by positivity
  filter_upwards [Ioo_mem_nhdsGT small] with s hs
  obtain ⟨hs,near⟩ := hs
  have slope : -s-1 < -1 := by linarith
  let f (x : ℝ) := x^(-s-1)*J x
  have hf : IntegrableOn f (Ioi 3) := weights s hs
  have front : ‖∫ x in Ioc (3:ℝ) T, f x‖ ≤ B := by
    apply MeasureTheory.norm_integral_le_of_norm_le (compact T ht).norm
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioc (3:ℝ) T) measurableSet_Ioc] with x hx
    change ‖x^(-s-1)*J x‖ ≤ ‖J x‖
    rw [norm_mul,Real.norm_of_nonneg (Real.rpow_nonneg (by linarith [hx.1]) _)]
    apply mul_le_of_le_one_left (norm_nonneg _)
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hx.1]) (by linarith)
  have tail : s * ‖∫ x in Ioi T, f x‖ ≤ ε/2 := by
    have hTI := (integrableOn_Ioi_rpow_of_lt slope (show 0 < T by linarith)).mul_const (ε/2)
    have hh : ‖∫ x in Ioi T, f x‖ ≤ ∫ x in Ioi T, x^(-s-1)*(ε/2) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hTI
      filter_upwards [ae_restrict_mem (μ := volume) (s := Ioi T) measurableSet_Ioi] with x hx
      have htail := hN x ((le_max_right 3 N).trans hx.le)
      simp only [dist_zero_right] at htail
      change ‖x^(-s-1)*J x‖ ≤ _
      rw [norm_mul,Real.norm_of_nonneg (Real.rpow_nonneg (by linarith [hx.out]) _)]
      exact mul_le_mul_of_nonneg_left htail.le (Real.rpow_nonneg (by linarith [hx.out]) _)
    rw [integral_mul_const,integral_Ioi_rpow_of_lt slope (by linarith),sub_add_cancel] at hh
    have : s * (-(T ^ (-s)) / (-s) * (ε/2)) = T^(-s)*(ε/2) := by field_simp
    calc
      _ ≤ s * (-(T ^ (-s)) / (-s) * (ε/2)) := mul_le_mul_of_nonneg_left hh hs.le
      _ = _ := this
      _ ≤ ε/2 := mul_le_of_le_one_left (by positivity) (Real.rpow_le_one_of_one_le_of_nonpos
        (by linarith) (by linarith))
  have sum : (∫ x in Ioi (3:ℝ), f x) = (∫ x in Ioc (3:ℝ) T, f x) + ∫ x in Ioi T, f x := by
    rw [← intervalIntegral.integral_of_le ht, intervalIntegral.integral_interval_add_Ioi hf
      (hf.mono_set (Ioi_subset_Ioi ht))]
  change dist (s * ∫ x in Ioi (3:ℝ), f x) 0 < ε
  rw [dist_zero_right,norm_mul,Real.norm_of_nonneg hs.le,sum]
  have bound := (norm_add_le (∫ x in Ioc (3:ℝ) T, f x) (∫ x in Ioi T, f x)).trans (add_le_add_left front _)
  have bound' := mul_le_mul_of_nonneg_left bound hs.le
  have hi := (lt_div_iff₀ (show 0 < 2*(1+B) by positivity)).1 near
  rw [mul_add] at bound'
  nlinarith only [tail,hi,hs,bound']
end RobinConverse
end

section
/- Abel boundary value for a Mellin transform of a density with a vanishing
finite-interval primitive. No absolute integrability at exponent zero is needed. -/
namespace RobinConverse
open MeasureTheory Set Real Filter
open scoped Topology

theorem primitive_boundary {q J : ℝ → ℝ} (hm : Measurable q) {C : ℝ}
    (hC : 0 ≤ C) (hq : ∀ t : ℝ, 3 < t → |q t| ≤ C / t)
    (anchor : ∀ x : ℝ, 3 ≤ x → J 3 - J x = ∫ t in (3:ℝ)..x, q t)
    (hJ : Tendsto J atTop (𝓝 0)) :
    Tendsto (fun s : ℝ => ∫ t in Ioi (3:ℝ), (t:ℂ)^(-(s:ℂ)) * (q t:ℂ))
      (𝓝[>] 0) (𝓝 (J 3:ℂ)) := by
  have weight (s : ℝ) (hs : 0 < s) := primitive_mellin hm hC hq anchor
    (z := -(s:ℂ)) (by simpa)
  have castW (s x : ℝ) (hx : 0 ≤ x) :
      (x:ℂ)^(-(s:ℂ)-1) * (J x:ℂ) = ((x^(-s-1)*J x : ℝ):ℂ) := by
    rw [Complex.ofReal_mul,Complex.ofReal_cpow hx,Complex.ofReal_sub,Complex.ofReal_neg,Complex.ofReal_one]
  have weights (s : ℝ) (hs : 0 < s) :
      IntegrableOn (fun x : ℝ => x^(-s-1)*J x) (Ioi 3) := by
    apply (weight s hs).1.re.congr
    filter_upwards [ae_restrict_mem (μ:=volume) (s:=Ioi (3:ℝ)) measurableSet_Ioi] with x hx
    change ((x:ℂ)^(-(s:ℂ)-1) * (J x:ℂ)).re = _
    rw [castW s x (by linarith [hx.out]),Complex.ofReal_re]
  have compact (T : ℝ) (hT : 3 ≤ T) : IntegrableOn J (Ioc 3 T) := by
    have H := (weights 1 (by norm_num)).mono_set (show Ioc (3:ℝ) T ⊆ Ioi 3 from Ioc_subset_Ioi_self)
    have H' := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 H
    have H'' := H'.mul_continuousOn (g := fun x : ℝ => x^2) (by fun_prop)
    apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 H'').congr_fun _ measurableSet_Ioc
    intro x hx
    have hp : 0 < x := by linarith [hx.1]
    change x^(-(1:ℝ)-1)*J x*x^2 = J x
    rw [show -(1:ℝ)-1 = -(2:ℝ) by norm_num,Real.rpow_neg hp.le]
    norm_cast
    field_simp
  have L := (abel_mellin_limit hJ compact weights).neg
  have L' := (Complex.continuous_ofReal.tendsto _).comp L
  have powL : Tendsto (fun s:ℝ => (3:ℂ)^(-(s:ℂ)) * (J 3:ℂ)) (𝓝[>] 0) (𝓝 (J 3:ℂ)) := by
    have hcont : Continuous (fun s:ℝ => (3:ℂ)^(-(s:ℂ)) * (J 3:ℂ)) := by fun_prop
    simpa using (hcont.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
  have joint := L'.add powL
  simp only [neg_zero,Complex.ofReal_zero,zero_add] at joint
  apply joint.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hi := (weight s hs).2
  have eq : (∫ x in Ioi (3:ℝ), (x:ℂ)^(-(s:ℂ)-1)*(J x:ℂ)) =
      ((∫ x in Ioi (3:ℝ), x^(-s-1)*J x : ℝ):ℂ) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact castW _ _ (by linarith [hx.out])
  rw [eq] at hi
  change ((-(s * ∫ x in Ioi (3:ℝ), x ^ (-s-1)*J x) : ℝ):ℂ) + _ = _
  push_cast
  linear_combination hi
end RobinConverse
end

section
open Real Set MeasureTheory Filter
open scoped Topology

namespace RobinConverse

/-- Damping the Frullani transform in its initial half-plane gives absolute
integrability before exchanging the order of integration. -/
theorem damped_frullani {E W : ℝ → ℝ} {P : ℂ → ℂ} (hm : Measurable E)
    {C : ℝ} (hq : ∀ t : ℝ, 3 < t → |E t * W t| ≤ C / t)
    (hk : ∀ t : ℝ, 3 < t →
      IntegrableOn (fun u : ℝ => (u+1) * t ^ (-(u+2))) (Ioi 0))
    (hw : ∀ t : ℝ, 3 < t → W t = ∫ u in Ioi (0:ℝ), (u+1) * t ^ (-(u+2)))
    (hP : ∀ s : ℂ, 1 < s.re →
      (∫ t in Ioi (3:ℝ), (E t:ℂ) * (t:ℂ) ^ (-(s+1))) = P s)
    {z : ℂ} (hz : z.re < 0) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^z * ((E t * W t:ℝ):ℂ)) (Ioi 3) ∧
    IntegrableOn (fun u : ℝ => ((u+1:ℝ):ℂ) * P (((u+1:ℝ):ℂ) - z)) (Ioi 0) ∧
    (∫ t in Ioi (3:ℝ), (t:ℂ)^z * ((E t * W t:ℝ):ℂ)) =
      ∫ u in Ioi (0:ℝ), ((u+1:ℝ):ℂ) * P (((u+1:ℝ):ℂ) - z) := by
  let μ : Measure ℝ := volume.restrict (Ioi 3)
  let ν : Measure ℝ := volume.restrict (Ioi 0)
  let k := fun t u : ℝ => (u+1) * t ^ (-(u+2))
  let F := fun p : ℝ × ℝ => ((p.1:ℂ)^z * (E p.1:ℂ)) * (k p.1 p.2:ℂ)
  have hpos (t u : ℝ) (ht : 3 < t) (hu : 0 < u) : 0 ≤ k t u := by
    dsimp [k]
    positivity
  have K (t : ℝ) (ht : 3 < t) : ∫ u, k t u ∂ν = W t := (hw t ht).symm
  have normRow (t : ℝ) (ht : 3 < t) :
      (∫ u, ‖F (t,u)‖ ∂ν) = t ^ z.re * |E t * W t| := by
    have wp : 0 ≤ W t := by
      rw [← K t ht]
      exact setIntegral_nonneg measurableSet_Ioi (fun u hu => hpos t u ht hu)
    rw [abs_mul,abs_of_nonneg wp, ← K t ht, ← mul_assoc, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change ‖((t:ℂ)^z * (E t:ℂ)) * (k t u:ℂ)‖ = _
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0<t),
      Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (hpos t u ht hu)]
  have fmeas : Measurable F := by
    dsimp [F,k]
    fun_prop
  have hi : Integrable F (μ.prod ν) := by
    apply (integrable_prod_iff fmeas.aestronglyMeasurable).2
    constructor
    · filter_upwards [ae_restrict_mem (μ:=volume) (s:=Ioi (3:ℝ)) measurableSet_Ioi] with t ht
      change Integrable (fun u : ℝ => ((t:ℂ)^z * (E t:ℂ)) * (k t u:ℂ)) ν
      exact (Complex.ofRealCLM.integrable_comp (hk t ht)).const_mul ((t:ℂ)^z * (E t:ℂ))
    · apply ((integrableOn_Ioi_rpow_of_lt (by linarith : z.re-1 < -1)
          (by norm_num : 0<(3:ℝ))).const_mul C).mono'
      · exact fmeas.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      · filter_upwards [ae_restrict_mem (μ:=volume) (s:=Ioi (3:ℝ)) measurableSet_Ioi] with t ht
        have ht0 : 0<t := lt_trans (by norm_num) ht
        rw [normRow t ht,Real.norm_of_nonneg (mul_nonneg (rpow_nonneg ht0.le _) (abs_nonneg _))]
        change t ^ z.re * |E t * W t| ≤ C * t ^ (z.re - 1)
        rw [Real.rpow_sub ht0,Real.rpow_one]
        calc
          _ ≤ t ^ z.re * (C / t) := mul_le_mul_of_nonneg_left (hq t ht) (rpow_nonneg ht0.le _)
          _ = _ := by ring
  have L (t : ℝ) (ht : 3 < t) : (∫ u, F (t,u) ∂ν) = (t:ℂ)^z * ((E t * W t:ℝ):ℂ) := by
    change (∫ u, ((t:ℂ)^z * (E t:ℂ)) * (k t u:ℂ) ∂ν) = _
    rw [integral_const_mul,integral_complex_ofReal,K t ht,Complex.ofReal_mul,mul_assoc]
  have R (u : ℝ) (hu : 0 < u) : (∫ t, F (t,u) ∂μ) =
      ((u+1:ℝ):ℂ) * P (((u+1:ℝ):ℂ) - z) := by
    have hs : 1 < (((u+1:ℝ):ℂ) - z).re := by
      rw [Complex.sub_re,Complex.ofReal_re]; linarith
    rw [← hP _ hs, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := lt_trans (by norm_num) ht
    have tn : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    have expEq : -((((u+1:ℝ):ℂ) - z) + 1) = z + ((-(u+2):ℝ):ℂ) := by push_cast; ring
    change ((t:ℂ)^z * (E t:ℂ)) * (((u+1) * t ^ (-(u+2)):ℝ):ℂ) =
      ((u+1:ℝ):ℂ) * ((E t:ℂ) * (t:ℂ) ^ (-((((u+1:ℝ):ℂ)-z)+1)))
    rw [Complex.ofReal_mul,Complex.ofReal_cpow ht0.le,expEq,Complex.cpow_add _ _ tn]
    ring
  have left := (ae_restrict_mem (μ:=volume) (s:=Ioi (3:ℝ)) measurableSet_Ioi).mono L
  have right := (ae_restrict_mem (μ:=volume) (s:=Ioi (0:ℝ)) measurableSet_Ioi).mono R
  refine ⟨hi.integral_prod_left.congr left, hi.integral_prod_right.congr right, ?_⟩
  rw [← integral_congr_ae left, ← integral_congr_ae right]
  exact integral_integral_swap (f := fun t u => F (t,u)) hi

end RobinConverse
end

section
/- Frullani representation for the damped Nicolas psi-error tail. -/

open Set MeasureTheory Real Robin1984

namespace RobinConverse

theorem weighted_psi_bound {t : ℝ} (ht : 3 < t) :
    |nicolasPsiError t * nicolasTailKernel t| ≤ (2*(log 4+5))/t := by
  have ht0 : 0 < t := lt_trans (by norm_num) ht
  have hlog : 1 < log t := (Real.lt_log_iff_exp_lt ht0).2 (Real.exp_one_lt_three.trans ht)
  have inv : 1 / log t ≤ 1 := (div_le_one (by linarith)).2 hlog.le
  have invsq : 1 / (log t)^2 ≤ 1 := (div_le_one (by positivity)).2 (by nlinarith)
  have nonneg := nicolasTailKernel_nonneg (by linarith : 1 ≤ t)
  rw [abs_mul,abs_of_nonneg nonneg]
  calc
    _ ≤ ((log 4+5)*t)*nicolasTailKernel t :=
      mul_le_mul_of_nonneg_right (abs_nicolasPsiError_le_linear ht0.le) nonneg
    _ ≤ ((log 4+5)*t)*(2/t^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = _ := by field_simp

theorem psi_damped_frullani {z : ℂ} (hz : z.re < 0) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^z * ((nicolasPsiError t * nicolasTailKernel t:ℝ):ℂ)) (Ioi 3) ∧
    IntegrableOn (fun u : ℝ => ((u+1:ℝ):ℂ) * nicolasPsiMellinTailContinuationFilled
      (((u+1:ℝ):ℂ)-z)) (Ioi 0) ∧
    (∫ t in Ioi (3:ℝ), (t:ℂ)^z * ((nicolasPsiError t * nicolasTailKernel t:ℝ):ℂ)) =
      ∫ u in Ioi (0:ℝ), ((u+1:ℝ):ℂ) * nicolasPsiMellinTailContinuationFilled
        (((u+1:ℝ):ℂ)-z) := by
  apply damped_frullani (C:=2*(log 4+5)) (Chebyshev.psi_mono.measurable.sub measurable_id)
    (fun _ ht => weighted_psi_bound ht)
    (fun _ ht => nicolasFrullaniKernel_integrable (by linarith))
    (fun _ ht => nicolasTailKernel_eq_frullani (by linarith)) _ hz
  intro s hs
  rw [nicolasPsiMellinTailContinuationFilled_eq_raw_of_one_lt_re hs]
  exact nicolasPsiErrorTailMellin_eq_continuation (by norm_num) hs

end RobinConverse
end

section
open Real Set Filter MeasureTheory
open scoped Topology

namespace RobinConverse

/-- Continuity under a right translation of the integrable Frullani kernel.
The bound at large arguments is the elementary bound for the psi Mellin transform. -/
theorem frullani_translation {g : ℝ → ℂ} (hg : ∀ v : ℝ, 0 ≤ v → ContinuousAt g v)
    {C : ℝ} (hC : 0 ≤ C) (hdec : ∀ v : ℝ, 1 ≤ v → ‖g v‖ ≤ C*((3:ℝ)^(-v)/v))
    (hI : IntegrableOn (fun u : ℝ => (u+1)*(3:ℝ)^(-(u+2))) (Ioi 0)) :
    IntegrableOn (fun u : ℝ => ((u+1:ℝ):ℂ)*g u) (Ioi 0) ∧
    Tendsto (fun s : ℝ => ∫ u in Ioi (0:ℝ), ((u+1:ℝ):ℂ)*g (u+s))
      (𝓝[>] 0) (𝓝 (∫ u in Ioi (0:ℝ), ((u+1:ℝ):ℂ)*g u)) := by
  have hc : ContinuousOn g (Icc 0 1) := fun v hv => (hg v hv.1).continuousWithinAt
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  let D := max C (3*B)
  have hD : 0 ≤ D := hC.trans (le_max_left _ _)
  have decay (v : ℝ) (hv : 0 ≤ v) : ‖g v‖ ≤ D * (3:ℝ)^(-v) := by
    by_cases h1 : 1 ≤ v
    · calc
        _ ≤ C*((3:ℝ)^(-v)/v) := hdec v h1
        _ ≤ C*(3:ℝ)^(-v) := mul_le_mul_of_nonneg_left (div_le_self (by positivity) h1) hC
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · have hp : 1/3 ≤ (3:ℝ)^(-v) := by
        calc
          (1/3:ℝ) = (3:ℝ)^(-(1:ℝ)) := by norm_num
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      calc
        _ ≤ B := hB v ⟨hv,le_of_not_ge h1⟩
        _ ≤ D * (1/3) := by dsimp [D]; linarith only [le_max_right C (3*B)]
        _ ≤ _ := mul_le_mul_of_nonneg_left hp hD
  let b := fun u : ℝ => (9*D) * ((u+1)*(3:ℝ)^(-(u+2)))
  have hb : IntegrableOn b (Ioi 0) := hI.const_mul _
  have bound {u s : ℝ} (hu : 0<u) (hs : 0 ≤ s) : ‖((u+1:ℝ):ℂ)*g (u+s)‖ ≤ b u := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0<u+1)]
    have hu' : (3:ℝ)^(-u) = (3:ℝ)^(-(u+2))*9 := by
      rw [show -u = -(u+2)+(2:ℝ) by ring,Real.rpow_add (by norm_num)]
      norm_num
    calc
      _ ≤ (u+1)*(D*(3:ℝ)^(-(u+s))) :=
        mul_le_mul_of_nonneg_left (decay _ (by linarith)) (by linarith)
      _ ≤ (u+1)*(D*(3:ℝ)^(-u)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        apply mul_le_mul_of_nonneg_left _ hD
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := by rw [hu']; dsimp [b]; ring
  have meas {s : ℝ} (hs : 0 ≤ s) :
      AEStronglyMeasurable (fun u : ℝ => ((u+1:ℝ):ℂ)*g (u+s)) (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro u hu
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul (by fun_prop)
    change ContinuousAt (g ∘ (fun x : ℝ => x+s)) u
    exact (hg (u+s) (add_nonneg (mem_Ioi.mp hu).le hs)).comp (f := fun x : ℝ => x+s) (x := u) (continuousAt_id.add_const s)
  have ae0 := ae_restrict_mem (μ:=volume) (s:=Ioi (0:ℝ)) measurableSet_Ioi
  constructor
  · apply hb.mono'
    · simpa only [add_zero] using meas (s:=0) le_rfl
    · filter_upwards [ae0] with u hu
      simpa only [add_zero] using bound (s:=0) hu le_rfl
  · apply tendsto_integral_filter_of_dominated_convergence b
    · filter_upwards [self_mem_nhdsWithin] with s hs using meas (mem_Ioi.mp hs).le
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact ae0.mono (fun u hu => bound hu (mem_Ioi.mp hs).le)
    · exact hb
    · filter_upwards [ae0] with u hu
      have h : Tendsto (fun s : ℝ => u+s) (𝓝[>] 0) (𝓝 u) := by
        have hid : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
        simpa only [add_zero] using (tendsto_const_nhds (x:=u)).add hid
      exact tendsto_const_nhds.mul ((hg u (mem_Ioi.mp hu).le).tendsto.comp h)

end RobinConverse
end

section
/- The damped transform at zero and the numerator of its filled continuation. -/
open Real Filter Set MeasureTheory Robin1984
open scoped Topology

namespace RobinConverse

theorem psi_frullani_boundary :
    IntegrableOn (fun u : ℝ => ((u+1:ℝ):ℂ) *
      nicolasPsiMellinTailContinuationFilled ((u+1:ℝ):ℂ)) (Ioi 0) ∧
    Tendsto (fun s : ℝ => ∫ t in Ioi (3:ℝ), (t:ℂ)^(-(s:ℂ)) *
      ((nicolasPsiError t * nicolasTailKernel t:ℝ):ℂ)) (𝓝[>] 0)
        (𝓝 (∫ u in Ioi (0:ℝ), ((u+1:ℝ):ℂ) *
          nicolasPsiMellinTailContinuationFilled ((u+1:ℝ):ℂ))) := by
  let g := fun u : ℝ => nicolasPsiMellinTailContinuationFilled ((u+1:ℝ):ℂ)
  have hc (v : ℝ) (hv : 0≤v) : ContinuousAt g v := by
    exact (nicolasPsiMellinTailContinuationFilled_analyticAt_pos_real
      (by linarith : 0<v+1)).continuousAt.comp (f := fun x : ℝ => ((x+1:ℝ):ℂ)) (x := v) (by fun_prop)
  have hd (v : ℝ) (hv : 1≤v) : ‖g v‖ ≤ (log 4+5)*((3:ℝ)^(-v)/v) := by
    have h := norm_nicolasPsiMellinTailContinuationFilled_le
      (s := ((v+1:ℝ):ℂ)) (by simpa only [Complex.ofReal_re] using (by linarith : 1<v+1))
    simpa only [g,Complex.ofReal_re,add_sub_cancel_right,show 1-(v+1) = -v by ring] using h
  have ext := frullani_translation hc (by positivity : 0≤log 4+5) hd
    (nicolasFrullaniKernel_integrable (by norm_num : 1<(3:ℝ)))
  refine ⟨ext.1, ext.2.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hz : (-(s:ℂ)).re < 0 := by
    change -s < 0
    exact neg_lt_zero.mpr (mem_Ioi.mp hs)
  rw [(psi_damped_frullani hz).2.2]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  change ((u+1:ℝ):ℂ) * nicolasPsiMellinTailContinuationFilled ((u+s+1:ℝ):ℂ) =
    ((u+1:ℝ):ℂ) * nicolasPsiMellinTailContinuationFilled (((u+1:ℝ):ℂ) - (-(s:ℂ)))
  congr 2
  push_cast
  ring

/-- Removing the factor z from the filled shift integrand recovers the
difference of the damped Frullani transform and its basepoint correction. -/
theorem filled_numerator {z : ℂ} (hz : z.re < 0) :
    z * nicolasJShiftedComplexContinuationFilled z =
      (∫ t in Ioi (3:ℝ), (t:ℂ)^z * ((nicolasPsiError t * nicolasTailKernel t:ℝ):ℂ)) -
        (3:ℂ)^z * ∫ u in Ioi (0:ℝ), ((u+1:ℝ):ℂ) *
          nicolasPsiMellinTailContinuationFilled ((u+1:ℝ):ℂ) := by
  let P := nicolasPsiMellinTailContinuationFilled
  let v := fun u : ℝ => ((u+1:ℝ):ℂ)
  have hZ : z ≠ 0 := fun h => by subst z; simp at hz
  have f (u : ℝ) (hu : 0<u) : z * nicolasJMellinShiftIntegrandFilled z u =
      v u * P (v u - z) - (3:ℂ)^z * (v u * P (v u)) := by
    rw [nicolasJMellinShiftIntegrandFilled_eq_raw hz hu]
    dsimp [nicolasJMellinShiftIntegrand,P,v]
    rw [nicolasPsiMellinTailContinuationFilled_eq_raw_of_one_lt_re
          (s := ((u+1:ℝ):ℂ)-z) (by simp only [Complex.sub_re,Complex.ofReal_re]; linarith),
      nicolasPsiMellinTailContinuationFilled_eq_raw_of_one_lt_re
          (s := ((u+1:ℝ):ℂ)) (by simp only [Complex.ofReal_re]; linarith)]
    field_simp
  have hr := psi_damped_frullani hz
  have h0 := psi_frullani_boundary.1
  rw [nicolasJShiftedComplexContinuationFilled, ← integral_const_mul, hr.2.2,
      ← integral_const_mul, ← integral_sub hr.2.1 (h0.const_mul _)]
  exact setIntegral_congr_fun measurableSet_Ioi f

end RobinConverse
end

section
/- The boundary of Nicolas's damped psi-error integral by elementary
prime estimates and Abel convergence. -/
namespace RobinConverse
open MeasureTheory Set Filter Real Robin1984
open scoped Topology

theorem psi_density_measurable : Measurable (fun t : ℝ => nicolasPsiError t * nicolasTailKernel t) := by
  unfold nicolasPsiError nicolasTailKernel
  exact (Chebyshev.psi_mono.measurable.sub measurable_id).mul (by measurability)

theorem psi_boundary :
    Tendsto (fun s : ℝ => ∫ t in Ioi (3:ℝ),
      (t:ℂ)^(-(s:ℂ))*((nicolasPsiError t*nicolasTailKernel t : ℝ):ℂ))
      (𝓝[>] 0) (𝓝 (compensatedPsi 3:ℂ)) :=
  primitive_boundary psi_density_measurable (by positivity : 0 ≤ 2*(log 4+5))
    (fun _ ht => weighted_psi_bound ht) (fun _ hx => compensatedPsi_sub le_rfl hx) compensatedPsi_tendsto

theorem psi_mellin {z : ℂ} (hz : z.re < 0) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(z-1) * (compensatedPsi x:ℂ)) (Ioi 3) ∧
    z*(∫ x in Ioi (3:ℝ), (x:ℂ)^(z-1) * (compensatedPsi x:ℂ)) =
      (∫ u in Ioi (0:ℝ), ((u+1:ℝ):ℂ) *
        nicolasPsiMellinTailContinuationFilled (((u+1:ℝ):ℂ)-z)) -
        (3:ℂ)^z*(compensatedPsi 3:ℂ) := by
  have step := primitive_mellin psi_density_measurable (by positivity : 0 ≤ 2*(log 4+5))
    (fun t ht => weighted_psi_bound ht) (fun _ hx => compensatedPsi_sub le_rfl hx) hz
  exact ⟨step.1, step.2.trans (congrArg (fun y : ℂ => y - _) (psi_damped_frullani hz).2.2)⟩

end RobinConverse
end

section
/- The existing singular continuation is the Mellin transform of the elementary
primitive on the negative half-plane. -/
namespace RobinConverse
open Set Real Filter MeasureTheory Robin1984
open scoped Topology

theorem compensated_mellin_eq {z : ℂ} (hz : z.re < 0) :
    nicolasJShiftedComplexContinuationFilled z =
      ∫ x in Ioi (3:ℝ), (x:ℂ)^(z-1)*(compensatedPsi x:ℂ) := by
  have z0 : z ≠ 0 := fun e => by subst z; simp at hz
  have base := tendsto_nhds_unique psi_boundary psi_frullani_boundary.2
  apply mul_left_cancel₀ z0
  rw [filled_numerator hz, (psi_mellin hz).2, base, (psi_damped_frullani hz).2.2]

theorem compensated_singularity :
    let M : ℂ → ℂ := fun z => ∫ x in Ioi (3:ℝ), (x:ℂ)^(z-1)*(compensatedPsi x:ℂ)
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 1/2 < ρ.re → ρ.re < 1 →
      (∀ v : ℝ, 0 < v → riemannZeta (ρ+(v:ℂ)) ≠ 0) →
      ∃ G : ℝ → ℂ, AnalyticOnNhd ℝ G (Ioi 0) ∧
        (∀ e : ℝ, 1 < e → G e = M (1-ρ-(e:ℂ))) ∧
        Tendsto (fun e => ‖G e‖) (𝓝[>] 0) atTop := by
  dsimp only
  intro ρ hzero hhalf hone hray
  let s := nicolasRightmostRayPoint ρ
  refine ⟨fun e => nicolasJShiftedComplexContinuationFilled (s e), ?_, ?_, ?_⟩
  · intro e he
    have hA := nicolasJShiftedComplexContinuationFilled_analyticAt_rightmostRay
      hzero hhalf hone hray (mem_Ioi.mp he)
    exact hA.restrictScalars.comp_of_eq (analyticAt_const.sub (Complex.ofRealCLM.analyticAt e)) rfl
  · intro e he
    apply compensated_mellin_eq
    simp only [s,nicolasRightmostRayPoint,Complex.sub_re,Complex.one_re,Complex.ofReal_re]
    linarith
  · exact nicolasJShiftedComplexContinuationFilled_rightmostRay_norm_tendsto_atTop
      hzero hhalf hone hray

end RobinConverse
end

section
namespace RobinConverse
open Filter Real Set MeasureTheory
open scoped Topology ArithmeticFunction.sigma
theorem eventual_compensated_lower
    (robin : ∀ n : ℕ, 5040 < n → (σ 1 n : ℝ) < exp eulerMascheroniConstant * n * log (log n))
    (b c : ℝ) (bp : 0 < b) (bh : b < 1/2) (cp : 0 < c) :
    ∀ᶠ x : ℝ in atTop, -(c*x^(-b)) < compensatedPsi x := by
  by_contra bad
  have freq : ∃ᶠ x : ℝ in atTop, c*x^(-b) ≤
      -compensatedPsi x :=
    (Filter.not_eventually.mp bad).mono (fun x hx => by linarith only [le_of_not_gt hx])
  have cmp := (eventually_ge_atTop (3:ℝ)).mono (fun _ hx => finite_product_compensatedPsi hx)
  have small : (fun x : ℝ => x^(-1:ℝ)) =o[atTop] (fun x : ℝ => x^(-b)) :=
    rpow_neg_one_isLittleO_rpow_neg (by linarith)
  have err := small.bound (show 0<c/8 by positivity)
  have loss := arithmetic b bp bh (c/2) (half_pos cp)
  obtain ⟨x,hx,prodBd,step,tailBd,hlarge⟩ :=
    (freq.and_eventually (cmp.and (loss.and (err.and (eventually_ge_atTop (5041:ℝ)))))).exists
  have xp : 0 < x := by linarith only [hlarge]
  simp only [Real.norm_eq_abs, abs_of_pos (rpow_pos_of_pos xp _)] at tailBd
  rw [Real.rpow_neg_one] at tailBd
  rw [div_eq_mul_inv] at prodBd
  let P := ⌊x⌋₊
  let n := Nat.lcmUpto P
  have hP : 5041 ≤ P := (Nat.le_floor_iff xp.le).mpr (by exact_mod_cast hlarge)
  have pn : P ≤ n := Nat.le_of_dvd (Nat.lcmUpto_pos _) (Finset.dvd_lcm (s := Finset.Icc 1 P)
    (f := id) (Finset.mem_Icc.mpr ⟨(by decide : 1 ≤ 5041).trans hP,le_rfl⟩))
  have large : 5040 < n := by omega
  have np : 0 < (n:ℝ) := by exact_mod_cast Nat.lcmUpto_pos P
  have lp : 0 < log (log (n:ℝ)) := by
    apply Real.log_pos
    apply (lt_log_iff_exp_lt np).mpr
    have nl : (5040:ℝ)<n := by exact_mod_cast large
    linarith only [exp_one_lt_three,nl]
  have ap : 0 < (σ 1 n : ℝ)/n := by
    exact div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 n (Nat.ne_of_gt (Nat.lcmUpto_pos P))) np
  have ratio : (σ 1 n : ℝ)/n < exp eulerMascheroniConstant*log (log n) := by
    apply (div_lt_iff₀ np).mpr
    simpa only [mul_right_comm] using robin n large
  have strict := Real.log_lt_log ap ratio
  rw [log_mul (exp_pos _).ne' lp.ne',log_exp] at strict
  change _ ≤ log ((σ 1 n:ℝ)/n)-eulerMascheroniConstant-log (log (log n)) at step
  linarith only [hx,prodBd,step,tailBd,strict]

/-- Positivity of the shifted tail gives holomorphic continuation across every
point of the half-plane to the left of b. The integral fixes its initial germ. -/
def H1 : Prop :=
  let J : ℝ → ℝ := compensatedPsi
  let M : ℂ → ℂ := fun z : ℂ => ∫ x in Ioi (3 : ℝ), (x : ℂ) ^ (z - 1) * (J x : ℂ)
  ∀ b : ℝ, 0 < b → b < 1 / 2 → (∀ᶠ x : ℝ in atTop, 0 ≤ J x + x ^ (-b)) →
    ∃ F : ℂ → ℂ, (∀ z : ℂ, z.re < b → AnalyticAt ℂ F z) ∧
      (∀ z : ℂ, z.re < 0 → F z = M z)

theorem riemannZeta_one_sub_eq_zero_of_nontrivial_zero
    {s : Complex} (hz : riemannZeta s = 0)
    (hNontrivial : Not (Exists fun n : Nat => s = -2 * (n + 1)))
    (hOne : Not (s = 1)) :
    riemannZeta (1 - s) = 0 := by
  have hsZero : Not (s = 0) := by
    intro hs
    subst s
    norm_num [riemannZeta_zero] at hz
  have hCompleted : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hsZero] at hz
    rcases div_eq_zero_iff.mp hz with hCompleted | hGammaFactor
    . exact hCompleted
    . change
        (Real.pi : Complex) ^ (-s / 2) * Complex.Gamma (s / 2) = 0 at hGammaFactor
      rcases mul_eq_zero.mp hGammaFactor with hPiPower | hGamma
      . have hPi : Not ((Real.pi : Complex) = 0) :=
          Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        exact (Complex.cpow_ne_zero_iff.mpr (Or.inl hPi) hPiPower).elim
      . choose m hm using (Complex.Gamma_eq_zero_iff (s / 2)).mp hGamma
        have hsEq : s = -2 * (m : Complex) := by
          calc
            s = 2 * (s / 2) := by ring
            _ = 2 * (-(m : Complex)) := by rw [hm]
            _ = -2 * (m : Complex) := by ring
        cases m with
        | zero => exact (hsZero (by simpa using hsEq)).elim
        | succ n =>
            exact (hNontrivial (Exists.intro n (by
              simpa [Nat.cast_add, Nat.cast_one] using hsEq))).elim
  have hMirrorCompleted : completedRiemannZeta (1 - s) = 0 := by
    rw [completedRiemannZeta_one_sub]
    exact hCompleted
  have hMirrorNeZero : Not (1 - s = 0) :=
    sub_ne_zero.mpr (Ne.symm hOne)
  rw [riemannZeta_def_of_ne_zero hMirrorNeZero, hMirrorCompleted, zero_div]

/-- Failure of RH supplies a zeta zero strictly to the right of the critical
line and strictly inside the critical strip. -/
theorem exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis
    (hNotRH : Not RiemannHypothesis) :
    Exists fun rho : Complex =>
      And (riemannZeta rho = 0)
        (And ((1 / 2 : Real) < rho.re) (rho.re < 1)) := by
  unfold RiemannHypothesis at hNotRH
  push Not at hNotRH
  choose z hz hNontrivial hzOne hzOff using hNotRH
  have hNontrivialExists :
      Not (Exists fun n : Nat => z = -2 * (n + 1)) := by
    intro hExists
    choose n hn using hExists
    exact hNontrivial n hn
  have hzLt : z.re < 1 := by
    by_contra hNotLt
    exact riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hNotLt) hz
  have hMirrorZero : riemannZeta (1 - z) = 0 :=
    riemannZeta_one_sub_eq_zero_of_nontrivial_zero hz hNontrivialExists hzOne
  have hzPos : 0 < z.re := by
    by_contra hNotPos
    have hMirrorRe : 1 <= (1 - z).re := by
      change 1 <= 1 - z.re
      linarith
    exact riemannZeta_ne_zero_of_one_le_re hMirrorRe hMirrorZero
  by_cases hRight : (1 / 2 : Real) < z.re
  . exact Exists.intro z (And.intro hz (And.intro hRight hzLt))
  . have hzLeft : z.re < (1 / 2 : Real) :=
      lt_of_le_of_ne (le_of_not_gt hRight) hzOff
    refine Exists.intro (1 - z) (And.intro hMirrorZero (And.intro ?_ ?_))
    . change (1 / 2 : Real) < 1 - z.re
      linarith
    . change 1 - z.re < (1 : Real)
      linarith

/-- On a horizontal segment ending at real part one, the zero set is closed.
Its rightmost point has an entire zero-free ray to the right. -/
theorem rightmost_zero {z : ℂ} (hz : riemannZeta z = 0)
    (hh : 1 / 2 < z.re) (h1 : z.re < 1) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1 ∧
      ∀ v : ℝ, 0 < v → riemannZeta (ρ + (v : ℂ)) ≠ 0 := by
  let ray := fun t : ℝ => z + (t : ℂ)
  let S := Icc (0 : ℝ) (1 - z.re) ∩ ray ⁻¹' riemannZetaZeros
  have hc : Continuous ray := by dsimp [ray]; fun_prop
  have hs : IsCompact S := isCompact_Icc.inter_right (isClosed_riemannZetaZeros.preimage hc)
  have hmem : (0 : ℝ) ∈ S := by
    refine ⟨⟨le_rfl, by linarith⟩, ?_⟩
    simpa [ray, mem_riemannZetaZeros] using hz
  obtain ⟨t, ht⟩ := hs.exists_isGreatest ⟨0, hmem⟩
  obtain ⟨⟨ht0, ht1⟩, hzt⟩ := ht.1
  have hzero : riemannZeta (ray t) = 0 := hzt
  have hr : (ray t).re = z.re + t := by simp [ray]
  have hlt : (ray t).re < 1 := by
    by_contra! hn
    exact riemannZeta_ne_zero_of_one_le_re hn hzero
  refine ⟨ray t, hzero, by linarith, hlt, ?_⟩
  intro v hv hshift
  have heq : ray (t + v) = ray t + (v : ℂ) := by simp [ray, add_assoc]
  have hupper : (ray t + (v : ℂ)).re < 1 := by
    by_contra! hn
    exact riemannZeta_ne_zero_of_one_le_re hn hshift
  rw [Complex.add_re, Complex.ofReal_re, hr] at hupper
  have hm : t + v ∈ S := by
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    change riemannZeta (ray (t + v)) = 0
    rwa [heq]
  have := ht.2 hm
  linarith

theorem original_converse_of_landau (hLandau : H1) : OMA.R_RiemannHypothesis_robin_criterion_R1.H2 := by
  intro robin
  by_contra hRH
  obtain ⟨z, hz, hh, hlt⟩ := exists_riemannZeta_zero_re_gt_half_of_not_riemannHypothesis hRH
  obtain ⟨ρ, hρ, hhalf, hone, hray⟩ := rightmost_zero hz hh hlt
  let b := ((1 - ρ.re) + 1 / 2) / 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hbHalf : b < 1 / 2 := by dsimp [b]; linarith
  have hbρ : 1 - ρ.re < b := by dsimp [b]; linarith
  have he := eventual_compensated_lower robin b 1 hb hbHalf zero_lt_one
  have hp : ∀ᶠ x : ℝ in atTop, 0 ≤ compensatedPsi x + x^(-b) := by
    filter_upwards [he] with x hx
    rw [one_mul] at hx
    linarith
  obtain ⟨F, hF, hFM⟩ := hLandau b hb hbHalf hp
  obtain ⟨G, hG, hGM, hInf⟩ := compensated_singularity ρ hρ hhalf hone hray
  let s := fun e : ℝ => 1 - ρ - (e : ℂ)
  have hs : ∀ e : ℝ, AnalyticAt ℝ s e :=
    fun e => analyticAt_const.sub (Complex.ofRealCLM.analyticAt e)
  have hA (e : ℝ) (he : 0 ≤ e) : AnalyticAt ℝ (F ∘ s) e := by
    have hsre : (s e).re < b := by
      simp only [s, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
      linarith
    exact (hF _ hsre).restrictScalars.comp_of_eq (hs e) rfl
  have hAon : AnalyticOnNhd ℝ (F ∘ s) (Ioi 0) := fun e he => hA e (mem_Ioi.mp he).le
  have hstart : F ∘ s =ᶠ[𝓝 (2 : ℝ)] G := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2)] with e he
    have he' := mem_Ioi.mp he
    have hleft : (s e).re < 0 := by
      simp only [s, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
      linarith
    exact (hFM _ hleft).trans (hGM _ he').symm
  have hagree : EqOn (F ∘ s) G (Ioi 0) :=
    hAon.eqOn_of_preconnected_of_eventuallyEq hG
      (convex_Ioi (0 : ℝ)).isPreconnected (by norm_num) hstart
  have hfin : Tendsto (fun e => ‖G e‖) (𝓝[>] 0) (𝓝 ‖(F ∘ s) 0‖) := by
    apply ((hA 0 le_rfl).continuousAt.norm.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with e he
    exact congrArg norm (hagree he)
  exact not_tendsto_nhds_of_tendsto_atTop hInf _ hfin

end RobinConverse
end

section
/- Weighted integrability and measurability of the compensated primitive. -/

open MeasureTheory Filter Set Robin1984 Real
open scoped Topology
namespace RobinConverse

theorem compMellin_integrable {z : ℂ} (hz : z.re < 0) :
    IntegrableOn (fun x : ℝ => (x : ℂ)^(z-1) * (compensatedPsi x : ℂ)) (Ioi 3) := (psi_mellin hz).1

theorem compRealMellin_integrable {a : ℝ} (ha : a < 0) :
    IntegrableOn (fun x : ℝ => x^(a-1) * compensatedPsi x) (Ioi 3) := by
  have h := Complex.reCLM.integrable_comp (compMellin_integrable (z := (a:ℂ)) (by simpa using ha))
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hp : 0 ≤ x := (by linarith [show (3:ℝ)<x from hx])
  have he : (a:ℂ)-1 = ((a-1:ℝ):ℂ) := by push_cast; rfl
  change (((x : ℂ) ^ ((a:ℂ)-1) * (compensatedPsi x : ℂ)).re) = _
  rw [he,← Complex.ofReal_cpow hp]
  simp

theorem comp_aemeasurable {X : ℝ} (hX : 3 ≤ X) :
    AEMeasurable compensatedPsi (volume.restrict (Ioi X)) := by
  have h := (compRealMellin_integrable (a := -1) (by norm_num)).mono_set (Ioi_subset_Ioi hX)
  have m : Measurable (fun x : ℝ => x^((-1:ℝ)-1)) := measurable_id.pow_const _
  apply (h.aemeasurable.div m.aemeasurable).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change x^((-1:ℝ)-1)*compensatedPsi x / x^((-1:ℝ)-1) = compensatedPsi x
  exact mul_div_cancel_left₀ _ (Real.rpow_pos_of_pos (by linarith [show X<x from hx]) _).ne'

end RobinConverse
end

section
/- The positive Landau argument specialized to the compensated primitive.
The zeta continuation and the positive-measure crossing argument are imported
from Jonas Whidden's Robin1984 development, as ported in Positive. -/

open Asymptotics Filter Set MeasureTheory ProbabilityTheory Robin1984
open scoped ENNReal Topology
namespace RobinConverse
noncomputable section


def compNicolasJMellin (z : Complex) : Complex :=
  integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
    (x : Complex) ^ (z - 1) * (compensatedPsi x : Complex))

def compNicolasLandauPositiveTail (b x : Real) : Real :=
  compensatedPsi x + x ^ (-b)

def compNicolasLandauPositiveDensity (b x : Real) : ENNReal :=
  ENNReal.ofReal (x ^ (-1 : Real) * compNicolasLandauPositiveTail b x)

def compNicolasLandauPositiveMeasure (X b : Real) : Measure Real :=
  (volume.restrict (Ioi X)).withDensity
    (compNicolasLandauPositiveDensity b)

def compNicolasLandauPositiveMellin (X b a : Real) : Real :=
  integral (volume.restrict (Ioi X)) (fun x : Real =>
    x ^ (a - 1) * compNicolasLandauPositiveTail b x)

def compNicolasJRealMellinStartup (X a : Real) : Real :=
  integral (volume.restrict (Ioc (3 : Real) X)) (fun x : Real =>
    x ^ (a - 1) * compensatedPsi x)

def compNicolasLandauPositiveMellinContinuation (X b a : Real) : Real :=
  nicolasJShiftedRealContinuation a - compNicolasJRealMellinStartup X a +
    nicolasLandauRpowMellinContinuation X b a

theorem compNicolasJ_realMellin_eq_shiftedRealContinuation [hBridge : Fact (∀ z : ℂ, z.re < 0 → Robin1984.nicolasJShiftedComplexContinuationFilled z = ∫ x in Ioi (3:ℝ), (x:ℂ)^(z-1) * (compensatedPsi x:ℂ))]
    {a : Real} (ha : a < 0) :
    integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
        x ^ (a - 1) * compensatedPsi x) =
      nicolasJShiftedRealContinuation a := by
  have hCast :
      ((integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
        x ^ (a - 1) * compensatedPsi x) : Real) : Complex) =
        compNicolasJMellin (a : Complex) := by
    unfold compNicolasJMellin
    calc
      ((integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
          x ^ (a - 1) * compensatedPsi x) : Real) : Complex) =
          integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
            ((x ^ (a - 1) * compensatedPsi x : Real) : Complex)) :=
        integral_ofReal.symm
      _ = integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
          (x : Complex) ^ ((a : Complex) - 1) *
            (compensatedPsi x : Complex)) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hxPos : 0 < x := lt_trans (by norm_num) hx
        have hPower : (x : Complex) ^ ((a : Complex) - 1) =
            ((x ^ (a - 1) : Real) : Complex) := by
          rw [show (a : Complex) - 1 = ((a - 1 : Real) : Complex) by
            push_cast
            rfl]
          rw [<- Complex.ofReal_cpow hxPos.le]
        rw [hPower]
        push_cast
        rfl
  rw [← nicolasJShiftedRealContinuationFilled_eq_raw ha]
  unfold nicolasJShiftedRealContinuationFilled
  rw [hBridge.out (a : ℂ) (by simpa using ha)]
  exact (congrArg Complex.re hCast).symm.symm |> fun h => by simpa [compNicolasJMellin] using h


theorem compNicolasLandauPositiveMellin_eq_continuation_of_neg [hBridge : Fact (∀ z : ℂ, z.re < 0 → Robin1984.nicolasJShiftedComplexContinuationFilled z = ∫ x in Ioi (3:ℝ), (x:ℂ)^(z-1) * (compensatedPsi x:ℂ))]
    {X b a : Real} (hX : 3 <= X) (hb : 0 < b) (ha : a < 0) :
    compNicolasLandauPositiveMellin X b a =
      compNicolasLandauPositiveMellinContinuation X b a := by
  have hJThree := compRealMellin_integrable ha
  have hJX : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * compensatedPsi x) (Ioi X) :=
    hJThree.mono_set (Ioi_subset_Ioi hX)
  have hJStartup : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * compensatedPsi x) (Ioc 3 X) :=
    hJThree.mono_set Ioc_subset_Ioi_self
  have hJSplit :
      integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
          x ^ (a - 1) * compensatedPsi x) =
        compNicolasJRealMellinStartup X a +
          integral (volume.restrict (Ioi X)) (fun x : Real =>
            x ^ (a - 1) * compensatedPsi x) := by
    unfold compNicolasJRealMellinStartup
    rw [<- Ioc_union_Ioi_eq_Ioi hX,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
    . exact hJStartup
    . exact hJX
  have hXPos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have haB : a < b := lt_trans ha hb
  have hRpowBase : IntegrableOn (fun x : Real =>
      x ^ (a - b - 1)) (Ioi X) := by
    rw [integrableOn_Ioi_rpow_iff hXPos]
    linarith
  have hRpow : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * x ^ (-b)) (Ioi X) := by
    apply hRpowBase.congr_fun
    . intro x hx
      have hxPos : 0 < x := hXPos.trans hx
      change x ^ (a - b - 1) = x ^ (a - 1) * x ^ (-b)
      rw [<- Real.rpow_add hxPos]
      congr 1
      ring
    . exact measurableSet_Ioi
  unfold compNicolasLandauPositiveMellin compNicolasLandauPositiveTail
    compNicolasLandauPositiveMellinContinuation
  have hDecomp :
      (fun x : Real => x ^ (a - 1) * (compensatedPsi x + x ^ (-b))) =
        (fun x : Real => x ^ (a - 1) * compensatedPsi x) +
          (fun x : Real => x ^ (a - 1) * x ^ (-b)) := by
    funext x
    dsimp
    ring
  rw [hDecomp]
  change integral (volume.restrict (Ioi X)) (fun x : Real =>
      x ^ (a - 1) * compensatedPsi x + x ^ (a - 1) * x ^ (-b)) =
    nicolasJShiftedRealContinuation a - compNicolasJRealMellinStartup X a +
      nicolasLandauRpowMellinContinuation X b a
  rw [integral_add hJX hRpow]
  rw [nicolasLandauRpowTailMellin_eq_continuation hXPos haB]
  rw [compNicolasJ_realMellin_eq_shiftedRealContinuation ha] at hJSplit
  linarith

theorem compNicolasLandauPositiveTail_integrableOn_of_neg
    {X b a : Real} (hX : 3 <= X) (hb : 0 < b) (ha : a < 0) :
    IntegrableOn (fun x : Real =>
      x ^ (a - 1) * compNicolasLandauPositiveTail b x) (Ioi X) := by
  have hJ : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * compensatedPsi x) (Ioi X) :=
    compRealMellin_integrable ha |>.mono_set
      (Ioi_subset_Ioi hX)
  have hXPos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hPowerBase : IntegrableOn (fun x : Real =>
      x ^ (a - b - 1)) (Ioi X) := by
    rw [integrableOn_Ioi_rpow_iff hXPos]
    linarith
  have hRpow : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * x ^ (-b)) (Ioi X) := by
    apply hPowerBase.congr_fun
    . intro x hx
      have hxPos : 0 < x := hXPos.trans hx
      change x ^ (a - b - 1) = x ^ (a - 1) * x ^ (-b)
      rw [<- Real.rpow_add hxPos]
      congr 1
      ring
    . exact measurableSet_Ioi
  apply (hJ.add hRpow).congr_fun
  . intro x hx
    unfold compNicolasLandauPositiveTail
    change x ^ (a - 1) * compensatedPsi x + x ^ (a - 1) * x ^ (-b) =
      x ^ (a - 1) * (compensatedPsi x + x ^ (-b))
    ring
  . exact measurableSet_Ioi

theorem compNicolasLandauPositiveDensity_aemeasurable
    {X b : Real} (hX : 3 <= X) :
    AEMeasurable (compNicolasLandauPositiveDensity b)
      (volume.restrict (Ioi X)) := by
  have hJ := comp_aemeasurable hX
  have hInv : AEMeasurable (fun x : Real => x ^ (-1 : Real))
      (volume.restrict (Ioi X)) :=
    measurable_id.aemeasurable.pow aemeasurable_const
  have hPower : AEMeasurable (fun x : Real => x ^ (-b))
      (volume.restrict (Ioi X)) :=
    measurable_id.aemeasurable.pow aemeasurable_const
  exact (hInv.mul (hJ.add hPower)).ennreal_ofReal

theorem compAe_log_nonneg_nicolasLandauPositiveMeasure
    {X b : Real} (hX : 3 <= X) :
    Filter.Eventually (fun x : Real => 0 <= Real.log x)
      (ae (compNicolasLandauPositiveMeasure X b)) := by
  have hBase : Filter.Eventually (fun x : Real => 0 <= Real.log x)
      (ae (volume.restrict (Ioi X))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.log_nonneg (le_trans (by norm_num) (hX.trans hx.le))
  exact (withDensity_absolutelyContinuous
    (volume.restrict (Ioi X)) (compNicolasLandauPositiveDensity b)).ae_le hBase

theorem compMgf_log_nicolasLandauPositiveMeasure_eq_mellin
    {X b a : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= compNicolasLandauPositiveTail b x) :
    mgf (fun x : Real => Real.log x)
        (compNicolasLandauPositiveMeasure X b) a =
      compNicolasLandauPositiveMellin X b a := by
  have hDensity := compNicolasLandauPositiveDensity_aemeasurable
    (X := X) (b := b) hX
  let measurableDensity : Real -> ENNReal :=
    hDensity.mk (compNicolasLandauPositiveDensity b)
  have hDensityEq : Filter.Eventually
      (fun x : Real => compNicolasLandauPositiveDensity b x =
        measurableDensity x)
      (ae (volume.restrict (Ioi X))) := hDensity.ae_eq_mk
  have hDensityTop : Filter.Eventually
      (fun x : Real => measurableDensity x < Top.top)
      (ae (volume.restrict (Ioi X))) := by
    filter_upwards [hDensityEq] with x hx
    rw [<- hx]
    exact ENNReal.ofReal_lt_top
  have hMeasureEq :
      (volume.restrict (Ioi X)).withDensity
          (compNicolasLandauPositiveDensity b) =
        (volume.restrict (Ioi X)).withDensity measurableDensity :=
    withDensity_congr_ae hDensityEq
  unfold mgf compNicolasLandauPositiveMeasure
  rw [hMeasureEq, integral_withDensity_eq_integral_toReal_smul
    hDensity.measurable_mk hDensityTop]
  unfold compNicolasLandauPositiveMellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hDensityEq] with x hx hdx
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) (hX.trans hx.le)
  have hTail : 0 <= compNicolasLandauPositiveTail b x := hPos x hx
  have hWeighted : 0 <= x ^ (-1 : Real) *
      compNicolasLandauPositiveTail b x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) hTail
  change (measurableDensity x).toReal * Real.exp (a * Real.log x) =
    x ^ (a - 1) * compNicolasLandauPositiveTail b x
  rw [<- hdx]
  unfold compNicolasLandauPositiveDensity
  rw [ENNReal.toReal_ofReal hWeighted]
  rw [Real.rpow_def_of_pos hxPos, Real.rpow_def_of_pos hxPos]
  calc
    Real.exp (Real.log x * -1) * compNicolasLandauPositiveTail b x *
        Real.exp (a * Real.log x) =
        (Real.exp (Real.log x * -1) *
          Real.exp (a * Real.log x)) *
            compNicolasLandauPositiveTail b x := by ring
    _ = Real.exp (Real.log x * -1 + a * Real.log x) *
        compNicolasLandauPositiveTail b x := by rw [Real.exp_add]
    _ = Real.exp (Real.log x * (a - 1)) *
        compNicolasLandauPositiveTail b x := by
      congr 2
      ring

theorem compMem_integrableExpSet_log_nicolasLandau_iff
    {X b a : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= compNicolasLandauPositiveTail b x) :
    Membership.mem
        (integrableExpSet (fun x : Real => Real.log x)
          (compNicolasLandauPositiveMeasure X b)) a <->
      IntegrableOn (fun x : Real =>
        x ^ (a - 1) * compNicolasLandauPositiveTail b x) (Ioi X) := by
  have hDensity := compNicolasLandauPositiveDensity_aemeasurable
    (X := X) (b := b) hX
  let measurableDensity : Real -> ENNReal :=
    hDensity.mk (compNicolasLandauPositiveDensity b)
  have hDensityEq : Filter.Eventually
      (fun x : Real => compNicolasLandauPositiveDensity b x =
        measurableDensity x)
      (ae (volume.restrict (Ioi X))) := hDensity.ae_eq_mk
  have hDensityTop : Filter.Eventually
      (fun x : Real => measurableDensity x < Top.top)
      (ae (volume.restrict (Ioi X))) := by
    filter_upwards [hDensityEq] with x hx
    rw [<- hx]
    exact ENNReal.ofReal_lt_top
  have hMeasureEq :
      (volume.restrict (Ioi X)).withDensity
          (compNicolasLandauPositiveDensity b) =
        (volume.restrict (Ioi X)).withDensity measurableDensity :=
    withDensity_congr_ae hDensityEq
  change Integrable (fun x : Real => Real.exp (a * Real.log x))
      (compNicolasLandauPositiveMeasure X b) <->
    Integrable (fun x : Real =>
      x ^ (a - 1) * compNicolasLandauPositiveTail b x)
      (volume.restrict (Ioi X))
  unfold compNicolasLandauPositiveMeasure
  rw [hMeasureEq, integrable_withDensity_iff
    hDensity.measurable_mk hDensityTop]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hDensityEq] with x hx hdx
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) (hX.trans hx.le)
  have hTail : 0 <= compNicolasLandauPositiveTail b x := hPos x hx
  have hWeighted : 0 <= x ^ (-1 : Real) *
      compNicolasLandauPositiveTail b x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) hTail
  change Real.exp (a * Real.log x) * (measurableDensity x).toReal =
    x ^ (a - 1) * compNicolasLandauPositiveTail b x
  rw [<- hdx]
  unfold compNicolasLandauPositiveDensity
  rw [ENNReal.toReal_ofReal hWeighted]
  rw [Real.rpow_def_of_pos hxPos, Real.rpow_def_of_pos hxPos]
  calc
    Real.exp (a * Real.log x) *
        (Real.exp (Real.log x * -1) *
          compNicolasLandauPositiveTail b x) =
        (Real.exp (a * Real.log x) *
          Real.exp (Real.log x * -1)) *
            compNicolasLandauPositiveTail b x := by ring
    _ = Real.exp (a * Real.log x + Real.log x * -1) *
        compNicolasLandauPositiveTail b x := by rw [Real.exp_add]
    _ = Real.exp (Real.log x * (a - 1)) *
        compNicolasLandauPositiveTail b x := by
      congr 2
      ring

theorem compInterior_integrableExpSet_log_nicolasLandau_of_below
    {X b sigma : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= compNicolasLandauPositiveTail b x)
    (hBelow : forall a : Real, a < sigma ->
      IntegrableOn (fun x : Real =>
        x ^ (a - 1) * compNicolasLandauPositiveTail b x) (Ioi X)) :
    forall a : Real, a < sigma ->
      Membership.mem
        (interior (integrableExpSet (fun x : Real => Real.log x)
          (compNicolasLandauPositiveMeasure X b))) a := by
  intro a ha
  rw [mem_interior_iff_mem_nhds]
  let eps : Real := (sigma - a) / 2
  have hEps : 0 < eps := by
    dsimp [eps]
    linarith
  apply mem_of_superset (Metric.ball_mem_nhds a hEps)
  intro y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have hySigma : y < sigma := by
    have hAbs := (abs_lt.mp hy).2
    dsimp [eps] at hAbs
    linarith
  exact (compMem_integrableExpSet_log_nicolasLandau_iff hX hPos).2
    (hBelow y hySigma)

def compNicolasJComplexMellinStartup (X : Real) (s : Complex) : Complex :=
  integral (volume.restrict (Ioc (3 : Real) X)) (fun x : Real =>
    (x : Complex) ^ (s - 1) * (compensatedPsi x : Complex))

theorem compNicolasJComplexMellinStartup_differentiableAt
    {X : Real} (hX : 3 <= X) (s0 : Complex) :
    DifferentiableAt Complex (compNicolasJComplexMellinStartup X) s0 := by
  let F : Complex -> Real -> Complex := fun s x =>
    (x : Complex) ^ (s - 1) * (compensatedPsi x : Complex)
  let F' : Complex -> Real -> Complex := fun s x =>
    ((Real.log x : Real) : Complex) * F s x
  let base : Real -> Complex := fun x =>
    (x : Complex) ^ (-3 : Complex) * (compensatedPsi x : Complex)
  let ratio : Complex -> Real -> Complex := fun s x =>
    (x : Complex) ^ (s + 2)
  let majorant : Real -> Real := fun x =>
    norm (base x) * X ^ (abs s0.re + 4)
  have hRealBase : IntegrableOn (fun x : Real =>
      x ^ (-3 : Real) * compensatedPsi x) (Ioc (3 : Real) X) := by
    have h := compRealMellin_integrable
      (a := (-2 : Real)) (by norm_num)
    have hRestricted := h.mono_set
      (show Ioc (3 : Real) X <= Ioi 3 from Ioc_subset_Ioi_self)
    apply hRestricted.congr_fun
    . intro x hx
      norm_num
    . exact measurableSet_Ioc
  have hCastBase : IntegrableOn (fun x : Real =>
      ((x ^ (-3 : Real) * compensatedPsi x : Real) : Complex))
      (Ioc (3 : Real) X) :=
    Complex.ofRealCLM.integrable_comp hRealBase
  have hBaseIntegrable : Integrable base
      (volume.restrict (Ioc (3 : Real) X)) := by
    apply hCastBase.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxPos : 0 < x := lt_trans (by norm_num) hx.1
    dsimp [base]
    rw [show (-3 : Complex) = ((-3 : Real) : Complex) by norm_num,
      <- Complex.ofReal_cpow hxPos.le]
    push_cast
    rfl
  have hXPos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hMajorantIntegrable : Integrable majorant
      (volume.restrict (Ioc (3 : Real) X)) := by
    have h := hBaseIntegrable.norm.const_mul
      (X ^ (abs s0.re + 4))
    simpa [majorant, mul_comm] using h
  have hMeasurable : forall s : Complex, AEStronglyMeasurable (F s)
      (volume.restrict (Ioc (3 : Real) X)) := by
    intro s
    have hRatioContinuous : ContinuousOn (ratio s) (Ioc (3 : Real) X) := by
      apply continuousOn_of_forall_continuousAt
      intro x hx
      dsimp [ratio]
      have hxPos : 0 < x := lt_trans (by norm_num) hx.1
      exact (continuousAt_cpow_const
        (Complex.ofReal_mem_slitPlane.2 hxPos)).comp
          Complex.continuous_ofReal.continuousAt
    have hProduct := hBaseIntegrable.aestronglyMeasurable.mul
      (hRatioContinuous.aestronglyMeasurable measurableSet_Ioc)
    apply hProduct.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hxPos : 0 < x := lt_trans (by norm_num) hx.1
    have hxZero : Not ((x : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hxPos)
    have hPower : (x : Complex) ^ (-3 : Complex) *
        (x : Complex) ^ (s + 2) = (x : Complex) ^ (s - 1) := by
      rw [<- Complex.cpow_add _ _ hxZero]
      congr 1
      ring
    dsimp [F, base, ratio]
    calc
      (x : Complex) ^ (-3 : Complex) * (compensatedPsi x : Complex) *
          (x : Complex) ^ (s + 2) =
          ((x : Complex) ^ (-3 : Complex) *
            (x : Complex) ^ (s + 2)) * (compensatedPsi x : Complex) := by ring
      _ = (x : Complex) ^ (s - 1) * (compensatedPsi x : Complex) := by
        rw [hPower]
  have hBound : forall s : Complex, dist s s0 < 1 ->
      forall x : Real, 3 < x -> x <= X ->
        norm (F s x) <= majorant x := by
    intro s hs x hxThree hxX
    have hDist : norm (s - s0) < 1 := by
      simpa [dist_eq_norm] using hs
    have hReAbs : abs (s.re - s0.re) <= norm (s - s0) := by
      simpa using Complex.abs_re_le_norm (s - s0)
    have hReUpper : s.re < s0.re + 1 := by
      have hAbsLt : abs (s.re - s0.re) < 1 := lt_of_le_of_lt hReAbs hDist
      linarith [(abs_lt.mp hAbsLt).2]
    have hxPos : 0 < x := lt_trans (by norm_num) hxThree
    have hxOne : 1 <= x := by linarith
    have hExponent : s.re + 2 <= abs s0.re + 4 := by
      have hPosPart : s0.re <= abs s0.re := le_abs_self s0.re
      linarith
    have hExponentNonneg : 0 <= abs s0.re + 4 := by positivity
    have hRatioBound : norm (ratio s x) <=
        X ^ (abs s0.re + 4) := by
      dsimp [ratio]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxPos]
      calc
        x ^ (s.re + 2) <= x ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow_of_exponent_le hxOne hExponent
        _ <= X ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow hxPos.le hxX hExponentNonneg
    have hxZero : Not ((x : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hxPos)
    have hFactor : F s x = base x * ratio s x := by
      have hPower : (x : Complex) ^ (-3 : Complex) *
          (x : Complex) ^ (s + 2) = (x : Complex) ^ (s - 1) := by
        rw [<- Complex.cpow_add _ _ hxZero]
        congr 1
        ring
      dsimp [F, base, ratio]
      calc
        (x : Complex) ^ (s - 1) * (compensatedPsi x : Complex) =
            ((x : Complex) ^ (-3 : Complex) *
              (x : Complex) ^ (s + 2)) * (compensatedPsi x : Complex) := by
          rw [hPower]
        _ = ((x : Complex) ^ (-3 : Complex) *
            (compensatedPsi x : Complex)) * (x : Complex) ^ (s + 2) := by ring
    rw [hFactor, norm_mul]
    dsimp [majorant]
    exact mul_le_mul_of_nonneg_left hRatioBound (norm_nonneg (base x))
  have hFIntegrable : Integrable (F s0)
      (volume.restrict (Ioc (3 : Real) X)) := by
    apply Integrable.mono hMajorantIntegrable (hMeasurable s0)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hMajorantNonneg : 0 <= majorant x := by
      dsimp [majorant]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hMajorantNonneg]
    exact hBound s0 (by simp [dist_self]) x hx.1 hx.2
  have hDerivativeMeasurable : AEStronglyMeasurable (F' s0)
      (volume.restrict (Ioc (3 : Real) X)) := by
    have hRealLogOn : ContinuousOn (fun x : Real => Real.log x)
        (Ioc (3 : Real) X) := by
      apply Real.continuousOn_log.mono
      intro x hx
      exact Set.mem_compl_singleton_iff.mpr
        (ne_of_gt (lt_trans (by norm_num) hx.1))
    have hRealLog : AEStronglyMeasurable (fun x : Real => Real.log x)
        (volume.restrict (Ioc (3 : Real) X)) :=
      hRealLogOn.aestronglyMeasurable measurableSet_Ioc
    have hLog : AEStronglyMeasurable
        (fun x : Real => ((Real.log x : Real) : Complex))
        (volume.restrict (Ioc (3 : Real) X)) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hRealLog
    exact hLog.mul (hMeasurable s0)
  have hDerivativeBound : Filter.Eventually
      (fun x : Real => forall s : Complex, Membership.mem (Metric.ball s0 1) s ->
        norm (F' s x) <= X * majorant x)
      (ae (volume.restrict (Ioc (3 : Real) X))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    intro s hs
    have hxPos : 0 < x := lt_trans (by norm_num) hx.1
    have hxOne : 1 <= x := by linarith [hx.1]
    have hLogNonneg : 0 <= Real.log x := Real.log_nonneg hxOne
    have hLogBound : Real.log x <= X := by
      have hLogSub := Real.log_le_sub_one_of_pos hxPos
      linarith [hx.2]
    have hFBound : norm (F s x) <= majorant x :=
      hBound s (by simpa [Metric.mem_ball] using hs) x hx.1 hx.2
    dsimp [F']
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hLogNonneg]
    exact mul_le_mul hLogBound hFBound (norm_nonneg _) hXPos.le
  have hDerivativeIntegrable : Integrable (fun x : Real => X * majorant x)
      (volume.restrict (Ioc (3 : Real) X)) :=
    hMajorantIntegrable.const_mul X
  have hDerivative : Filter.Eventually
      (fun x : Real => forall s : Complex, Membership.mem (Metric.ball s0 1) s ->
        HasDerivAt (fun z : Complex => F z x) (F' s x) s)
      (ae (volume.restrict (Ioc (3 : Real) X))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    intro s hs
    have hxPos : 0 < x := lt_trans (by norm_num) hx.1
    have hxZero : Not ((x : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hxPos)
    have hExponent : HasDerivAt (fun z : Complex => z - 1) 1 s :=
      (hasDerivAt_id' s).sub_const 1
    have hPower := hExponent.const_cpow (Or.inl hxZero)
    have hProduct := hPower.mul_const (compensatedPsi x : Complex)
    dsimp [F, F']
    apply hProduct.congr_deriv
    rw [Complex.ofReal_log hxPos.le]
    ring
  unfold compNicolasJComplexMellinStartup
  have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s0 zero_lt_one)
    (Eventually.of_forall hMeasurable) hFIntegrable
    hDerivativeMeasurable hDerivativeBound hDerivativeIntegrable hDerivative
  exact hMain.2.differentiableAt

theorem compNicolasJComplexMellinStartup_analyticAt
    {X : Real} (hX : 3 <= X) (s0 : Complex) :
    AnalyticAt Complex (compNicolasJComplexMellinStartup X) s0 := by
  have hDifferentiable : Differentiable Complex
      (compNicolasJComplexMellinStartup X) := by
    intro s
    exact compNicolasJComplexMellinStartup_differentiableAt hX s
  exact hDifferentiable.analyticAt s0

def compNicolasLandauPositiveMellinContinuationFilled
    (X b a : Real) : Real :=
  nicolasJShiftedRealContinuationFilled a -
    Complex.re (compNicolasJComplexMellinStartup X (a : Complex)) +
      nicolasLandauRpowMellinContinuation X b a

theorem compNicolasLandauPositiveMellinContinuationFilled_analyticAt_zero
    {X b : Real} (hX : 3 <= X) (hb : 0 < b) :
    AnalyticAt Real (compNicolasLandauPositiveMellinContinuationFilled X b) 0 := by
  have hStartup : AnalyticAt Real
      (fun a : Real =>
        Complex.re (compNicolasJComplexMellinStartup X (a : Complex))) 0 :=
    realAnalyticAt_re_comp_of_complexAnalyticAt
      (compNicolasJComplexMellinStartup_analyticAt hX 0)
  have hRpow := nicolasLandauRpowMellinContinuation_analyticAt
    (X := X) (b := b) (sigma := (0 : Real))
    (lt_of_lt_of_le (by norm_num) hX) hb
  unfold compNicolasLandauPositiveMellinContinuationFilled
  exact nicolasJShiftedRealContinuationFilled_analyticAt_zero.sub
    hStartup |>.add hRpow

theorem compRe_nicolasJComplexMellinStartup_eq_real_of_neg
    {X a : Real} (_hX : 3 <= X) (ha : a < 0) :
    Complex.re (compNicolasJComplexMellinStartup X (a : Complex)) =
      compNicolasJRealMellinStartup X a := by
  have hReal : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * compensatedPsi x) (Ioc (3 : Real) X) :=
    (compRealMellin_integrable ha).mono_set
      Ioc_subset_Ioi_self
  have hCast : IntegrableOn (fun x : Real =>
      ((x ^ (a - 1) * compensatedPsi x : Real) : Complex))
      (Ioc (3 : Real) X) :=
    Complex.ofRealCLM.integrable_comp hReal
  have hComplex : IntegrableOn (fun x : Real =>
      (x : Complex) ^ ((a : Complex) - 1) * (compensatedPsi x : Complex))
      (Ioc (3 : Real) X) := by
    apply hCast.congr_fun
    . intro x hx
      have hxPos : 0 < x := lt_trans (by norm_num) hx.1
      change ((x ^ (a - 1) * compensatedPsi x : Real) : Complex) =
        (x : Complex) ^ ((a : Complex) - 1) * (compensatedPsi x : Complex)
      rw [show (a : Complex) - 1 = ((a - 1 : Real) : Complex) by
        push_cast
        rfl]
      rw [<- Complex.ofReal_cpow hxPos.le (a - 1)]
      push_cast
      rfl
    . exact measurableSet_Ioc
  have hRe := integral_re hComplex
  unfold compNicolasJComplexMellinStartup compNicolasJRealMellinStartup
  calc
    Complex.re (integral (volume.restrict (Ioc (3 : Real) X))
        (fun x : Real =>
          (x : Complex) ^ ((a : Complex) - 1) * (compensatedPsi x : Complex))) =
        integral (volume.restrict (Ioc (3 : Real) X)) (fun x : Real =>
          Complex.re ((x : Complex) ^ ((a : Complex) - 1) *
            (compensatedPsi x : Complex))) := hRe.symm
    _ = integral (volume.restrict (Ioc (3 : Real) X)) (fun x : Real =>
          x ^ (a - 1) * compensatedPsi x) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      have hxPos : 0 < x := lt_trans (by norm_num) hx.1
      rw [show (a : Complex) - 1 = ((a - 1 : Real) : Complex) by
        push_cast
        rfl]
      have hPoint :
          (x : Complex) ^ ((a - 1 : Real) : Complex) *
              (compensatedPsi x : Complex) =
            ((x ^ (a - 1) * compensatedPsi x : Real) : Complex) := by
        calc
          (x : Complex) ^ ((a - 1 : Real) : Complex) *
                (compensatedPsi x : Complex) =
              ((x ^ (a - 1) : Real) : Complex) *
                (compensatedPsi x : Complex) := by
            congr 1
            exact (Complex.ofReal_cpow hxPos.le (a - 1)).symm
          _ = ((x ^ (a - 1) * compensatedPsi x : Real) : Complex) := by
            push_cast
            rfl
      change Complex.re
          ((x : Complex) ^ ((a - 1 : Real) : Complex) *
            (compensatedPsi x : Complex)) =
        x ^ (a - 1) * compensatedPsi x
      rw [hPoint]
      simp

theorem compNicolasLandauPositiveMellinContinuationFilled_eq_raw_of_neg
    {X b a : Real} (hX : 3 <= X) (ha : a < 0) :
    compNicolasLandauPositiveMellinContinuationFilled X b a =
      compNicolasLandauPositiveMellinContinuation X b a := by
  unfold compNicolasLandauPositiveMellinContinuationFilled
    compNicolasLandauPositiveMellinContinuation
  rw [nicolasJShiftedRealContinuationFilled_eq_raw ha,
    compRe_nicolasJComplexMellinStartup_eq_real_of_neg hX ha]

theorem compNicolasLandauPositiveMellinContinuationFilled_analyticAt_pos
    {X b sigma : Real} (hX : 3 <= X) (hSigmaPos : 0 < sigma)
    (hSigmaHalf : sigma < 1 / 2) (hSigmaB : sigma < b) :
    AnalyticAt Real (compNicolasLandauPositiveMellinContinuationFilled X b)
      sigma := by
  have hShift : AnalyticAt Real nicolasJShiftedRealContinuationFilled sigma :=
    nicolasJShiftedRealContinuationFilled_analyticAt_pos
      hSigmaPos hSigmaHalf
  have hStartup : AnalyticAt Real
      (fun a : Real =>
        Complex.re (compNicolasJComplexMellinStartup X (a : Complex))) sigma :=
    realAnalyticAt_re_comp_of_complexAnalyticAt
      (compNicolasJComplexMellinStartup_analyticAt hX (sigma : Complex))
  have hRpow : AnalyticAt Real
      (nicolasLandauRpowMellinContinuation X b) sigma :=
    nicolasLandauRpowMellinContinuation_analyticAt
      (lt_of_lt_of_le (by norm_num) hX) hSigmaB
  unfold compNicolasLandauPositiveMellinContinuationFilled
  exact (hShift.sub hStartup).add hRpow

theorem compNicolasLandauPositiveMellinContinuationFilled_analyticAt_neg [hBridge : Fact (∀ z : ℂ, z.re < 0 → Robin1984.nicolasJShiftedComplexContinuationFilled z = ∫ x in Ioi (3:ℝ), (x:ℂ)^(z-1) * (compensatedPsi x:ℂ))]
    {X b sigma : Real} (hX : 3 <= X) (hb : 0 < b)
    (hPos : forall x : Real, X < x ->
      0 <= compNicolasLandauPositiveTail b x)
    (hSigma : sigma < 0) :
    AnalyticAt Real (compNicolasLandauPositiveMellinContinuationFilled X b)
      sigma := by
  have hBelow : forall a : Real, a < 0 ->
      IntegrableOn (fun x : Real =>
        x ^ (a - 1) * compNicolasLandauPositiveTail b x) (Ioi X) := by
    intro a ha
    exact compNicolasLandauPositiveTail_integrableOn_of_neg hX hb ha
  have hInterior : Membership.mem
      (interior (integrableExpSet (fun x : Real => Real.log x)
        (compNicolasLandauPositiveMeasure X b))) sigma :=
    compInterior_integrableExpSet_log_nicolasLandau_of_below
      hX hPos hBelow sigma hSigma
  have hMgf : AnalyticAt Real
      (mgf (fun x : Real => Real.log x)
        (compNicolasLandauPositiveMeasure X b)) sigma :=
    analyticAt_mgf hInterior
  have hEq : Filter.EventuallyEq (nhds sigma)
      (mgf (fun x : Real => Real.log x)
        (compNicolasLandauPositiveMeasure X b))
      (compNicolasLandauPositiveMellinContinuationFilled X b) := by
    filter_upwards [Iio_mem_nhds hSigma] with a ha
    rw [compMgf_log_nicolasLandauPositiveMeasure_eq_mellin hX hPos]
    calc
      compNicolasLandauPositiveMellin X b a =
          compNicolasLandauPositiveMellinContinuation X b a :=
        compNicolasLandauPositiveMellin_eq_continuation_of_neg hX hb ha
      _ = compNicolasLandauPositiveMellinContinuationFilled X b a :=
        (compNicolasLandauPositiveMellinContinuationFilled_eq_raw_of_neg
          hX ha).symm
  exact (analyticAt_congr hEq).mp hMgf

theorem compNicolasLandauPositiveMellinContinuationFilled_analyticAt_lt [hBridge : Fact (∀ z : ℂ, z.re < 0 → Robin1984.nicolasJShiftedComplexContinuationFilled z = ∫ x in Ioi (3:ℝ), (x:ℂ)^(z-1) * (compensatedPsi x:ℂ))]
    {X b sigma : Real} (hX : 3 <= X) (hb : 0 < b)
    (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x ->
      0 <= compNicolasLandauPositiveTail b x)
    (hSigma : sigma < b) :
    AnalyticAt Real (compNicolasLandauPositiveMellinContinuationFilled X b)
      sigma := by
  rcases lt_trichotomy sigma 0 with hSigmaNeg | hSigmaZero | hSigmaPos
  . exact compNicolasLandauPositiveMellinContinuationFilled_analyticAt_neg
      hX hb hPos hSigmaNeg
  . subst sigma
    exact compNicolasLandauPositiveMellinContinuationFilled_analyticAt_zero hX hb
  . exact compNicolasLandauPositiveMellinContinuationFilled_analyticAt_pos
      hX hSigmaPos (lt_of_lt_of_le hSigma hbHalf) hSigma

theorem compIio_subset_interior_integrableExpSet_nicolasLandau_of_positive [hBridge : Fact (∀ z : ℂ, z.re < 0 → Robin1984.nicolasJShiftedComplexContinuationFilled z = ∫ x in Ioi (3:ℝ), (x:ℂ)^(z-1) * (compensatedPsi x:ℂ))]
    {X b : Real} (hX : 3 <= X) (hb : 0 < b) (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x ->
      0 <= compNicolasLandauPositiveTail b x) :
    Iio b <= interior
      (integrableExpSet (fun x : Real => Real.log x)
        (compNicolasLandauPositiveMeasure X b)) := by
  have hBelow : forall a : Real, a < 0 ->
      IntegrableOn (fun x : Real =>
        x ^ (a - 1) * compNicolasLandauPositiveTail b x) (Ioi X) := by
    intro a ha
    exact compNicolasLandauPositiveTail_integrableOn_of_neg hX hb ha
  have hNeg : forall a : Real, a < 0 -> Membership.mem
      (interior (integrableExpSet (fun x : Real => Real.log x)
        (compNicolasLandauPositiveMeasure X b))) a :=
    compInterior_integrableExpSet_log_nicolasLandau_of_below
      hX hPos hBelow
  have hAnalytic : forall sigma : Real, sigma < b ->
      AnalyticAt Real (compNicolasLandauPositiveMellinContinuationFilled X b)
        sigma := by
    intro sigma hSigma
    exact compNicolasLandauPositiveMellinContinuationFilled_analyticAt_lt
      hX hb hbHalf hPos hSigma
  have hEqNeg : forall a : Real, a < 0 ->
      mgf (fun x : Real => Real.log x)
          (compNicolasLandauPositiveMeasure X b) a =
        compNicolasLandauPositiveMellinContinuationFilled X b a := by
    intro a ha
    rw [compMgf_log_nicolasLandauPositiveMeasure_eq_mellin hX hPos]
    calc
      compNicolasLandauPositiveMellin X b a =
          compNicolasLandauPositiveMellinContinuation X b a :=
        compNicolasLandauPositiveMellin_eq_continuation_of_neg hX hb ha
      _ = compNicolasLandauPositiveMellinContinuationFilled X b a :=
        (compNicolasLandauPositiveMellinContinuationFilled_eq_raw_of_neg
          hX ha).symm
  exact Iio_subset_interior_integrableExpSet_of_analyticContinuation
    (compAe_log_nonneg_nicolasLandauPositiveMeasure hX) hNeg hAnalytic hEqNeg

theorem compNicolasLandauComplexMGF_analyticAt_of_positive [hBridge : Fact (∀ z : ℂ, z.re < 0 → Robin1984.nicolasJShiftedComplexContinuationFilled z = ∫ x in Ioi (3:ℝ), (x:ℂ)^(z-1) * (compensatedPsi x:ℂ))]
    {X b : Real} (hX : 3 <= X) (hb : 0 < b) (hbHalf : b <= 1 / 2)
    (hPos : forall x : Real, X < x ->
      0 <= compNicolasLandauPositiveTail b x)
    {z : Complex} (hz : z.re < b) :
    AnalyticAt Complex
      (complexMGF (fun x : Real => Real.log x)
        (compNicolasLandauPositiveMeasure X b)) z := by
  apply analyticAt_complexMGF
  exact compIio_subset_interior_integrableExpSet_nicolasLandau_of_positive
    hX hb hbHalf hPos hz

def compNicolasLandauPositiveComplexContinuationFilled
    (X b : Real) (z : Complex) : Complex :=
  nicolasJShiftedComplexContinuationFilled z -
    compNicolasJComplexMellinStartup X z +
      nicolasLandauRpowComplexContinuation X b z

def compNicolasLandauPositiveComplexMellin
    (X b : Real) (z : Complex) : Complex :=
  integral (volume.restrict (Ioi X)) (fun x : Real =>
    (x : Complex) ^ (z - 1) *
      (compNicolasLandauPositiveTail b x : Complex))

theorem compComplexMGF_log_nicolasLandauPositiveMeasure_eq_complexMellin
    {X b : Real} (hX : 3 <= X)
    (hPos : forall x : Real, X < x ->
      0 <= compNicolasLandauPositiveTail b x) {z : Complex} :
    complexMGF (fun x : Real => Real.log x)
        (compNicolasLandauPositiveMeasure X b) z =
      compNicolasLandauPositiveComplexMellin X b z := by
  have hDensity := compNicolasLandauPositiveDensity_aemeasurable
    (X := X) (b := b) hX
  let measurableDensity : Real -> ENNReal :=
    hDensity.mk (compNicolasLandauPositiveDensity b)
  have hDensityEq : Filter.Eventually
      (fun x : Real => compNicolasLandauPositiveDensity b x =
        measurableDensity x)
      (ae (volume.restrict (Ioi X))) := hDensity.ae_eq_mk
  have hDensityTop : Filter.Eventually
      (fun x : Real => measurableDensity x < Top.top)
      (ae (volume.restrict (Ioi X))) := by
    filter_upwards [hDensityEq] with x hx
    rw [<- hx]
    exact ENNReal.ofReal_lt_top
  have hMeasureEq :
      (volume.restrict (Ioi X)).withDensity
          (compNicolasLandauPositiveDensity b) =
        (volume.restrict (Ioi X)).withDensity measurableDensity :=
    withDensity_congr_ae hDensityEq
  unfold complexMGF compNicolasLandauPositiveMeasure
  rw [hMeasureEq, integral_withDensity_eq_integral_toReal_smul
    hDensity.measurable_mk hDensityTop]
  unfold compNicolasLandauPositiveComplexMellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hDensityEq] with x hx hdx
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) (hX.trans hx.le)
  have hxNe : Not ((x : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr hxPos.ne'
  have hTail : 0 <= compNicolasLandauPositiveTail b x := hPos x hx
  have hWeighted : 0 <= x ^ (-1 : Real) *
      compNicolasLandauPositiveTail b x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) hTail
  have hExp : Complex.exp (z * (Real.log x : Complex)) =
      (x : Complex) ^ z := by
    rw [Complex.cpow_def_of_ne_zero hxNe, <- Complex.ofReal_log hxPos.le]
    congr 1
    ring
  change SMul.smul (measurableDensity x).toReal
      (Complex.exp (z * (Real.log x : Complex))) =
    (x : Complex) ^ (z - 1) *
      (compNicolasLandauPositiveTail b x : Complex)
  rw [<- hdx]
  unfold compNicolasLandauPositiveDensity
  rw [ENNReal.toReal_ofReal hWeighted]
  change ((x ^ (-1 : Real) * compNicolasLandauPositiveTail b x : Real) : Complex) *
      Complex.exp (z * (Real.log x : Complex)) =
    (x : Complex) ^ (z - 1) *
      (compNicolasLandauPositiveTail b x : Complex)
  rw [hExp]
  push_cast
  calc
    ((x ^ (-1 : Real) : Real) : Complex) *
          (compNicolasLandauPositiveTail b x : Complex) * (x : Complex) ^ z =
        (((x ^ (-1 : Real) : Real) : Complex) * (x : Complex) ^ z) *
          (compNicolasLandauPositiveTail b x : Complex) := by ring
    _ = ((x : Complex) ^ ((-1 : Real) : Complex) *
          (x : Complex) ^ z) *
          (compNicolasLandauPositiveTail b x : Complex) := by
      rw [Complex.ofReal_cpow hxPos.le]
    _ = (x : Complex) ^ (((-1 : Real) : Complex) + z) *
          (compNicolasLandauPositiveTail b x : Complex) := by
      rw [Complex.cpow_add _ _ hxNe]
    _ = (x : Complex) ^ (z - 1) *
          (compNicolasLandauPositiveTail b x : Complex) := by
      congr 2
      norm_num [sub_eq_add_neg, add_comm]

theorem compNicolasJShiftedComplexContinuationFilled_eq_mellin_of_re_neg [hBridge : Fact (∀ z : ℂ, z.re < 0 → Robin1984.nicolasJShiftedComplexContinuationFilled z = ∫ x in Ioi (3:ℝ), (x:ℂ)^(z-1) * (compensatedPsi x:ℂ))]
    {z : Complex} (hz : z.re < 0) :
    nicolasJShiftedComplexContinuationFilled z = compNicolasJMellin z := hBridge.out z hz

theorem compNicolasJMellin_eq_startup_add_tail_of_re_neg
    {X : Real} (hX : 3 <= X) {z : Complex} (hz : z.re < 0) :
    compNicolasJMellin z = compNicolasJComplexMellinStartup X z +
      integral (volume.restrict (Ioi X)) (fun x : Real =>
        (x : Complex) ^ (z - 1) * (compensatedPsi x : Complex)) := by
  have hJThree := compMellin_integrable hz
  have hJX : IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) * (compensatedPsi x : Complex)) (Ioi X) :=
    hJThree.mono_set (Ioi_subset_Ioi hX)
  have hJStartup : IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) * (compensatedPsi x : Complex)) (Ioc 3 X) :=
    hJThree.mono_set Ioc_subset_Ioi_self
  unfold compNicolasJMellin compNicolasJComplexMellinStartup
  rw [<- Ioc_union_Ioi_eq_Ioi hX,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
  . exact hJStartup
  . exact hJX

theorem compNicolasLandauPositiveComplexMellin_eq_continuation_of_re_neg [hBridge : Fact (∀ z : ℂ, z.re < 0 → Robin1984.nicolasJShiftedComplexContinuationFilled z = ∫ x in Ioi (3:ℝ), (x:ℂ)^(z-1) * (compensatedPsi x:ℂ))]
    {X b : Real} (hX : 3 <= X) (hb : 0 < b)
    {z : Complex} (hz : z.re < 0) :
    compNicolasLandauPositiveComplexMellin X b z =
      compNicolasLandauPositiveComplexContinuationFilled X b z := by
  have hJThree := compMellin_integrable hz
  have hJX : IntegrableOn (fun x : Real =>
      (x : Complex) ^ (z - 1) * (compensatedPsi x : Complex)) (Ioi X) :=
    hJThree.mono_set (Ioi_subset_Ioi hX)
  have hXPos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hzB : z.re < b := lt_trans hz hb
  have hRpow := nicolasLandauRpowComplexTailMellin_integrableOn
    hXPos hzB
  have hDecomp : (fun x : Real =>
      (x : Complex) ^ (z - 1) *
        (compNicolasLandauPositiveTail b x : Complex)) =
      (fun x : Real =>
        (x : Complex) ^ (z - 1) * (compensatedPsi x : Complex)) +
      (fun x : Real =>
        (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex)) := by
    funext x
    unfold compNicolasLandauPositiveTail
    push_cast
    simp only [Pi.add_apply]
    ring
  unfold compNicolasLandauPositiveComplexMellin
    compNicolasLandauPositiveComplexContinuationFilled
  rw [hDecomp]
  change integral (volume.restrict (Ioi X)) (fun x : Real =>
      (x : Complex) ^ (z - 1) * (compensatedPsi x : Complex) +
        (x : Complex) ^ (z - 1) * ((x ^ (-b) : Real) : Complex)) = _
  rw [integral_add hJX hRpow]
  rw [nicolasLandauRpowComplexTailMellin_eq_continuation hXPos hzB]
  have hSplit := compNicolasJMellin_eq_startup_add_tail_of_re_neg hX hz
  rw [<- compNicolasJShiftedComplexContinuationFilled_eq_mellin_of_re_neg hz] at hSplit
  rw [hSplit]
  ring

theorem compNicolasLandauComplexMGF_eq_continuationFilled_of_re_neg [hBridge : Fact (∀ z : ℂ, z.re < 0 → Robin1984.nicolasJShiftedComplexContinuationFilled z = ∫ x in Ioi (3:ℝ), (x:ℂ)^(z-1) * (compensatedPsi x:ℂ))]
    {X b : Real} (hX : 3 <= X) (hb : 0 < b)
    (hPos : forall x : Real, X < x ->
      0 <= compNicolasLandauPositiveTail b x)
    {z : Complex} (hz : z.re < 0) :
    complexMGF (fun x : Real => Real.log x)
        (compNicolasLandauPositiveMeasure X b) z =
      compNicolasLandauPositiveComplexContinuationFilled X b z := by
  rw [compComplexMGF_log_nicolasLandauPositiveMeasure_eq_complexMellin hX hPos]
  exact compNicolasLandauPositiveComplexMellin_eq_continuation_of_re_neg
    hX hb hz

open Real in
theorem comp_positive_local_instance [hBridge : Fact (∀ z : ℂ, z.re < 0 → Robin1984.nicolasJShiftedComplexContinuationFilled z = ∫ x in Ioi (3:ℝ), (x:ℂ)^(z-1) * (compensatedPsi x:ℂ))] : let J : ℝ → ℝ := compensatedPsi
  let M : ℂ → ℂ := fun z : ℂ => ∫ x in Ioi (3 : ℝ), (x : ℂ) ^ (z - 1) * (J x : ℂ)
  ∀ b : ℝ, 0 < b → b < 1 / 2 → (∀ᶠ x : ℝ in atTop, 0 ≤ J x + x ^ (-b)) →
    ∃ F : ℂ → ℂ, (∀ z : ℂ, z.re < b → AnalyticAt ℂ F z) ∧
      (∀ z : ℂ, z.re < 0 → F z = M z) := by

  dsimp only
  intro b hb hbHalf hpos
  change ∀ᶠ x : ℝ in atTop, 0 ≤ compNicolasLandauPositiveTail b x at hpos
  obtain ⟨a, ha⟩ := eventually_atTop.1 hpos
  let X := max 3 a
  have hX : 3 ≤ X := le_max_left _ _
  have hp (x : ℝ) (hx : X < x) : 0 ≤ compNicolasLandauPositiveTail b x :=
    ha _ ((le_max_right _ _).trans hx.le)
  let L := complexMGF Real.log (compNicolasLandauPositiveMeasure X b)
  let F := fun z : ℂ =>
    L z + compNicolasJComplexMellinStartup X z - nicolasLandauRpowComplexContinuation X b z
  refine ⟨F, ?_, ?_⟩
  · intro z hz
    have hL : AnalyticAt ℂ L z :=
      compNicolasLandauComplexMGF_analyticAt_of_positive hX hb hbHalf.le hp hz
    have hne : z ≠ (b : ℂ) := by
      rintro rfl
      exact lt_irrefl _ hz
    exact (hL.add (compNicolasJComplexMellinStartup_analyticAt hX z)).sub
      (nicolasLandauRpowComplexContinuation_analyticAt (by linarith) hne)
  · intro z hz
    change L z + compNicolasJComplexMellinStartup X z -
      nicolasLandauRpowComplexContinuation X b z = compNicolasJMellin z
    have hL : L z = compNicolasLandauPositiveComplexContinuationFilled X b z :=
      compNicolasLandauComplexMGF_eq_continuationFilled_of_re_neg hX hb hp hz
    rw [hL, compNicolasLandauPositiveComplexContinuationFilled,
      compNicolasJShiftedComplexContinuationFilled_eq_mellin_of_re_neg hz]
    ring

end
end RobinConverse
end

section
/- The positive continuation argument for Robin's compensated primitive. -/
namespace RobinConverse
open Filter MeasureTheory Set
open scoped Topology

theorem compensated_positive :
    let M : ℂ → ℂ := fun z => ∫ x in Ioi (3:ℝ), (x:ℂ)^(z-1)*(compensatedPsi x:ℂ)
    ∀ b : ℝ, 0 < b → b < 1/2 → (∀ᶠ x : ℝ in atTop, 0 ≤ compensatedPsi x + x^(-b)) →
      ∃ F : ℂ → ℂ, (∀ z : ℂ, z.re < b → AnalyticAt ℂ F z) ∧
        ∀ z : ℂ, z.re < 0 → F z = M z := by
  have : Fact (∀ z : ℂ, z.re < 0 → Robin1984.nicolasJShiftedComplexContinuationFilled z =
      ∫ x in Ioi (3:ℝ), (x:ℂ)^(z-1)*(compensatedPsi x:ℂ)) :=
    ⟨fun _ hz => compensated_mellin_eq hz⟩
  exact comp_positive_local_instance

end RobinConverse
end

theorem OMA.solution : OMA.R_RiemannHypothesis_robin_criterion_R1.H2 :=
  RobinConverse.original_converse_of_landau RobinConverse.compensated_positive
