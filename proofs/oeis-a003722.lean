import OMAStatements.S_oeis_a003722

/-!
# The modified Bessel formula for the odd derivatives of sin(sinh x)

Velin Yanev proposed the identity in OEIS A003722. The registered Lean statement appeared
in commit f5418e2dae9e. We expand the two exponentials in the classical modified Bessel
generating function, bound each derivative series near zero by a product of two exponential
series, and combine opposite diagonals of the resulting sum.

https://oeis.org/A003722
https://dlmf.nist.gov/10.35.E1
-/

namespace BesselMoment
open Complex
abbrev Pair := ℕ × ℕ

noncomputable def signI (a b : ℕ) : ℂ := I ^ a * (-I) ^ b

noncomputable def coeff (p : Pair) : ℝ :=
  (signI p.1 p.2).im * ((1/2 : ℝ) ^ (p.1+p.2) / (p.1.factorial * p.2.factorial))

noncomputable def gap (p : Pair) : ℝ := (p.1:ℝ) - p.2

noncomputable def term (d : ℕ) (p : Pair) (x : ℝ) : ℝ :=
  coeff p * (gap p)^d * Real.exp ((gap p)*x)

noncomputable def maj (d : ℕ) (p : Pair) : ℝ :=
  d.factorial * ((Real.exp 2)^p.1 / p.1.factorial * ((Real.exp 2)^p.2 / p.2.factorial))

theorem summable_maj (d : ℕ) : Summable (maj d) := by
  have h := Real.summable_pow_div_factorial (Real.exp 2)
  exact (h.mul_of_nonneg h (fun _ => by positivity) (fun _ => by positivity)).mul_left _

theorem signI_bound (a b : ℕ) : |(signI a b).im| ≤ 1 := by
  simpa [signI] using Complex.abs_im_le_norm (I^a * (-I)^b)

theorem term_bound (d : ℕ) (p : Pair) {x : ℝ} (hx : x ∈ Set.Ioo (-1:ℝ) 1) :
    ‖term d p x‖ ≤ maj d p := by
  let u : ℝ := p.1
  let v : ℝ := p.2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hg : |gap p| ≤ u+v := abs_le.mpr ⟨by change -(u+v) ≤ u-v; linarith, by change u-v ≤ u+v; linarith⟩
  have hx' : |x| ≤ 1 := abs_le.mpr ⟨le_of_lt hx.1,le_of_lt hx.2⟩
  have hh : (gap p)*x ≤ u+v := calc
    (gap p)*x ≤ |(gap p)*x| := le_abs_self _
    _ = |gap p| * |x| := abs_mul _ _
    _ ≤ (u+v)*1 := mul_le_mul hg hx' (abs_nonneg _) (by positivity)
    _ = u+v := mul_one _
  have pd : |gap p|^d ≤ (d.factorial : ℝ) * Real.exp (u+v) := by
    refine (pow_le_pow_left₀ (abs_nonneg _) hg d).trans ?_
    have h := Real.pow_div_factorial_le_exp (u+v) (by positivity : 0 ≤ u+v) d
    simpa [mul_comm] using (div_le_iff₀ (by positivity : 0<(d.factorial:ℝ))).mp h
  let den : ℝ := p.1.factorial * p.2.factorial
  have den_pos : 0 < den := by dsimp [den]; positivity
  have cf : |coeff p| ≤ 1/den := by
    unfold coeff
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1/2)^ (p.1+p.2) / (p.1.factorial*p.2.factorial))]
    exact (mul_le_mul (signI_bound _ _) (div_le_div_of_nonneg_right (pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1)) den_pos.le)
      (by positivity) (by norm_num)).trans_eq (one_mul _)
  have expform : Real.exp (u+v) * Real.exp (u+v) = (Real.exp 2)^p.1 * (Real.exp 2)^p.2 := by
    rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    dsimp [u,v]; ring_nf
  unfold term
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (1/den * ((d.factorial:ℝ)*Real.exp (u+v))) * Real.exp (u+v) :=
      mul_le_mul (mul_le_mul cf pd (by positivity) (by positivity)) (Real.exp_le_exp.mpr hh)
        (Real.exp_pos _).le (by positivity)
    _ = maj d p := by
      unfold maj
      calc
        _ = (d.factorial:ℝ) * (Real.exp (u+v)*Real.exp (u+v)) / den := by ring
        _ = _ := by rw [expform]; dsimp [den]; ring

theorem summable_term (d : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1:ℝ) 1) :
    Summable (fun p => term d p x) := (summable_maj d).of_norm_bounded (fun p => term_bound d p hx)

end BesselMoment

namespace BesselMoment

theorem term_deriv (d : ℕ) (p : Pair) (y : ℝ) :
    HasDerivAt (term d p) (term (d+1) p y) y := by
  have h := ((Real.hasDerivAt_exp _).comp y ((hasDerivAt_id y).const_mul (gap p))).const_mul (coeff p * gap p ^ d)
  apply h.congr_deriv
  simp only [term, pow_succ, id_eq, mul_one]
  ring

theorem series_deriv (d : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1:ℝ) 1) :
    HasDerivAt (fun y => ∑' p, term d p y) (∑' p, term (d+1) p x) x := by
  have hz : (0:ℝ) ∈ Set.Ioo (-1:ℝ) 1 := ⟨by norm_num, by norm_num⟩
  exact hasDerivAt_tsum_of_isPreconnected (summable_maj (d+1)) isOpen_Ioo
    (convex_Ioo _ _).isPreconnected (fun p y _ => term_deriv d p y)
    (fun p _ hy => term_bound (d+1) p hy) hz (summable_term d hz) hx

theorem iterated_series (d : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1:ℝ) 1) :
    iteratedDeriv d (fun y => ∑' p, term 0 p y) x = ∑' p, term d p x := by
  induction d generalizing x with
  | zero => simp
  | succ d ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv d (fun y => ∑' p, term 0 p y) =ᶠ[nhds x]
        (fun y => ∑' p, term d p y) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx) (fun _ hy => ih hy)
    exact he.deriv_eq.trans (series_deriv d hx).deriv

end BesselMoment

namespace BesselMoment
open Complex

private theorem norm_summable (z : ℂ) :
    Summable (fun m : ℕ => ‖z^m / (m.factorial:ℂ)‖) := by
  simpa [norm_div, norm_pow] using Real.summable_pow_div_factorial ‖z‖

private theorem phase_weight (a b : ℕ) (x : ℝ) :
    ((I * ((Real.exp x/2:ℝ):ℂ))^a / (a.factorial:ℂ) *
      (((-I) * ((Real.exp (-x)/2:ℝ):ℂ))^b / (b.factorial:ℂ))).im =
      term 0 (a,b) x := by
  have ex : (Real.exp x)^a * (Real.exp (-x))^b = Real.exp (((a:ℝ)-b)*x) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have he : (I * ((Real.exp x/2:ℝ):ℂ))^a / (a.factorial:ℂ) *
        (((-I) * ((Real.exp (-x)/2:ℝ):ℂ))^b / (b.factorial:ℂ)) =
      signI a b * (((Real.exp x/2)^a / a.factorial * ((Real.exp (-x)/2)^b / b.factorial):ℝ):ℂ) := by
    simp only [mul_pow, signI, ofReal_mul, ofReal_div, ofReal_pow, ofReal_natCast, ofReal_ofNat]
    ring
  rw [he, Complex.mul_im]
  simp only [Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add, term, coeff, gap,
    pow_zero, mul_one]
  simp only [div_pow, pow_add]
  rw [← ex]
  ring

private theorem exp_hasSum (z : ℂ) :
    HasSum (fun n : ℕ => z^n / (n.factorial:ℂ)) (Complex.exp z) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

private theorem product_hasSum (A B : ℂ) :
    HasSum (fun p : Pair => (A^p.1 / (p.1.factorial:ℂ)) * (B^p.2 / (p.2.factorial:ℂ)))
      (Complex.exp A * Complex.exp B) := by
  apply (exp_hasSum A).mul (exp_hasSum B)
  exact summable_mul_of_summable_norm (f := fun n : ℕ => A^n / (n.factorial:ℂ))
    (g := fun n : ℕ => B^n / (n.factorial:ℂ)) (norm_summable A) (norm_summable B)

private theorem product_im (A B : ℂ) :
    (Complex.exp A * Complex.exp B).im =
      ∑' p : Pair, (A^p.1 / (p.1.factorial:ℂ) * (B^p.2 / (p.2.factorial:ℂ))).im := by
  exact (Complex.imCLM.hasSum (f := fun p : Pair => A^p.1 / (p.1.factorial:ℂ) *
    (B^p.2 / (p.2.factorial:ℂ))) (product_hasSum A B)).tsum_eq.symm

theorem expansion (x : ℝ) : Real.sin (Real.sinh x) = ∑' p, term 0 p x := by
  let A : ℂ := I * ((Real.exp x / 2 : ℝ) : ℂ)
  let B : ℂ := (-I) * ((Real.exp (-x) / 2 : ℝ) : ℂ)
  have hs : A + B = (Real.sinh x : ℂ) * I := by
    simp only [A, B, Real.sinh_eq, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_ofNat]
    ring
  have hi : (Complex.exp A * Complex.exp B).im = Real.sin (Real.sinh x) := by
    rw [← Complex.exp_add, hs, Complex.exp_im]
    simp only [Complex.mul_I_re, Complex.ofReal_im, neg_zero, Real.exp_zero, Complex.mul_I_im, Complex.ofReal_re, one_mul]
  calc
    Real.sin (Real.sinh x) = (Complex.exp A * Complex.exp B).im := hi.symm
    _ = ∑' p : Pair, (A^p.1 / (p.1.factorial:ℂ) * (B^p.2 / (p.2.factorial:ℂ))).im :=
      product_im A B
    _ = _ := tsum_congr fun p => phase_weight p.1 p.2 x

end BesselMoment

namespace BesselMoment

/-- Opposite orientations of every odd diagonal of the table of pairs. -/
private def oddPair : Bool × Pair → Pair
  | (false,k,m) => (m+2*k+1,m)
  | (true,k,m) => (m,m+2*k+1)

private theorem oddPair_inj : Function.Injective oddPair := by
  rintro ⟨s,k,m⟩ ⟨z,l,h⟩ eq
  cases s <;> cases z <;> simp [oddPair] at eq ⊢ <;> omega

private theorem sign_high (m d : ℕ) : signI (m+d) m = Complex.I^d := by
  have h : Complex.I^m * (-Complex.I)^m = 1 := by rw [←mul_pow]; simp
  unfold signI
  rw [pow_add,mul_right_comm, h,one_mul]

private theorem sign_low (m d : ℕ) : signI m (m+d) = (-Complex.I)^d := by
  have h : Complex.I^m * (-Complex.I)^m = 1 := by rw [←mul_pow]; simp
  unfold signI
  rw [pow_add,←mul_assoc,h,one_mul]

private theorem vanish_high (n m k : ℕ) : term n (m+2*k,m) 0 = 0 := by
  simp only [term, coeff, sign_high, pow_mul, Complex.I_sq]
  have h : (((-1:ℝ)^k : ℝ) : ℂ) = (-1:ℂ)^k := by push_cast; rfl
  rw [←h]
  simp only [Complex.ofReal_im,zero_mul]

private theorem vanish_low (n m k : ℕ) : term n (m,m+2*k) 0 = 0 := by
  simp only [term, coeff, sign_low, pow_mul, neg_sq, Complex.I_sq]
  have h : (((-1:ℝ)^k : ℝ) : ℂ) = (-1:ℂ)^k := by push_cast; rfl
  rw [←h]
  simp only [Complex.ofReal_im,zero_mul]

private theorem supported_diagonal (n : ℕ) :
    Function.support (fun p => term n p 0) ⊆ Set.range oddPair := by
  rintro ⟨a,b⟩ hn
  change term n (a,b) 0 ≠ 0 at hn
  by_cases ord : b≤a
  · by_cases even : (a-b)%2=0
    · obtain ⟨k,hk⟩ : ∃ k, a=b+2*k := ⟨(a-b)/2,by omega⟩
      exact False.elim (hn (hk ▸ vanish_high n b k))
    · exact ⟨(false,(a-b)/2,b),by simp [oddPair]; omega⟩
  · by_cases even : (b-a)%2=0
    · obtain ⟨k,hk⟩ : ∃ k, b=a+2*k := ⟨(b-a)/2,by omega⟩
      exact False.elim (hn (hk ▸ vanish_low n a k))
    · exact ⟨(true,(b-a)/2,a),by simp [oddPair]; omega⟩

private noncomputable def diagonalWeight (n k m : ℕ) : ℝ :=
  (-1:ℝ)^k * (2*(k:ℝ)+1)^(2*n+1) *
    ((1/2:ℝ)^(2*m+(2*k+1))/((m.factorial:ℝ)*((m+(2*k+1)).factorial:ℝ)))

private theorem oddPair_value (n : ℕ) (s : Bool) (k m : ℕ) :
    term (2*n+1) (oddPair (s,k,m)) 0 = diagonalWeight n k m := by
  have castSign : (-1:ℂ)^k = (((-1:ℝ)^k:ℝ):ℂ) := by push_cast; rfl
  have sq : (-Complex.I)^2 = -1 := by rw [neg_sq,Complex.I_sq]
  have high : (signI (m+(2*k+1)) m).im = (-1:ℝ)^k := by
    rw [sign_high,pow_succ,pow_mul,Complex.I_sq,castSign]
    simp only [Complex.mul_I_im,Complex.ofReal_re]
  have low : (signI m (m+(2*k+1))).im = -((-1:ℝ)^k) := by
    rw [sign_low,pow_succ,pow_mul,sq,castSign]
    simp only [mul_neg,Complex.neg_im,Complex.mul_I_im,Complex.ofReal_re]
  cases s
  · simp only [oddPair,term,coeff,gap,diagonalWeight,mul_zero,Real.exp_zero,mul_one]
    rw [Nat.add_assoc m (2*k) 1, high,show m+(2*k+1)+m=2*m+(2*k+1) by omega]
    push_cast
    ring
  · simp only [oddPair,term,coeff,gap,diagonalWeight,mul_zero,Real.exp_zero,mul_one]
    rw [Nat.add_assoc m (2*k) 1, low,show m+(m+(2*k+1))=2*m+(2*k+1) by omega]
    have gapEq : (m:ℝ)-(m+(2*k+1):ℕ) = -(2*(k:ℝ)+1) := by push_cast; ring
    rw [gapEq, (show Odd (2*n+1) from ⟨n,rfl⟩).neg_pow]
    ring

/-- Sum the two orientations and remove the identically zero even diagonals. -/
theorem diagonal_moment_rows (n : ℕ) :
    (∑' p : Pair, term (2*n+1) p 0) = 2 * ∑' k : ℕ, ∑' m : ℕ,
      (-1:ℝ)^k * (2*(k:ℝ)+1)^(2*n+1) *
       ((1/2:ℝ)^(2*m+(2*k+1))/((m.factorial:ℝ)*((m+(2*k+1)).factorial:ℝ))) := by
  have whole := summable_term (2*n+1) (x:=0) (by constructor <;> norm_num)
  have rows : Summable (fun c => term (2*n+1) (oddPair c) 0) := whole.comp_injective oddPair_inj
  rw [← oddPair_inj.tsum_eq (supported_diagonal (2*n+1))]
  rw [rows.tsum_prod]
  have inner (s : Bool) : (∑' p : Pair, term (2*n+1) (oddPair (s,p)) 0) =
      ∑' k, ∑' m, diagonalWeight n k m := by
    have sub := rows.prod_factor s
    rw [sub.tsum_prod]
    exact tsum_congr fun k => tsum_congr fun m => oddPair_value n s k m
  change (∑' s : Bool, ∑' p : Pair, term (2*n+1) (oddPair (s,p)) 0) =
    2 * (∑' k, ∑' m, diagonalWeight n k m)
  simp only [inner,tsum_fintype, Fintype.sum_bool]
  ring

end BesselMoment

namespace BesselMoment

theorem diagonal_moment (n : ℕ) :
    (∑' p : Pair, term (2*n+1) p 0) = -2 * ∑' k : ℕ,
      (-1:ℝ)^(k+1) * ((2*k+1:ℝ)^(2*n+1)) * OMA.S_oeis_a003722.besselI (2*k+1) 1 := by
  rw [diagonal_moment_rows]
  have inner (k : ℕ) : (∑' m : ℕ, (-1:ℝ)^k * (2*(k:ℝ)+1)^(2*n+1) *
      ((1/2:ℝ)^(2*m+(2*k+1))/((m.factorial:ℝ)*((m+(2*k+1)).factorial:ℝ)))) =
      -((-1:ℝ)^(k+1) * (2*(k:ℝ)+1)^(2*n+1) * OMA.S_oeis_a003722.besselI (2*k+1) 1) := by
    rw [tsum_mul_left]
    unfold OMA.S_oeis_a003722.besselI
    rw [pow_succ]
    ring
  simp only [inner,tsum_neg]
  ring

end BesselMoment

theorem OMA.solution : type_of% @OMA.S_oeis_a003722.main := by
  intro n
  rw [show (fun x : ℝ => Real.sin (Real.sinh x)) = (fun x => ∑' p, BesselMoment.term 0 p x)
    from funext BesselMoment.expansion]
  exact (BesselMoment.iterated_series (2*n+1)
    (x := 0) ⟨by norm_num, by norm_num⟩).trans (BesselMoment.diagonal_moment n)
