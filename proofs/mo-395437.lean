import OMAStatements.S_mo_395437
import Mathlib

/-! # An explicit drop in the Robin score for colossally abundant numbers

MathOverflow 395437, posed by ntessore. The two reciprocal parameters 1/125 and 1/134
select 2021649740510400 and three times that number. Their divisor-sum ratios gain a
factor of 121/120, insufficient to compensate for the double logarithm in the
normalization. The Grönwall limsup implication in the edit is proved separately.
-/

/- The marginal gain in abundancy from increasing a prime exponent
decreases as either the prime or the new exponent increases. -/
namespace RobinRecord
open Finset

theorem ratio_as_reciprocal_sum {x : ℝ} (hx : 1 < x) {j : ℕ} (hj : 0 < j) :
    (1 - x⁻¹ ^ (j + 1)) / (1 - x⁻¹ ^ j) =
      1 + 1 / (x * ∑ i ∈ range j, x ^ i) := by
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x ≠ 1 := ne_of_gt hx
  have hp : 1 < x ^ j := one_lt_pow₀ hx (Nat.ne_of_gt hj)
  have hd : x ^ j - 1 ≠ 0 := by linarith
  rw [geom_sum_eq hx1 j, inv_pow, inv_pow, pow_succ]
  field_simp [hx0, hx1, hd]
  ring

theorem gain_mono {p q : ℝ} (hp : 1 < p) (hpq : p ≤ q)
    {j k : ℕ} (hj : 0 < j) (hjk : j ≤ k) :
    (1 - q⁻¹ ^ (k + 1)) / (1 - q⁻¹ ^ k) ≤
      (1 - p⁻¹ ^ (j + 1)) / (1 - p⁻¹ ^ j) := by
  rw [ratio_as_reciprocal_sum (hp.trans_le hpq) (hj.trans_le hjk),
    ratio_as_reciprocal_sum hp hj]
  apply add_le_add_right
  have hpos : 0 < ∑ i ∈ range j, p ^ i := by
    apply sum_pos
    · intro i hi
      positivity
    · exact ⟨0, mem_range.mpr hj⟩
  apply one_div_le_one_div_of_le (mul_pos (by linarith : 0 < p) hpos)
  apply mul_le_mul hpq _ hpos.le (by linarith)
  calc
    (∑ i ∈ range j, p ^ i) ≤ ∑ i ∈ range j, q ^ i := by
      apply sum_le_sum
      intro i hi
      exact pow_le_pow_left₀ (by linarith) hpq i
    _ ≤ ∑ i ∈ range k, q ^ i := by
      apply sum_le_sum_of_subset_of_nonneg (range_mono hjk)
      intro i hi h
      exact pow_nonneg (by linarith : 0 ≤ q) i

end RobinRecord

/- The following identity is the prime-layer calculation of Robin1984, CAProfile,
written directly for Mathlib's divisor sum (kimihiro64, Apache-2.0). -/
namespace RobinProfile
open Finset
open ArithmeticFunction (sigma)
theorem prime_gain {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    (sigma 1 (n*p) : ℝ) / (p * (sigma 1 n : ℝ)) =
      (1 - (p:ℝ)⁻¹ ^ (n.factorization p + 2)) / (1 - (p:ℝ)⁻¹ ^ (n.factorization p + 1)) := by
  let a := n.factorization p
  let d := n / p^a
  have hdpos : 0 < d := Nat.ordCompl_pos p hn
  have hc : Nat.Coprime p d := Nat.coprime_ordCompl hp hn
  have heq : p^a * d = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have heq' : p^(a+1)*d=n*p := by rw [pow_succ, ← heq]; ring
  have sd : sigma 1 n = sigma 1 (p^a) * sigma 1 d := by
    conv_lhs => rw [← heq]
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hc.pow_left _)
  have sp : sigma 1 (n*p) = sigma 1 (p^(a+1)) * sigma 1 d := by
    rw [← heq']
    exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hc.pow_left _)
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have ds : (sigma 1 d:ℝ) ≠ 0 := by exact_mod_cast (ArithmeticFunction.sigma_pos 1 d hdpos.ne').ne'
  have closed (e : ℕ) : (sigma 1 (p^e):ℝ) = ((p:ℝ)^(e+1)-1)/(p-1) := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
    push_cast
    exact geom_sum_eq hp1.ne' _
  have ht : (p:ℝ)^(a+1)-1 ≠ 0 := ne_of_gt (sub_pos.mpr (one_lt_pow₀ hp1 (by omega)))
  change _ = (1-(p:ℝ)⁻¹^(a+2))/(1-(p:ℝ)⁻¹^(a+1))
  rw [sp,sd,Nat.cast_mul,Nat.cast_mul,closed,closed,inv_pow,inv_pow]
  have hp_sub : (p:ℝ)-1 ≠ 0 := by linarith
  field_simp [hp0.ne',hp_sub,ds,ht]
  ring
end RobinProfile

/- Prime-exponent tests for global maximizers of weighted abundancy. -/
namespace CA395437
open Finset Real
open ArithmeticFunction (sigma)

def denom (p j : ℕ) : ℕ := p * ∑ i ∈ range j, p ^ i
noncomputable def gain (p j : ℕ) : ℝ := 1 + 1 / (denom p j : ℝ)

theorem gain_eq {p j : ℕ} (hp : 1 < p) (hj : 0 < j) :
    gain p j = (1 - (p : ℝ)⁻¹ ^ (j + 1)) / (1 - (p : ℝ)⁻¹ ^ j) := by
  rw [RobinRecord.ratio_as_reciprocal_sum (by exact_mod_cast hp : (1 : ℝ) < p) hj]
  simp [gain, denom]

theorem gain_antitone {p q j k : ℕ} (hp : 1 < p) (hpq : p ≤ q)
    (hj : 0 < j) (hjk : j ≤ k) : gain q k ≤ gain p j := by
  rw [gain_eq (hp.trans_le hpq) (hj.trans_le hjk), gain_eq hp hj]
  exact RobinRecord.gain_mono (by exact_mod_cast hp) (by exact_mod_cast hpq) hj hjk

noncomputable def abundance (n : ℕ) : ℝ := (sigma 1 n : ℝ) / n
noncomputable def objective (e : ℝ) (n : ℕ) : ℝ := abundance n / (n : ℝ)^e

theorem objective_pos (e : ℝ) {n : ℕ} (hn : 0 < n) : 0 < objective e n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  exact div_pos (div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 n hn.ne') hnR)
    (rpow_pos_of_pos hnR e)

theorem prime_step (e : ℝ) {n p : ℕ} (hn : 0 < n) (hp : p.Prime) :
    objective e (n*p) = objective e n * gain p (n.factorization p + 1) / (p : ℝ)^e := by
  have nR : (0:ℝ) < n := by exact_mod_cast hn
  have pR : (0:ℝ) < p := by exact_mod_cast hp.pos
  have dR : (0:ℝ) < sigma 1 n := by exact_mod_cast ArithmeticFunction.sigma_pos 1 n hn.ne'
  have ratio := RobinProfile.prime_gain hp hn.ne'
  rw [← gain_eq hp.one_lt (Nat.zero_lt_succ (n.factorization p))] at ratio
  have step := (div_eq_iff (mul_pos pR dR).ne').mp ratio
  simp only [objective, abundance, Nat.cast_mul, mul_rpow nR.le pR.le, step]
  field_simp

theorem bounds_at_max {e : ℝ} {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (h : ∀ m : ℕ, 0 < m → objective e m ≤ objective e n) :
    gain p (n.factorization p + 1) ≤ (p : ℝ)^e ∧
      (0 < n.factorization p → (p : ℝ)^e ≤ gain p (n.factorization p)) := by
  have pR : 0 < (p : ℝ)^e := rpow_pos_of_pos (by exact_mod_cast hp.pos) _
  constructor
  · have nxt := h (n*p) (Nat.mul_pos hn hp.pos)
    rw [prime_step e hn hp] at nxt
    exact (mul_le_mul_iff_right₀ (objective_pos e hn)).mp ((div_le_iff₀ pR).mp nxt)
  · intro hpos
    obtain ⟨v,hv⟩ := Nat.dvd_of_factorization_pos hpos.ne'
    have nv : n = v*p := by simpa [mul_comm] using hv
    have vp : 0 < v := Nat.pos_of_mul_pos_right (nv ▸ hn)
    have fac : n.factorization p = v.factorization p + 1 := by
      rw [nv, Nat.factorization_mul vp.ne' hp.ne_zero, Finsupp.add_apply, hp.factorization_self]
    have last := h v vp
    rw [nv, prime_step e vp hp] at last
    rw [fac]
    exact (mul_le_mul_iff_right₀ (objective_pos e vp)).mp ((le_div_iff₀ pR).mp last)

theorem determine_exponent {e : ℝ} {n p a : ℕ} (hn : 0 < n) (hp : p.Prime)
    (h : ∀ m : ℕ, 0 < m → objective e m ≤ objective e n)
    (upper : gain p (a+1) < (p : ℝ)^e) (lower : 0 < a → (p : ℝ)^e < gain p a) :
    n.factorization p = a := by
  obtain ⟨nxt,last⟩ := bounds_at_max hn hp h
  by_contra ne
  rcases lt_or_gt_of_ne ne with lt | gt
  · have cmp := gain_antitone hp.one_lt (le_rfl (a:=p))
      (Nat.zero_lt_succ (n.factorization p)) (show n.factorization p+1 ≤ a by omega)
    exact ((lower (by omega)).not_ge (cmp.trans nxt))
  · have cmp := gain_antitone hp.one_lt (le_rfl (a:=p))
      (Nat.zero_lt_succ a) (show a+1 ≤ n.factorization p by omega)
    exact (upper.not_ge ((last (by omega)).trans cmp))

end CA395437

/- Exact integer tests for the prime-power layers at rational reciprocal parameters. -/
namespace CA395437
open Real Finset

theorem denom_pos {p j : ℕ} (hp : 0 < p) (hj : 0 < j) : 0 < denom p j := by
  apply Nat.mul_pos hp
  exact sum_pos (fun i _ => Nat.pow_pos hp) ⟨0,mem_range.mpr hj⟩

theorem compare_gain {p j d : ℕ} (hp : 0 < p) (hj : 0 < j) (hd : d ≠ 0) :
    (gain p j < (p : ℝ) ^ (1 / (d : ℝ)) ↔
      (denom p j + 1)^d < p * (denom p j)^d) ∧
    ((p : ℝ) ^ (1 / (d : ℝ)) < gain p j ↔
      p * (denom p j)^d < (denom p j + 1)^d) := by
  have dn : (0:ℝ) < denom p j := by exact_mod_cast denom_pos hp hj
  have gd : gain p j = ((denom p j + 1 : ℕ) : ℝ) / (denom p j : ℝ) := by
    simp only [gain, Nat.cast_add, Nat.cast_one]
    field_simp
  have hg : 0 ≤ gain p j := by unfold gain; positivity
  have hr : 0 ≤ (p : ℝ) ^ (1 / (d : ℝ)) := by positivity
  have power : ((p : ℝ) ^ (1 / (d : ℝ))) ^ d = p := by
    rw [one_div, Real.rpow_inv_natCast_pow (Nat.cast_nonneg p) hd]
  constructor
  · rw [← pow_lt_pow_iff_left₀ hg hr hd, gd, div_pow, power, div_lt_iff₀ (pow_pos dn d)]
    norm_cast
  · rw [← pow_lt_pow_iff_left₀ hr hg hd, gd, div_pow, power, lt_div_iff₀ (pow_pos dn d)]
    norm_cast

def localTest (d M p : ℕ) : Prop :=
  let a := M.factorization p
  (denom p (a+1) + 1)^d < p * (denom p (a+1))^d ∧
  (0 < a → p * (denom p a)^d < (denom p a + 1)^d)

instance (d M p : ℕ) : Decidable (localTest d M p) := by unfold localTest; infer_instance

/-- The table covers primes up through 31. Beyond that, monotonicity of the first layer
and the comparison for 37 rule out every prime. -/
theorem identify_max {n M d : ℕ} (hn : 0 < n) (hM : 0 < M) (hd : 0 < d)
    (h : ∀ m : ℕ, 0 < m → objective (1/(d:ℝ)) m ≤ objective (1/(d:ℝ)) n)
    (table : ∀ p : Fin 37, p.val.Prime → localTest d M p.val)
    (cut : (denom 37 1 + 1)^d < 37*(denom 37 1)^d)
    (support : ∀ p ∈ M.primeFactors, p < 37) : n = M := by
  apply Nat.eq_of_factorization_eq hn.ne' hM.ne'
  intro p
  by_cases hp : p.Prime
  · by_cases lt : p < 37
    · obtain ⟨high,low⟩ := table ⟨p,lt⟩ hp
      apply determine_exponent hn hp h
      · exact (compare_gain hp.pos (Nat.zero_lt_succ _) hd.ne').1.mpr high
      · intro pos
        exact (compare_gain hp.pos pos hd.ne').2.mpr (low pos)
    · have zero : M.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd
        (fun dvd => lt (support p (Nat.mem_primeFactors.mpr ⟨hp,dvd,hM.ne'⟩)))
      rw [zero]
      apply determine_exponent hn hp h
      · have cmp := gain_antitone (p:=37) (q:=p) (j:=1) (k:=1) (by decide) (by omega) (by decide) le_rfl
        have bridge := (compare_gain (p:=37) (j:=1) (by decide) (by decide) hd.ne').1.mpr cut
        have big : (37:ℝ) ≤ p := by exact_mod_cast (by omega : 37 ≤ p)
        exact (cmp.trans_lt bridge).trans_le (Real.rpow_le_rpow (by norm_num) big (by positivity))
      · omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem lower_index {n : ℕ} (hn : 0 < n)
    (h : ∀ m : ℕ, 0 < m → objective (1/125) m ≤ objective (1/125) n) :
    n = 2021649740510400 := by
  apply identify_max (d:=125) hn (by decide) (by decide) h <;> decide +kernel

theorem upper_index {n : ℕ} (hn : 0 < n)
    (h : ∀ m : ℕ, 0 < m → objective (1/134) m ≤ objective (1/134) n) :
    n = 6064949221531200 := by
  apply identify_max (d:=134) hn (by decide) (by decide) h <;> decide +kernel
end CA395437

/- A power-weighted abundancy ratio attains its maximum on every positive
tail. The harmonic comparison is adapted from Open Math Agents PR 12089.
Related global-maximizer and logarithmic estimates appear in Jonas Whidden's
Robin1984, ColossallyAbundant/CAProfile.lean, Apache-2.0. -/
namespace RobinRecord
open Finset Real Filter Topology
open ArithmeticFunction (sigma)

theorem sigma_harmonic_bound (n : ℕ) (hn : 0 < n) :
    (sigma 1 n : ℝ) ≤ n * (1 + log n) := by
  have subset : n.divisors ⊆ Icc 1 n := fun d hd =>
    mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)⟩
  calc
    (ArithmeticFunction.sigma 1 n : ℝ) = ∑ d ∈ n.divisors, ((n / d : ℕ) : ℝ) := by
      rw [Nat.sum_div_divisors n (fun d => (d : ℝ)), ArithmeticFunction.sigma_one_apply, Nat.cast_sum]
    _ = n * ∑ d ∈ n.divisors, (d : ℝ)⁻¹ := by
      rw [mul_sum]
      refine sum_congr rfl fun d hd => ?_
      rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) (by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'),
        div_eq_mul_inv]
    _ ≤ n * ∑ d ∈ Icc 1 n, (d : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg subset (by intros; positivity)) (Nat.cast_nonneg n)
    _ ≤ n * (1 + Real.log n) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using harmonic_le_one_add_log n

theorem tail_max {s : ℕ} (hs : 0 < s) {e : ℝ} (he : 0 < e) :
    ∃ r : ℕ, s ≤ r ∧ ∀ m : ℕ, s ≤ m →
      (sigma 1 m : ℝ) / m / (m : ℝ)^e ≤ (sigma 1 r : ℝ) / r / (r : ℝ)^e := by
  classical
  let f (n : ℕ) := (sigma 1 n : ℝ) / n / (n : ℝ)^e
  have fs : 0 < f s :=
    div_pos (div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 s hs.ne')
      (by exact_mod_cast hs)) (rpow_pos_of_pos (by exact_mod_cast hs) e)
  have hone : Tendsto (fun x : ℝ => 1 / x^e) atTop (𝓝 0) := by
    refine (tendsto_rpow_neg_atTop he).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [rpow_neg hx, one_div]
  have hlog := (isLittleO_log_rpow_atTop he).tendsto_div_nhds_zero
  have hsum : Tendsto (fun n : ℕ => (1 + log n) / (n : ℝ)^e) atTop (𝓝 0) := by
    simpa [Function.comp_def, add_div] using (hone.add hlog).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hn⟩ := eventually_atTop.mp (hsum.eventually_lt_const fs)
  let A := Icc s (max s N)
  have member : s ∈ A := mem_Icc.mpr ⟨le_rfl,le_max_left _ _⟩
  obtain ⟨r,hr,peak⟩ := exists_max_image A f ⟨s,member⟩
  refine ⟨r,(mem_Icc.mp hr).1,?_⟩
  intro m hm
  by_cases h : m ≤ max s N
  · exact peak m (mem_Icc.mpr ⟨hm,h⟩)
  · have mp : 0 < m := hs.trans_le hm
    have mR : (0 : ℝ) < m := by exact_mod_cast mp
    apply le_trans _ (peak s member)
    calc
      f m ≤ (1 + log m) / (m : ℝ)^e := by
        apply div_le_div_of_nonneg_right _ (rpow_pos_of_pos mR e).le
        exact (div_le_iff₀ mR).mpr (by simpa only [mul_comm] using sigma_harmonic_bound m mp)
      _ ≤ f s := (hn m (by omega)).le
end RobinRecord

namespace CA395437
open Filter Real Topology OMA.S_mo_395437
open ArithmeticFunction (sigma)

/-- The tie-breaking supremum defining the candidate is itself a positive maximizer. -/
theorem candidate_is_max {e : ℝ} (he : 0 < e) :
    0 < candidate e ∧ ∀ m : ℕ, 0 < m →
      abundancy m / (m : ℝ)^e ≤ abundancy (candidate e) / (candidate e : ℝ)^e := by
  let S : Set ℕ := {n | 0 < n ∧ ∀ m : ℕ, 0 < m →
    abundancy m / (m : ℝ)^e ≤ abundancy n / (n : ℝ)^e}
  obtain ⟨r, hr, hmax⟩ := RobinRecord.tail_max (s := 1) (by decide) he
  have nonempty : S.Nonempty := ⟨r, hr, hmax⟩
  have hone : Tendsto (fun x : ℝ => 1/x^e) atTop (𝓝 0) := by
    refine (tendsto_rpow_neg_atTop he).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [rpow_neg hx, one_div]
  have hsum : Tendsto (fun n : ℕ => (1 + log n)/(n : ℝ)^e) atTop (𝓝 0) := by
    have hlog := (isLittleO_log_rpow_atTop he).tendsto_div_nhds_zero
    simpa [Function.comp_def, add_div] using (hone.add hlog).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, cutoff⟩ := eventually_atTop.mp (hsum.eventually_lt_const (show (0:ℝ)<1 by norm_num))
  have bound : BddAbove S := by
    refine ⟨N, fun n hn => ?_⟩
    by_contra! hN
    have hp : (0:ℝ)<n := Nat.cast_pos.mpr hn.1
    have top := hn.2 1 (by decide)
    have base : abundancy 1 / (1 : ℕ)^e = 1 := by simp [abundancy]
    rw [base] at top
    have upper : abundancy n ≤ 1+log n :=
      (div_le_iff₀ hp).2 (by simpa [mul_comm] using RobinRecord.sigma_harmonic_bound n hn.1)
    have := (div_le_div_of_nonneg_right upper (rpow_pos_of_pos hp e).le).trans_lt (cutoff n hN.le)
    exact (not_lt_of_ge top) this
  exact Nat.sSup_mem nonempty bound

end CA395437

/- The logarithmic tangent that turns any violation of Robin's inequality
into one at a maximum of a power-weighted abundancy ratio. -/

namespace RobinRecord
open Real

theorem log_tangent {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    log a - log b ≤ (a - b) / b := by
  have h := log_le_sub_one_of_pos (div_pos ha hb)
  rw [log_div ha.ne' hb.ne'] at h
  calc
    log a - log b ≤ a / b - 1 := h
    _ = (a - b) / b := by field_simp

theorem double_log_tangent {m n : ℝ} (hm : 1 < log m) (hn : 1 < log n)
    (mp : 0 < m) (np : 0 < n) :
    log (log m) / log (log n) ≤ (m / n) ^ (1 / (log n * log (log n))) := by
  have ml : 0 < log m := zero_lt_one.trans hm
  have nl : 0 < log n := zero_lt_one.trans hn
  have mm := log_pos hm
  have nn := log_pos hn
  rw [rpow_def_of_pos (div_pos mp np), log_div mp.ne' np.ne']
  apply (log_le_iff_le_exp (div_pos mm nn)).mp
  rw [log_div mm.ne' nn.ne']
  calc
    log (log (log m)) - log (log (log n)) ≤
        (log (log m) - log (log n)) / log (log n) := log_tangent mm nn
    _ ≤ ((log m - log n) / log n) / log (log n) :=
      div_le_div_of_nonneg_right (log_tangent ml nl) nn.le
    _ = (log m - log n) * (1 / (log n * log (log n))) := by ring

end RobinRecord

/- An unbounded positive sequence forces every family of its power-weighted
global maximizers to leave every finite initial segment as the exponent tends
to zero from above. -/
namespace GronwallCA
open Filter Real Finset Topology

theorem maximizers_escape (A : ℕ → ℝ) (nonneg : ∀ n, 0 ≤ A n)
    (unbounded : ∀ b : ℝ, ∃ n : ℕ, 0 < n ∧ b < A n)
    (N : ℝ → ℕ) (positive : ∀ e > 0, 0 < N e)
    (maximal : ∀ e > 0, ∀ n : ℕ, 0 < n →
      A n / (n : ℝ)^e ≤ A (N e) / (N e : ℝ)^e) :
    Tendsto N (𝓝[>] 0) atTop := by
  apply tendsto_atTop.mpr
  intro k
  obtain ⟨u,hu,high⟩ := exists_max_image (Icc 0 k) A ⟨0,mem_Icc.mpr ⟨le_rfl,Nat.zero_le _⟩⟩
  obtain ⟨w,hw,above⟩ := unbounded (A u)
  have wp : (0 : ℝ) < w := by exact_mod_cast hw
  have near : Tendsto (fun e : ℝ => A w / (w : ℝ)^e) (𝓝[>] 0) (𝓝 (A w)) := by
    have cont : ContinuousAt (fun e : ℝ => A w / (w : ℝ)^e) 0 := by
      fun_prop (disch := simp [wp.ne'])
    simpa using (cont.continuousWithinAt (s := Set.Ioi 0)).tendsto
  filter_upwards [near.eventually_const_lt above, self_mem_nhdsWithin] with e win ep
  have ep' : 0 < e := ep
  have np := positive e ep'
  have denom : 1 ≤ (N e : ℝ)^e := one_le_rpow (by exact_mod_cast np) ep'.le
  by_contra! small
  have loss := div_le_self (nonneg (N e)) denom
  exact (not_lt_of_ge (high (N e) (mem_Icc.mpr ⟨Nat.zero_le _,small.le⟩)))
    (win.trans_le ((maximal e ep' w hw).trans loss))

theorem bounded_of_limsup_ne_zero {F : Filter α} {u : α → ℝ}
    (h : limsup u F ≠ 0) : F.IsBoundedUnder (· ≤ ·) u := by
  by_contra no_bound
  have empty : {a : ℝ | ∀ᶠ i in F, u i ≤ a} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact no_bound (isBoundedUnder_of_eventually_le ha)
  exact h (by rw [limsup_eq,empty,Real.sInf_empty])

end GronwallCA

/- The tangent exponent vanishes along the positive half-line, and a maximizer at
this exponent dominates the original logarithmically normalized value. -/
namespace GronwallCA
open Filter Real Topology

noncomputable def slope (n : ℕ) : ℝ := 1 / (log n * log (log n))

theorem slope_tends_to_zero : Tendsto slope atTop (𝓝[>] 0) := by
  have h : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh := tendsto_log_atTop.comp h
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · refine (tendsto_inv_atTop_zero.comp (h.atTop_mul_atTop₀ hh)).congr ?_
    intro n
    simp [slope, one_div]
  · filter_upwards [h.eventually_gt_atTop 1] with n hn
    exact one_div_pos.mpr (mul_pos (zero_lt_one.trans hn) (log_pos hn))

theorem tangent_dominates (A : ℕ → ℝ) {n r : ℕ} (hn : 3 ≤ n) (hr : 3 ≤ r)
    (nn : 0 ≤ A n) (high : A n / (n : ℝ)^(slope n) ≤ A r / (r : ℝ)^(slope n)) :
    A n / log (log n) ≤ A r / log (log r) := by
  have large (w : ℕ) (hw : 3 ≤ w) : 1 < log (w : ℝ) := by
    have wbig : (3 : ℝ) ≤ w := by exact_mod_cast hw
    exact (lt_log_iff_exp_lt (by linarith)).mpr (exp_one_lt_three.trans_le wbig)
  have np : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have rp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have nlog := log_pos (large n hn)
  have rlog := log_pos (large r hr)
  have npow := rpow_pos_of_pos np (slope n)
  have rpowpos := rpow_pos_of_pos rp (slope n)
  have h := RobinRecord.double_log_tangent (large r hr) (large n hn) rp np
  change log (log r) / log (log n) ≤ ((r : ℝ) / n)^(slope n) at h
  rw [div_rpow rp.le np.le] at h
  have tangent := (div_le_div_iff₀ nlog npow).mp h
  have maxine := (div_le_div_iff₀ npow rpowpos).mp high
  apply (div_le_div_iff₀ nlog rlog).mpr
  apply le_of_mul_le_mul_right (a := (n : ℝ)^(slope n)) _ npow
  calc
    A n * log (log r) * (n : ℝ)^(slope n) = A n * (log (log r) * (n : ℝ)^(slope n)) := by ring
    _ ≤ A n * ((r : ℝ)^(slope n) * log (log n)) := mul_le_mul_of_nonneg_left tangent nn
    _ = (A n * (r : ℝ)^(slope n)) * log (log n) := by ring
    _ ≤ (A r * (n : ℝ)^(slope n)) * log (log n) := mul_le_mul_of_nonneg_right maxine nlog.le
    _ = A r * log (log n) * (n : ℝ)^(slope n) := by ring
end GronwallCA

/- A Gronwall-type limsup transfers to any choice of global power-weighted
maximizers. The unboundedness and the escape of the maximizing indices are
consequences of the limsup premise. -/
namespace GronwallCA
open Real Filter Topology

theorem selection_limsup (A : ℕ → ℝ) (nonneg : ∀ n, 0 ≤ A n)
    (positive : ∀ n, 0 < n → 0 < A n) (g : ℝ) (N : ℝ → ℕ)
    (index_pos : ∀ e > 0, 0 < N e)
    (global : ∀ e > 0, ∀ n : ℕ, 0 < n →
      A n / (n : ℝ)^e ≤ A (N e) / (N e : ℝ)^e)
    (gronwall : limsup (fun n : ℕ => A n / log (log n)) atTop = exp g) :
    limsup (fun e : ℝ => log (A (N e) / log (log (N e)))) (𝓝[>] 0) = g := by
  let R (n : ℕ) := A n / log (log n)
  change limsup R atTop = exp g at gronwall
  change limsup (fun e : ℝ => log (R (N e))) (𝓝[>] 0) = g
  have loglog_top : Tendsto (fun n : ℕ => log (log n)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have Rpos : ∀ᶠ n : ℕ in atTop, 0 < R n := by
    filter_upwards [loglog_top.eventually_gt_atTop 0,eventually_gt_atTop (0 : ℕ)] with n hn hp
    exact div_pos (positive n hp) hn
  have cob : atTop.IsCoboundedUnder (· ≤ ·) R :=
    isCoboundedUnder_le_of_eventually_le atTop (Rpos.mono fun _ h => h.le)
  have bounded := bounded_of_limsup_ne_zero (gronwall.trans_ne (exp_pos g).ne')
  have often (z : ℝ) (hz : z < exp g) : ∃ᶠ n : ℕ in atTop, z < R n :=
    frequently_lt_of_lt_limsup cob (hz.trans_eq gronwall.symm)
  have grows : ∀ b : ℝ, ∃ n : ℕ, 0 < n ∧ b < A n := by
    intro b
    let c := exp g / 2
    have cp : 0 < c := half_pos (exp_pos _)
    have freq := often c (half_lt_self (exp_pos g))
    obtain ⟨n,better,large,lnpos,np⟩ := (freq.and_eventually
      ((loglog_top.eventually_gt_atTop (b / c)).and
        ((loglog_top.eventually_gt_atTop 0).and (eventually_gt_atTop (0 : ℕ))))).exists
    exact ⟨n,np,((div_lt_iff₀ cp).mp large).trans
      (by simpa only [mul_comm] using (lt_div_iff₀ lnpos).mp better)⟩
  have escapes := maximizers_escape A nonneg grows N index_pos global
  have upper (z : ℝ) (hz : g < z) : ∀ᶠ e in 𝓝[>] (0 : ℝ), log (R (N e)) < z := by
    have eventual := eventually_lt_of_limsup_lt (gronwall.trans_lt (exp_lt_exp.mpr hz)) bounded
    filter_upwards [escapes.eventually eventual,escapes.eventually Rpos] with e he hr
    exact (log_lt_iff_lt_exp hr).mpr he
  have epspos : ∀ᶠ n : ℕ in atTop, 0 < slope n := slope_tends_to_zero.eventually self_mem_nhdsWithin
  have height : ∀ᶠ n : ℕ in atTop, R n ≤ R (N (slope n)) := by
    filter_upwards [eventually_ge_atTop (3 : ℕ),epspos,
        (escapes.comp slope_tends_to_zero).eventually_ge_atTop 3] with n hn ep hr
    exact tangent_dominates A hn hr (nonneg n) (global _ ep n (by omega))
  have lower (z : ℝ) (hz : z < g) : ∃ᶠ e in 𝓝[>] (0 : ℝ), z < log (R (N e)) := by
    have freq := (often (exp z) (exp_lt_exp.mpr hz)).and_eventually height
    have pull : ∃ᶠ n : ℕ in atTop, z < log (R (N (slope n))) := by
      refine freq.mono fun n ⟨high,comparison⟩ => ?_
      have h := high.trans_le comparison
      exact (lt_log_iff_exp_lt ((exp_pos _).trans h)).mpr h
    exact (show ∃ᶠ e in map slope atTop, z < log (R (N e)) from pull).filter_mono slope_tends_to_zero
  have upper_bdd := isBoundedUnder_of_eventually_le
    ((upper (g+1) (by linarith)).mono fun _ h => h.le)
  have lower_bdd : (𝓝[>] (0 : ℝ)).IsCoboundedUnder (· ≤ ·) (fun e => log (R (N e))) := by
    refine ⟨g-1,fun b hb => ?_⟩
    change ∀ᶠ e in 𝓝[>] (0 : ℝ), log (R (N e)) ≤ b at hb
    obtain ⟨e,he,ub⟩ := ((lower (g-1) (by linarith)).and_eventually hb).exists
    exact he.le.trans ub
  exact le_antisymm ((limsup_le_iff lower_bdd upper_bdd).mpr upper)
    ((le_limsup_iff lower_bdd upper_bdd).mpr lower)
end GronwallCA

/- The assertion about the right-hand limit superior in the edit of
MathOverflow question 395437, with its greatest maximizing integer at ties. -/

namespace CA395437
open OMA.S_mo_395437 Filter Real Topology
open ArithmeticFunction (sigma)

theorem gronwall_implies_score_limsup :
    limsup ratio atTop = exp eulerMascheroniConstant →
      limsup score (𝓝[>] 0) = eulerMascheroniConstant := by
  intro gronwall
  exact GronwallCA.selection_limsup abundancy
    (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun n hn => div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 n hn.ne')
      (by exact_mod_cast hn)) eulerMascheroniConstant candidate
    (fun _ he => (candidate_is_max he).1) (fun _ he => (candidate_is_max he).2) gronwall

end CA395437

namespace CA395437

/-- Multiplication by 3 increases the iterated logarithm by more than
one 120th of its former value at the first witness. -/
theorem double_log_gap :
    (121 : ℝ)/120 * Real.log (Real.log 2021649740510400) <
      Real.log (Real.log (3 * 2021649740510400)) := by
  let A := Real.log 2021649740510400
  let B := Real.log (3 * 2021649740510400)
  change (121 : ℝ)/120 * Real.log A < Real.log B
  have hA : 0 < A := Real.log_pos (by norm_num)
  have hB : 0 < B := Real.log_pos (by norm_num)
  have hAB : B = Real.log 3 + A := Real.log_mul (by norm_num) (by norm_num)
  have smallA : A < (354 : ℝ)/10 := by
    have h : A < Real.log ((2 : ℝ)^51) := Real.log_lt_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h
    norm_num1 at h
    linarith [Real.log_two_lt_d9]
  have smallB : B < (365 : ℝ)/10 := by linarith [Real.log_three_lt_d9]
  have small : Real.log A < (36 : ℝ)/10 := by
    have h : Real.log A < Real.log ((2 * 3 : ℝ)^2) :=
      Real.log_lt_log hA (by linarith)
    rw [Real.log_pow, Real.log_mul (by norm_num) (by norm_num)] at h
    norm_num1 at h
    linarith [Real.log_two_lt_d9, Real.log_three_lt_d9]
  have ratio : (3 : ℝ)/100 < Real.log 3 / B :=
    (lt_div_iff₀ hB).2 (by linarith [Real.log_three_gt_d9])
  have convex := Real.one_sub_inv_le_log_of_pos (div_pos hB hA)
  have cancel : 1 - (B/A)⁻¹ = Real.log 3 / B := by
    rw [inv_div]; field_simp; linarith
  rw [cancel, Real.log_div hB.ne' hA.ne'] at convex
  linarith

/-- For positive abundance and normalizing factors, a strict relative gain in
the normalizer forces a strict decrease in the normalized abundance. -/
theorem normalized_drop {a b u v k : ℝ} (ha : 0 < a) (hu : 0 < u) (hv : 0 < v)
    (gain : b = k * a) (gap : k * u < v) : b / v < a / u := by
  apply (div_lt_div_iff₀ hv hu).2
  rw [gain]
  calc
    k * a * u = a * (k * u) := by ring
    _ < a * v := mul_lt_mul_of_pos_left gap ha

/-- Score drop when abundances are recorded as divisor sums divided by the index. -/
theorem score_drop {s t n m a b k : ℝ} (abundant : 0 < s/n)
    (positive_old : 0 < a) (positive_new : 0 < b)
    (gain : t/m = k*(s/n)) (gap : k*a < b) : t/(m*b) < s/(n*a) := by
  simpa only [div_div] using normalized_drop abundant positive_old positive_new gain gap

end CA395437

namespace CA395437
open OMA.S_mo_395437 Real
open ArithmeticFunction (sigma)

theorem witness_exponent : (2021649740510400 : ℕ).factorization 3 = 3 := by
  rw [show (2021649740510400:ℕ) = 3^3 * 74875916315200 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow_self (by decide : Nat.Prime 3),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬3 ∣ 74875916315200), Nat.add_zero]

private theorem gain_at_three (n : ℕ) (hn : 0 < n) (hthree : n.factorization 3 = 3) :
    abundancy (n*3) = (121:ℝ)/120 * abundancy n := by
  have hs : (0:ℝ) < (sigma 1 n : ℝ) := by exact_mod_cast ArithmeticFunction.sigma_pos 1 n hn.ne'
  have h := RobinProfile.prime_gain (p:=3) (n:=n) (by decide) hn.ne'
  rw [hthree] at h
  have ratio : (sigma 1 (n*3) : ℝ) / (3 * (sigma 1 n : ℝ)) = 121/120 := by
    calc _ = _ := h
         _ = _ := by norm_num
  have num := (div_eq_iff (show 3*(sigma 1 n:ℝ) ≠ 0 by positivity)).1 ratio
  unfold abundancy
  rw [Nat.cast_mul, Nat.cast_ofNat, num]
  ring

theorem abundance_gain : abundancy 6064949221531200 = (121:ℝ)/120 * abundancy 2021649740510400 :=
  gain_at_three 2021649740510400 (by decide) witness_exponent

theorem witness_score_drop : log (ratio 6064949221531200) < log (ratio 2021649740510400) := by
  have A : 0 < log (log (2021649740510400:ℝ)) :=
    log_pos (by exact (lt_trans (by norm_num : (1:ℝ)<1.0986122885)
      (Real.log_three_gt_d9.trans (log_lt_log (by norm_num) (by norm_num)))))
  have B : 0 < log (log (6064949221531200:ℝ)) :=
    A.trans (log_lt_log (log_pos (by norm_num)) (log_lt_log (by norm_num) (by norm_num)))
  have ab (n : ℕ) (hn : 0 < n) : 0 < abundancy n :=
    div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 n hn.ne') (by exact_mod_cast hn)
  apply log_lt_log (div_pos (ab _ (by decide)) B)
  exact normalized_drop (ab _ (by decide)) A B abundance_gain (by convert double_log_gap using 1 <;> norm_num)

end CA395437

namespace CA395437
open OMA.S_mo_395437

/-- These two maximizers refute monotonic increase of the score as the parameter decreases. -/
theorem not_monotone_of_candidates
    (first : candidate (1/125:ℝ) = 2021649740510400)
    (second : candidate (1/134:ℝ) = 6064949221531200) : ¬ monotonicity := by
  intro anti
  have line := anti (a:=1/134) (b:=1/125)
    (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num)
  rw [score, score, first, second] at line
  exact (not_le_of_gt witness_score_drop) line

end CA395437

namespace CA395437
open OMA.S_mo_395437

/-- The score strictly decreases when the parameter goes from 1/125 to 1/134. -/
theorem score_counterexample :
    candidate (1/125:ℝ) = 2021649740510400 ∧
    candidate (1/134:ℝ) = 6064949221531200 ∧
    score (1/134:ℝ) < score (1/125:ℝ) := by
  obtain ⟨ha, maximizesA⟩ := candidate_is_max (e:=1/125) (by norm_num)
  obtain ⟨hb, maximizesB⟩ := candidate_is_max (e:=1/134) (by norm_num)
  have ea := lower_index ha maximizesA
  have eb := upper_index hb maximizesB
  refine ⟨ea, eb, ?_⟩
  simpa only [score, ea, eb] using witness_score_drop

theorem not_monotone : ¬ monotonicity :=
  not_monotone_of_candidates score_counterexample.1 score_counterexample.2.1

end CA395437

namespace CA395437
open OMA.S_mo_395437

/-- With the monotonicity assertion refuted, the final comparison is equivalent to
the negation of the Riemann hypothesis. -/
theorem comparison_iff_not_rh : (monotonicity ↔ RiemannHypothesis) ↔ ¬ RiemannHypothesis := by
  constructor
  · exact fun h rh => not_monotone (h.mpr rh)
  · exact fun h => ⟨fun mon => (not_monotone mon).elim, fun rh => (h rh).elim⟩

end CA395437

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_395437.main) := by
  exact fun h => CA395437.not_monotone h.1
