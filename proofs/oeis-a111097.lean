import OMAStatements.S_oeis_a111097
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.GCD.Basic

/-! # The unique maximum-likelihood urn size for A111097

After observing n distinct draws with replacement followed by a repeat, let N be
the proposed number of marbles. The sign of the adjacent likelihood difference is
the sign of n minus a geometric sum in 1−1/(N+1). That sum is monotone in N.
Third- and fourth-order binomial bounds locate the sign change at the conjectured
integer. Equivalently, the answer for n ≥ 2 is ⌊n(3n+1)/6⌋. This proves the formulas of McKone, Alaa, and Spezia and gives a unique
maximizer for each positive n. Source: https://oeis.org/A111097
Credit: @sturdy4days
-/

namespace A111097
open OMA.S_oeis_a111097 Finset

def residual (n : ℕ) (t : ℚ) := (1 - 1/t)^(n+1) - (1 - n/t)
def comparison (n : ℕ) (t : ℚ) := (n : ℚ) - ∑ j ∈ range (n+1), (1-1/t)^j

theorem residual_scale (n : ℕ) {t : ℚ} (ht : 0 < t) :
    t * residual n t = comparison n t := by
  have h := geom_sum_mul_neg (1 - 1/t) (n+1)
  simp only [sub_sub_cancel] at h
  unfold residual comparison
  have hu : (∑ j ∈ range (n+1), (1-1/t)^j) / t = 1 - (1-1/t)^(n+1) := by simpa [div_eq_mul_inv] using h
  rw [(div_eq_iff ht.ne').mp hu]
  generalize (1-1/t)^(n+1) = z
  field_simp
  ring

theorem comparison_antitone (n : ℕ) {s t : ℚ} (hs : 1 ≤ s) (hst : s ≤ t) :
    comparison n t ≤ comparison n s := by
  apply sub_le_sub_left
  have sp : 0 < s := by linarith
  have invle : 1/t ≤ 1/s := one_div_le_one_div_of_le sp hst
  have u : 0 ≤ 1-1/s := by
    have := one_div_le_one_div_of_le (by decide : (0:ℚ)<1) hs
    exact sub_nonneg.mpr (by simpa only [div_one] using this)
  exact sum_le_sum fun j _ => pow_le_pow_left₀ u (by linarith) j

theorem step_identity (n N : ℕ) (hN : 0 < N) (hnN : n ≤ N+1) :
    (likelihood n (N+1) - likelihood n N) * (N : ℚ)^(n+1) =
      (n : ℚ) * ((N+1).descFactorial n : ℚ) * residual n (N+1) := by
  have np : (0:ℚ)<N := by exact_mod_cast hN
  have sp : (0:ℚ)<(N:ℚ)+1 := by linarith
  have aux := Nat.succ_descFactorial N n
  have hc : ((N:ℚ)+1-n) * ((N+1).descFactorial n : ℚ) =
      ((N:ℚ)+1) * (N.descFactorial n : ℚ) := by
    have h : ((N+1-n : ℕ):ℚ) * ((N+1).descFactorial n : ℚ) =
      ((N+1 : ℕ):ℚ) * (N.descFactorial n : ℚ) := by exact_mod_cast aux
    simpa only [Nat.cast_sub hnN, Nat.cast_add, Nat.cast_one] using h
  have base : (1:ℚ)-1/(N+1) = N/(N+1) := by field_simp; ring
  have c : (N.descFactorial n : ℚ) = ((N+1).descFactorial n : ℚ) * (1-(n:ℚ)/(N+1)) := by
    field_simp [sp.ne']
    linear_combination -hc
  unfold likelihood residual
  push_cast
  rw [base, div_pow, sub_mul, div_mul_cancel₀ _ (pow_ne_zero _ np.ne'), c]
  ring

theorem shape_of_cutoff {n M : ℕ} (hn : 0<n) (hnM : n≤M)
    (left : 0 < residual n M) (right : residual n (M+1) ≤ 0) :
    (∀ K : ℕ, K<M → likelihood n K < likelihood n M) ∧
    (∀ N : ℕ, M≤N → likelihood n (N+1) ≤ likelihood n N) ∧
    (∀ j : ℕ, M≤j → likelihood n j ≤ likelihood n M) := by
  have hM : 0<M := by omega
  have positive : 0 < likelihood n M := by
    unfold likelihood
    have h : 0 < M.descFactorial n := Nat.descFactorial_pos.mpr hnM
    positivity
  have left_step (N : ℕ) (h : n ≤ N) (h' : N < M) : likelihood n N < likelihood n (N+1) := by
    have hN : 0<N := by omega
    have pos : (0:ℚ)<(M:ℚ) := by exact_mod_cast (show 0<M by omega)
    have ord := comparison_antitone n (s:=((N:ℚ)+1)) (t:=(M:ℚ)) (by linarith [Nat.cast_nonneg (α:=ℚ) N]) (by exact_mod_cast (show N+1≤M by omega))
    rw [← residual_scale n pos, ← residual_scale n (by positivity)] at ord
    have hpos : 0 < residual n ((N:ℚ)+1) := pos_of_mul_pos_right (lt_of_lt_of_le (mul_pos pos left) ord) (by positivity)
    have hdesc : 0 < (N + 1).descFactorial n := Nat.descFactorial_pos.mpr (by omega)
    have hprod := step_identity n N hN (by omega)
    have hr : 0 < (n:ℚ) * ((N+1).descFactorial n : ℚ) * residual n (↑N+1) := by positivity
    rw [← hprod] at hr
    exact sub_pos.mp (pos_of_mul_pos_left hr (by positivity))
  have right_step (N : ℕ) (h : M≤N) : likelihood n (N+1) ≤ likelihood n N := by
    have pos : (0:ℚ)<(M:ℚ)+1 := by positivity
    have ord := comparison_antitone n (s:=((M:ℚ)+1)) (t:=((N:ℚ)+1)) (by linarith [Nat.cast_nonneg (α:=ℚ) M]) (by exact_mod_cast Nat.succ_le_succ h)
    rw [← residual_scale n pos, ← residual_scale n (by positivity)] at ord
    have hr : residual n ((N:ℚ)+1) ≤ 0 := by
      by_contra! pos'
      exact (ord.trans (mul_nonpos_of_nonneg_of_nonpos pos.le right)).not_gt (mul_pos (by positivity) pos')
    have hprod := step_identity n N (by omega) (by omega)
    have hr' := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ (n:ℚ)*((N+1).descFactorial n : ℚ) by positivity) hr
    rw [← hprod] at hr'
    have hN : 0<N := by omega
    by_contra! gt
    exact hr'.not_gt (mul_pos (sub_pos.mpr gt) (by positivity))
  have before (K : ℕ) (hk : K<M) : likelihood n K < likelihood n M := by
    by_cases small : K<n
    · simpa [likelihood, Nat.descFactorial_eq_zero_iff_lt.mpr small] using positive
    · have nk : n≤K := by omega
      have go (j : ℕ) (lo : K+1≤j) (hi : j≤M) : likelihood n K < likelihood n j := by
        induction j, lo using Nat.le_induction with
        | base => exact left_step K nk hk
        | succ j hj ih => exact (ih (by omega)).trans (left_step j (by omega) (by omega))
      exact go M hk le_rfl
  have after (j : ℕ) (h : M≤j) : likelihood n j ≤ likelihood n M := by
    induction j, h using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj ih => exact (right_step j hj).trans ih
  exact ⟨before, right_step, after⟩

theorem mode_of_cutoff {n M : ℕ} (hn : 0<n) (hnM : n≤M)
    (left : 0 < residual n M) (right : residual n (M+1) ≤ 0) : a n=M := by
  obtain ⟨before, _, after⟩ := shape_of_cutoff hn hnM left right
  unfold a
  rw [if_neg hn.ne']
  apply IsLeast.csInf_eq
  constructor
  ·
    exact ⟨by omega, fun K _ => if h : K<M then (before K h).le else after K (by omega)⟩
  · rintro K ⟨_,best⟩
    by_contra! lt
    exact (before K lt).not_ge (best M (by omega))

end A111097

namespace A111097
open OMA.S_oeis_a111097
def tri (n : ℕ) := n*(n+1)/2

theorem tri_succ (n : ℕ) : tri (n+1) = tri n + (n+1) := by
  unfold tri
  rw [show (n+1)*(n+1+1)=n*(n+1)+2*(n+1) by ring, Nat.add_mul_div_left _ _ (by decide)]

theorem tri_large {n : ℕ} (hn : 2 ≤ n) : n + 1 + (n-1)/3 ≤ tri n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ k hk ih => rw [tri_succ]; omega

theorem large_mode {n : ℕ} (hn : 2 ≤ n) : n ≤ n*(n+1)/2-1-(n-1)/3 := by
  have := tri_large hn
  unfold tri at this
  omega

theorem diff_of_formula
    (one : a 1 = 1) (form : ∀ n : ℕ, 2 ≤ n → a n = n*(n+1)/2-1-(n-1)/3)
    (n : ℕ) (hn : 0<n) :
    (a (n+2):ℤ)-2*(a (n+1):ℤ)+(a n:ℤ) = secondDifferenceValue n := by
  by_cases h : n=1
  · subst n; norm_num [form _ (by decide : 2≤3),form _ (by decide : 2≤2),one,secondDifferenceValue]
  have rep (k : ℕ) (hk : 2≤k) : (a k:ℤ) = (tri k : ℤ)-1-(((k-1)/3 : ℕ):ℤ) := by
    rw [form k hk]
    change ((tri k - 1 - (k-1)/3 : ℕ) : ℤ) = _
    have := tri_large hk
    omega
  rw [rep n (by omega),rep (n+1) (by omega),rep (n+2) (by omega)]
  rw [show n+2 = (n+1)+1 by omega,tri_succ (n+1),tri_succ n]
  simp only [Nat.cast_add,Nat.cast_one]
  unfold secondDifferenceValue
  split_ifs <;> omega

open PowerSeries
private def diffCoeff : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | k+3 => secondDifferenceValue (k+1)

theorem series_of_differences (one : a 1 = 1) (two : a 2 = 2)
    (dif : ∀ n : ℕ, 0<n → (a (n+2):ℤ)-2*(a (n+1):ℤ)+(a n:ℤ) = secondDifferenceValue n) :
    (1-X)^3 * (1+X+X^2) * mk (fun n => (a n:ℤ)) =
      X * (1+2*X^2-X^3+2*X^4-X^5) := by
  let A : PowerSeries ℤ := mk fun n => (a n:ℤ)
  have h0 : a 0 = 0 := by simp [a]
  have d : (A*(1-X))*(1-X) = mk diffCoeff := by
    ext j
    rcases j with _ | _ | _ | k
    · simp [A, coeff_zero_eq_constantCoeff, diffCoeff, h0]
    · simp [A,mul_sub,map_sub,coeff_succ_mul_X,coeff_zero_eq_constantCoeff,diffCoeff,one,h0]
    · simp [A,mul_sub,map_sub,coeff_succ_mul_X,diffCoeff,two,one,h0]
    · simp only [mul_sub,mul_one,map_sub,coeff_succ_mul_X,A,coeff_mk,diffCoeff]
      linarith [dif (k+1) (by omega)]
  have last : mk diffCoeff * (1-X^3) = X*(1+2*X^2-X^3+2*X^4-X^5) := by
    have pol : (X*(1+2*X^2-X^3+2*X^4-X^5) : PowerSeries ℤ) =
        X + X^3 + X^3 - X^4 + X^5 + X^5 - X^6 := by ring
    rw [pol]
    ext j
    rw [mul_sub,mul_one,map_sub,coeff_mul_X_pow',coeff_mk]
    rcases j with _ | _ | _ | _ | _ | _ | _ | k
    all_goals simp [diffCoeff,secondDifferenceValue,coeff_X,coeff_X_pow]
    split_ifs <;> omega
  change (1-X)^3*(1+X+X^2)*A=_
  calc (1-X)^3*(1+X+X^2)*A = (A*(1-X)*(1-X))*(1-X^3) := by ring
       _ = _ := by rw [d,last]

end A111097

/-! The two adjacent binomial probabilities at the conjectured likelihood maximum. -/

namespace A111097

/-- The third and fourth Bonferroni truncations bound the probability of no successes. -/
theorem bonferroni {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (n : ℕ) (hn : 2 ≤ n) (x : F) (hx : 0 ≤ x) (hx' : x ≤ 1) :
    1 - (n+1)*x + (n+1)*n*x^2/2 - (n+1)*n*(n-1)*x^3/6 ≤ (1-x)^(n+1) ∧
    (1-x)^(n+1) ≤ 1 - (n+1)*x + (n+1)*n*x^2/2 - (n+1)*n*(n-1)*x^3/6 +
      (n+1)*n*(n-1)*(n-2)*x^4/24 := by
  induction n, hn using Nat.le_induction with
  | base =>
    norm_num
    constructor <;> ring_nf <;> rfl
  | succ n hn ih =>
    have htwo : (2:F) ≤ n := by exact_mod_cast hn
    have h₃ : 0 ≤ ((n:F)+1)*n*(n-1)*x^4 := by
      have : 0 ≤ (n:F)-1 := by linarith
      positivity
    have h₄ : 0 ≤ ((n:F)+1)*n*(n-1)*(n-2)*x^5 := by
      have : 0 ≤ (n:F)-1 := by linarith
      have : 0 ≤ (n:F)-2 := by linarith
      positivity
    rw [pow_succ (1-x) (n+1)]
    push_cast
    exact ⟨by nlinarith only [mul_le_mul_of_nonneg_right ih.1 (sub_nonneg.mpr hx'),h₃],
           by nlinarith only [mul_le_mul_of_nonneg_right ih.2 (sub_nonneg.mpr hx'),h₄]⟩

/-- The strict lower comparison and the weak upper comparison at two consecutive orders. -/
theorem cutoff_estimates_in {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (n : ℕ) (hn : 2 ≤ n) :
    let M := n*(n+1)/2-1-(n-1)/3
    1-(n:F)/(M:F) < (1-1/(M:F))^(n+1) ∧
      (1-1/((M+1:ℕ):F))^(n+1) ≤ 1-(n:F)/((M+1:ℕ):F) := by
  let a := (n-1)/3
  let C := n*(n+1)/2
  let M := C-1-a
  change 1-(n:F)/(M:F) < _ ∧ _ ≤ 1-(n:F)/((M+1:ℕ):F)
  have hd : 2 ∣ n*(n+1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self n)
  have htri : 2*C=n*(n+1) := by dsimp [C]; omega
  have hnC : n ≤ C := by nlinarith [Nat.mul_le_mul_left n (show 2 ≤ n+1 by omega)]
  have ha : a+1 < n := by dsimp [a]; omega
  have hsum : M+a+1=C := by dsimp [M]; omega
  have hpos : 1 ≤ M := by omega
  have hpos' : (1:F) ≤ M := by exact_mod_cast hpos
  have htri' : 2*(C:F)=(n:F)*(n+1) := by exact_mod_cast htri
  have hsum' : (M:F)+a+1=C := by exact_mod_cast hsum
  have form : (M:F) = (n:F)*(n+1)/2-a-1 := by linarith
  have cert :
      0 < 6*((C:F)-M)*M-(n+1: F)*n*(n-1) ∧
      0 ≤ (n+1:F)*n*(n-1)*(4*(M+1)-(n-2))-24*a*(M+1)^2 := by
    have cases : n=3*a+1 ∨ n=3*a+2 ∨ n=3*a+3 := by dsimp [a]; omega
    have Cform : (C:F)=(n:F)*(n+1)/2 := by linarith
    rw [Cform,form]
    rcases cases with h | h | h
    · have h' : (n:F)=3*a+1 := by exact_mod_cast h
      have ha' : 0 < (a:F) := by exact_mod_cast (show 0<a by omega)
      rw [h']; constructor <;> ring_nf <;> positivity
    · have h' : (n:F)=3*a+2 := by exact_mod_cast h
      rw [h']; constructor <;> ring_nf <;> positivity
    · have h' : (n:F)=3*a+3 := by exact_mod_cast h
      rw [h']; constructor <;> ring_nf <;> positivity
  have x1 : 0 < (M:F) := by linarith
  have x2 : 0 < (M:F)+1 := by linarith
  have lower := (bonferroni n hn (1/(M:F)) (by positivity)
    ((div_le_one x1).mpr hpos')).1
  have upper := (bonferroni n hn (1/((M:F)+1)) (by positivity)
    ((div_le_one x2).mpr (by linarith))).2
  push_cast
  constructor
  · apply lt_of_lt_of_le _ lower
    field_simp
    nlinarith only [cert.1, htri']
  · apply le_trans upper
    field_simp
    nlinarith only [cert.2,hsum',htri']

theorem cutoff_estimates (n : ℕ) (hn : 2 ≤ n) :
    let M := n*(n+1)/2-1-(n-1)/3
    1-(n:ℚ)/(M:ℚ) < (1-1/(M:ℚ))^(n+1) ∧
      (1-1/((M+1:ℕ):ℚ))^(n+1) ≤ 1-(n:ℚ)/((M+1:ℕ):ℚ) :=
  cutoff_estimates_in n hn

end A111097

/-! At integer urn sizes the likelihood comparison is always strict. -/

namespace A111097

theorem no_integer_tie (n m : ℕ) (hn : 0<n) (hm : 2≤m) :
    (1-1/(m:ℚ))^(n+1) ≠ 1-(n:ℚ)/m := by
  intro tie
  have mpos : (0:ℚ)<m := by exact_mod_cast (show 0<m by omega)
  have one : (1:ℚ)≤m := by exact_mod_cast (show 1≤m by omega)
  have cmp : n≤m := by
    by_contra! high
    have num : (m:ℚ)<n := by exact_mod_cast high
    have frac := (one_lt_div mpos).mpr num
    have pos := pow_nonneg (sub_nonneg.mpr ((div_le_one mpos).mpr one)) (n+1)
    linarith
  have l : (1:ℚ)-1/m=((m:ℚ)-1)/m := by field_simp
  have r : 1-(n:ℚ)/m=((m:ℚ)-n)/m := by field_simp
  rw [l,r, div_pow,div_eq_div_iff (pow_ne_zero _ mpos.ne') mpos.ne',pow_succ (m:ℚ)] at tie
  have eq : ((m:ℚ)-1)^(n+1)=((m:ℚ)-n)*m^n := by
    apply mul_right_cancel₀ mpos.ne'
    simpa only [mul_assoc] using tie
  have eqN : (m-1)^(n+1)=(m-n)*m^n := by
    exact_mod_cast (by simpa only [Nat.cast_sub (show 1≤m by omega),Nat.cast_sub cmp,Nat.cast_one] using eq :
      ((m-1:ℕ):ℚ)^(n+1)=((m-n:ℕ):ℚ)*m^n)
  have cp := (Nat.coprime_self_sub_left (show 1≤m by omega)).mpr (Nat.coprime_one_left _)
  have dv : m ∣ (m-1)^(n+1) := eqN ▸ dvd_mul_of_dvd_right (dvd_pow_self m hn.ne') _
  have := Nat.eq_one_of_dvd_coprimes (cp.pow_left (n+1)) dv (dvd_refl m)
  omega

end A111097

namespace A111097
open OMA.S_oeis_a111097

theorem first_mode : a 1 = 1 := by
  unfold a
  rw [if_neg (by decide)]
  apply IsLeast.csInf_eq
  constructor
  · refine ⟨by decide,?_⟩
    intro K hk
    have hk' : 0<(K:ℚ) := by exact_mod_cast hk
    have oneK : (1:ℚ) ≤ K := by exact_mod_cast hk
    simp only [likelihood,Nat.descFactorial_one,Nat.cast_one,one_mul,one_pow,div_one]
    field_simp [hk'.ne']
    norm_num1
    nlinarith [mul_nonneg hk'.le (sub_nonneg.mpr oneK)]
  · rintro _ ⟨hp,_⟩
    exact hp

theorem exact_mode (n : ℕ) (hn : 2≤n) : a n=n*(n+1)/2-1-(n-1)/3 := by
  obtain ⟨lo,hi⟩ := cutoff_estimates n hn
  apply mode_of_cutoff (by omega) (large_mode hn)
  · exact sub_pos.mpr lo
  · simpa only [residual, Nat.cast_add, Nat.cast_one] using sub_nonpos.mpr hi

end A111097

namespace A111097
open OMA.S_oeis_a111097

/-- For positive integer urn sizes the maximizer is unique. -/
theorem strict_maximum (n : ℕ) (hn : 0<n) (K : ℕ) (hk : 0<K) (hne : K ≠ a n) :
    likelihood n K < likelihood n (a n) := by
  by_cases small : n=1
  · subst n
    rw [first_mode] at hne ⊢
    have hK : (1:ℚ)<K := by exact_mod_cast (show 1<K by omega)
    have kpos : (0:ℚ)<K := by positivity
    simp only [likelihood,Nat.descFactorial_one,Nat.cast_one,one_mul,one_pow,div_one]
    field_simp
    norm_num1
    nlinarith [mul_pos kpos (sub_pos.mpr hK)]
  have htwo : 2≤n := by omega
  let M := n*(n+1)/2-1-(n-1)/3
  have hM : n ≤ M := large_mode htwo
  obtain ⟨lo,hi⟩ := cutoff_estimates n htwo
  have pos : 0<residual n M := sub_pos.mpr lo
  have neg : residual n ((M:ℚ)+1) ≤ 0 := by
    simpa only [M, residual,Nat.cast_add,Nat.cast_one] using sub_nonpos.mpr hi
  have ⟨left,step,after⟩ := shape_of_cutoff hn hM pos neg
  have eq : a n=M := exact_mode n htwo
  rw [eq] at hne ⊢
  rcases lt_or_gt_of_ne hne with h | h
  · exact left _ h
  · obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    have hNM : M≤N := by omega
    apply lt_of_lt_of_le _ (after N hNM)
    apply lt_of_le_of_ne (step _ hNM)
    intro tie
    have barrier := step_identity n N (by omega) (by omega)
    rw [tie,sub_self,zero_mul] at barrier
    have pd : 0 < (N+1).descFactorial n := Nat.descFactorial_pos.mpr (by omega)
    have nz : (n : ℚ)*((N+1).descFactorial n : ℚ) ≠ 0 := by positivity
    have hz := (mul_eq_zero.mp barrier.symm).resolve_left nz
    exact no_integer_tie n (N+1) hn (by omega) (by
      simpa only [Nat.cast_add,Nat.cast_one] using sub_eq_zero.mp hz)
end A111097

/-! The three congruence classes combine into a single integer quotient. -/
namespace A111097
open OMA.S_oeis_a111097

theorem simple_mode (n : ℕ) (hn : 2≤n) : a n = n * (3*n+1)/6 := by
  rw [exact_mode n hn]
  have even : 2 ∣ n*(n+1) := by
    rcases Nat.even_or_odd n with ⟨k,h⟩|⟨k,h⟩
    · exact ⟨k*(n+1), by nlinarith [congrArg (·*(n+1)) h]⟩
    · exact ⟨n*(k+1), by nlinarith [congrArg (n*·) h]⟩
  obtain ⟨v,hv⟩ := even
  have ht : n*(3*n+1)+2*n=3*(n*(n+1)) := by ring
  have lo := large_mode hn
  omega

end A111097

theorem OMA.solution : type_of% @OMA.S_oeis_a111097.main := by
  have d := A111097.diff_of_formula A111097.first_mode A111097.exact_mode
  exact ⟨A111097.first_mode, A111097.exact_mode, d,
    A111097.series_of_differences A111097.first_mode (by simpa using A111097.exact_mode 2 (by decide)) d⟩
