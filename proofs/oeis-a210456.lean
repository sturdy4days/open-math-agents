import OMAStatements.S_oeis_a210456

/-!
# Digital-root periods of multinacci sequences

Paolo P. Lava and Robert G. Wilson v introduced OEIS A210456 in 2013.
Fred W. Helenius proposed the two period formulas in 2013. Hans Havermann
identified the modulus-nine interpretation and Shixuan Gao related the eventual
period to A351889. Chai Wah Wu had conjectured the characteristic-three
orders in A337212 and a prime-modulus generalization in A351889. The registered sequence starts with genuine zero digits;
the proof tracks their disappearance before passing to residues.

For a width of q−1 or q, with q a positive power of three, the denominator
modulo three describes an affine trace line in a quadratic extension or a
trace-zero projective line in a cubic extension. Ratios give the exact
multiplicative orders q²−1 and q²+q+1. The quadratic argument is the
classical trace-one relative difference set (Dieter Jungnickel, RICAM 2013,
slide 15). The cubic difference-set theorem
is Corollary 1.2 of Mészáros, Rónyai and Szabó (2019), arXiv:1908.05591. The lift to modulus nine gains at most
a factor of three. For every width at least two its presence is necessary:
the companion's trace differs from its third-power trace modulo nine. The
matrix trace congruence used here is a special case of the results of
V. I. Arnold (2004, p. 1119), A. V. Zarelua (2008) and Heinrich Steinlein
(2017).
-/


namespace Multinacci
open OMA.S_oeis_a210456

lemma root_cast (m : ℕ) : (digitalRoot m : ZMod 9) = m := by
  unfold digitalRoot
  split_ifs with h
  · simp [h]
  · apply (ZMod.natCast_eq_natCast_iff _ _ _).2
    change ((m - 1) % 9 + 1) % 9 = m % 9
    omega

lemma root_bounds {m : ℕ} (hm : 0 < m) : 1 ≤ digitalRoot m ∧ digitalRoot m ≤ 9 := by
  simp only [digitalRoot, if_neg (Nat.ne_of_gt hm)]
  omega

lemma state_succ (n k : ℕ) : vstate n (k+1) = vstep n (vstate n k) := by
  exact Function.iterate_succ_apply' _ _ _

lemma state_head {n : ℕ} (hn : 0 < n) (k i : ℕ) (hi : i < n) :
    seqN n (k+i) = vstate n k ⟨i,hi⟩ := by
  induction i generalizing k with
  | zero => simp [seqN, hn]
  | succ i ih =>
    rw [show k + (i+1) = (k+1)+i by omega, ih (k+1) (by omega), state_succ]
    simp [vstep, hi]

lemma state_last {n : ℕ} (hn : 0 < n) (k : ℕ) :
    1 ≤ vstate n k ⟨n-1, by omega⟩ ∧ vstate n k ⟨n-1, by omega⟩ ≤ 9 := by
  induction k with
  | zero => simp [vstate, vinit, show ¬ n-1+1 < n by omega]
  | succ k ih =>
    rw [state_succ]
    simp only [vstep, show ¬ n-1+1 < n by omega, ↓reduceDIte]
    apply root_bounds
    exact ih.1.trans <| Finset.single_le_sum (f := vstate n k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨n-1, by omega⟩ : Fin n))

lemma digits_bounded {n k : ℕ} (hn : 0 < n) (hk : n-1 ≤ k) :
    1 ≤ seqN n k ∧ seqN n k ≤ 9 := by
  have h := state_head hn (k-(n-1)) (n-1) (by omega)
  rw [Nat.sub_add_cancel hk] at h
  rw [h]; exact state_last hn _

lemma seed {n i : ℕ} (hi : i < n) : seqN n i = if i+1 < n then 0 else 1 := by
  simpa [vstate, vinit] using state_head (n:=n) (by omega) 0 i hi

lemma recurrence {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (seqN n (k+n) : ZMod 9) = ∑ i : Fin n, (seqN n (k+i.val) : ZMod 9) := by
  have h := state_head hn (k+1) (n-1) (by omega)
  rw [show k+1+(n-1)=k+n by omega, state_succ] at h
  simp only [vstep, show ¬ n-1+1 < n by omega, ↓reduceDIte] at h
  rw [h, root_cast, Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => congrArg (fun x : ℕ => (x : ZMod 9)) (state_head hn k i.val i.isLt).symm

lemma period_iff_residues {n p : ℕ} (hn : 0 < n) :
    IsEventualPeriod n p ↔ ∃ t, ∀ k : ℕ, t ≤ k →
        (seqN n (k+p) : ZMod 9) = seqN n k := by
  constructor
  · rintro ⟨t,ht⟩; exact ⟨t,fun k hk => congrArg (fun x : ℕ => (x : ZMod 9)) (ht k hk)⟩
  · rintro ⟨t,ht⟩
    refine ⟨max t n, fun k hk => ?_⟩
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).1 (ht k (by omega))
    have a := digits_bounded (k:=k+p) hn (by omega)
    have b := digits_bounded (k:=k) hn (by omega)
    change seqN n (k+p) % 9 = seqN n k % 9 at h
    omega

end Multinacci

namespace Multinacci

open Finset Polynomial
open scoped PowerSeries

/-- Reciprocal characteristic polynomial of the width-n recurrence. -/
noncomputable def denom (R : Type*) [CommRing R] (n : ℕ) : R[X] :=
  1 - X * ∑ i ∈ range n, X ^ i

theorem periodSeries_iff {R : Type*} [CommRing R] (p : ℕ) (f : R⟦X⟧) :
    (∃ t, ∀ k : ℕ, t ≤ k → PowerSeries.coeff (k+p) f = PowerSeries.coeff k f) ↔
      ∃ h : R[X], f * (1 - PowerSeries.X ^ p) = (h : R⟦X⟧) := by
  constructor
  · rintro ⟨t,period⟩
    let g := f * (1 - PowerSeries.X ^ p)
    refine ⟨g.trunc (t+p), PowerSeries.ext fun k => ?_⟩
    change PowerSeries.coeff k g = _
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with le
    · rfl
    · change PowerSeries.coeff k (f * (1 - PowerSeries.X ^ p)) = 0
      rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow', if_pos (by omega)]
      exact sub_eq_zero.mpr (by simpa [Nat.sub_add_cancel (show p ≤ k by omega)] using period (k-p) (by omega))
  · rintro ⟨h,he⟩
    refine ⟨h.natDegree+1, fun k hk => ?_⟩
    have hz := congrArg (PowerSeries.coeff (k+p)) he
    rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow, Polynomial.coeff_coe,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)] at hz
    exact sub_eq_zero.mp hz

theorem period_of_denominator {R : Type*} [CommRing R] (n p : ℕ)
    {f : R⟦X⟧} {b : R[X]} (equation : f * (denom R n : R⟦X⟧) = (b : R⟦X⟧))
    (dvd : denom R n ∣ 1-X^p) :
    ∃ t, ∀ k : ℕ, t ≤ k → PowerSeries.coeff (k+p) f = PowerSeries.coeff k f := by
  obtain ⟨u,hu⟩ := dvd
  apply (periodSeries_iff p f).2
  refine ⟨b*u, ?_⟩
  have e := congrArg (fun z : R[X] => (z : R⟦X⟧)) hu
  simp only [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul] at e
  rw [e, ← mul_assoc, equation, Polynomial.coe_mul]

theorem period_iff_denominator {R : Type*} [CommRing R] (n p d : ℕ)
    {f : R⟦X⟧} (equation : f * (denom R n : R⟦X⟧) = PowerSeries.X ^ d) :
    (∃ t, ∀ k : ℕ, t ≤ k → PowerSeries.coeff (k+p) f = PowerSeries.coeff k f) ↔
      denom R n ∣ 1-X^p := by
  constructor
  · rintro per
    obtain ⟨h,he⟩ := (periodSeries_iff p f).1 per
    have cop : IsCoprime (denom R n) X := ⟨1, ∑ i ∈ range n, X ^ i, by simp [denom]; ring⟩
    apply cop.pow_right.dvd_of_dvd_mul_left (y := X^d)
    refine ⟨h, Polynomial.coe_injective R ?_⟩
    simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X, Polynomial.coe_pow]
    rw [← he, ← equation]; ring
  · exact period_of_denominator n p (b := X^d) (by simpa using equation)

end Multinacci

namespace Multinacci
open Finset Polynomial
open scoped PowerSeries

/-- Coefficients of the recurrence denominator times an arbitrary sequence. -/
theorem coeff_denom {R : Type*} [CommRing R] (u : ℕ → R) (n k : ℕ) :
    PowerSeries.coeff k (PowerSeries.mk u * (denom R n : R⟦X⟧)) =
      u k - ∑ i ∈ range n, if n-i ≤ k then u (k-(n-i)) else 0 := by
  have poly : denom R n = 1 - ∑ i ∈ range n, (X : R[X])^(n-i) := by
    rw [denom, mul_sum, ← sum_range_reflect (fun i => X * X^i) n]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [← pow_succ']
    congr 1; have := mem_range.mp hi; omega
  rw [poly, Polynomial.coe_sub, Polynomial.coe_one]
  have coe_sum' : ((∑ i ∈ range n, (X : R[X])^(n-i) : R[X]) : R⟦X⟧) =
      ∑ i ∈ range n, (PowerSeries.X : R⟦X⟧)^(n-i) := by
    exact (map_sum (Polynomial.coeToPowerSeries.ringHom : R[X] →+* R⟦X⟧)
      (fun i : ℕ => (X : R[X]) ^ (n-i)) (range n)).trans
      (sum_congr rfl (fun i _ => by rw [map_pow, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]))
  rw [coe_sum', mul_sub, mul_one, mul_sum, map_sub, map_sum]
  simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul_X_pow']

theorem coeff_denom_zero {R : Type*} [CommRing R] {u : ℕ → R} (n : ℕ)
    (rec : ∀ j, u (j+n) = ∑ i : Fin n, u (j+i.val)) {k : ℕ} (hk : n ≤ k) :
    PowerSeries.coeff k (PowerSeries.mk u * (denom R n : R⟦X⟧)) = 0 := by
  rw [coeff_denom, sub_eq_zero, ← Nat.sub_add_cancel hk, rec, Fin.sum_univ_eq_sum_range (fun i => u (k-n+i)) n]
  refine sum_congr rfl fun i hi => ?_
  have h := mem_range.mp hi
  rw [if_pos (by omega)]
  congr 1; omega

theorem poly_of_recurrence {R : Type*} [CommRing R] {u : ℕ → R} (n : ℕ)
    (rec : ∀ j, u (j+n) = ∑ i : Fin n, u (j+i.val)) :
    ∃ b : R[X], PowerSeries.mk u * (denom R n : R⟦X⟧) = (b : R⟦X⟧) := by
  let f := PowerSeries.mk u * (denom R n : R⟦X⟧)
  refine ⟨f.trunc n, PowerSeries.ext fun k => ?_⟩
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with h
  · rfl
  · exact coeff_denom_zero n rec (by omega)

theorem impulse_equation {R : Type*} [CommRing R] {u : ℕ → R} {n : ℕ} (hn : 0 < n)
    (seed : ∀ i < n, u i = if i+1 < n then 0 else 1)
    (rec : ∀ j, u (j+n) = ∑ i : Fin n, u (j+i.val)) :
    PowerSeries.mk u * (denom R n : R⟦X⟧) = PowerSeries.X^(n-1) := by
  ext k
  rw [PowerSeries.coeff_X_pow]
  by_cases hi : k < n
  · rw [coeff_denom, seed k hi]
    have zero : (∑ i ∈ range n, if n-i ≤ k then u (k-(n-i)) else 0) = 0 := by
      apply sum_eq_zero
      intro i h
      have := mem_range.mp h
      split_ifs with le
      · rw [seed _ (by omega), if_pos (by omega)]
      · rfl
    rw [zero, sub_zero]
    split_ifs <;> first | rfl | omega
  · rw [coeff_denom_zero n rec (by omega), if_neg (by omega)]

end Multinacci

namespace Multinacci
open OMA.S_oeis_a210456 Polynomial

theorem actual_period_iff {n p : ℕ} (hn : 0 < n) :
    IsEventualPeriod n p ↔ denom (ZMod 9) n ∣ 1-X^p := by
  rw [period_iff_residues hn]
  let u (k : ℕ) : ZMod 9 := seqN n k
  have hseed (i : ℕ) (hi : i < n) : u i = if i+1 < n then 0 else 1 := by
    simp only [u, seed hi]
    split_ifs <;> simp
  have e := impulse_equation hn hseed (recurrence hn)
  simpa [u] using period_iff_denominator n p (n-1) e

theorem period_small {n : ℕ} (hn : n ≤ 1) : a210456 n = 1 := by
  suffices yes : IsEventualPeriod n 1 by
    exact IsLeast.csInf_eq ⟨⟨by decide, yes⟩, fun k (hk : 0 < k ∧ _) => hk.1⟩
  interval_cases n
  · exact ⟨0, fun k _ => by simp [seqN]⟩
  · apply (actual_period_iff (by decide : 0 < 1)).2
    simp [denom]

end Multinacci

namespace Multinacci
open Finset Polynomial
open scoped PowerSeries Matrix

/-- The shift with last row given by the sum is injective over any ring. -/
theorem window_injective {R : Type*} [CommRing R] {n : ℕ} (hn : 0 < n)
    (T : (Fin n → R) → (Fin n → R))
    (next : ∀ v (i : Fin n) (h : i.val+1 < n), T v i = v ⟨i.val+1,h⟩)
    (last : ∀ v, T v ⟨n-1, by omega⟩ = ∑ i, v i) : Function.Injective T := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  intro a b h
  have tail (j : Fin d) : a j.succ = b j.succ := by
    have hi : j.castSucc.val+1 < d+1 := by simp
    have e := congrFun h j.castSucc
    rw [next _ _ hi, next _ _ hi] at e
    have same : (⟨j.castSucc.val+1,hi⟩ : Fin (d+1)) = j.succ := Fin.ext (by simp)
    simpa only [same] using e
  have totals := congrFun h ⟨d,by omega⟩
  have eq : (∑ i, a i) = ∑ i, b i := by simpa [← last] using totals
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at eq
  have tailSum : (∑ j : Fin d, a j.succ) = ∑ j : Fin d, b j.succ := Finset.sum_congr rfl (fun j _ => tail j)
  rw [tailSum] at eq
  exact funext <| Fin.cases (add_right_cancel eq) tail

theorem matrix_period_of_denominator {R : Type*} [CommRing R] {n p : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) R)
    (next : ∀ v (i : Fin n) (h : i.val+1 < n), (A *ᵥ v) i = v ⟨i.val+1,h⟩)
    (last : ∀ v, (A *ᵥ v) ⟨n-1, by omega⟩ = ∑ i, v i)
    (dvd : denom R n ∣ 1-X^p) : A^p=1 := by
  let T (v : Fin n → R) := A *ᵥ v
  have inj := window_injective hn T next last
  apply Matrix.mulVec_injective
  funext v
  have power (k : ℕ) : (A^k) *ᵥ v = T^[k] v := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Function.iterate_succ_apply']
  rw [power, Matrix.one_mulVec]
  let u (k : ℕ) := (T^[k] v) ⟨0,hn⟩
  have head (k i : ℕ) (hi : i < n) : u (k+i) = (T^[k] v) ⟨i,hi⟩ := by
    induction i generalizing k with
    | zero => simp [u]
    | succ i ih =>
      rw [show k+(i+1) = (k+1)+i by omega, ih (k+1) (by omega), Function.iterate_succ_apply']
      exact next _ _ hi
  have hrec (k : ℕ) : u (k+n) = ∑ i : Fin n, u (k+i.val) := by
    have h := head (k+1) (n-1) (by omega)
    rw [show k+1+(n-1)=k+n by omega, Function.iterate_succ_apply'] at h
    change u (k+n) = (A *ᵥ (T^[k] v)) _ at h
    rw [last] at h
    exact h.trans (sum_congr rfl fun i _ => (head k i i.isLt).symm)
  obtain ⟨b,hb⟩ := poly_of_recurrence n hrec
  obtain ⟨t,per⟩ := period_of_denominator n p hb dvd
  apply inj.iterate t
  rw [← Function.iterate_add_apply]
  funext i
  rw [← head (t+p) i.val i.isLt, ← head t i.val i.isLt, show t+p+i.val=t+i.val+p by omega]
  simpa using per (t+i.val) (by omega)

end Multinacci

namespace Multinacci

/-- The transition matrix of the digital-root recurrence, with a column state vector. -/
def shift (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 9) := fun i j =>
  if i.val + 1 = n ∨ j.val = i.val + 1 then 1 else 0

theorem shift_mulVec_next {n : ℕ} (x : Fin n → ZMod 9) (i : Fin n)
    (h : i.val+1 < n) : (shift n).mulVec x i = x ⟨i.val+1,h⟩ := by
  let t : Fin n := ⟨i.val+1,h⟩
  have pick (j : Fin n) : j.val=i.val+1 ↔ j=t := by change j.val=t.val ↔ j=t; exact Fin.ext_iff.symm
  have notlast : i.val+1≠n := by omega
  simp [Matrix.mulVec, dotProduct, shift, notlast, pick, ite_mul, t]

theorem shift_mulVec_last {n : ℕ} (x : Fin n → ZMod 9) (i : Fin n)
    (h : i.val+1=n) : (shift n).mulVec x i = ∑ j, x j := by
  simp [Matrix.mulVec, dotProduct, shift, h]

private def advance (n k : ℕ) : Matrix (Fin n) (Fin n) (ZMod 9) := fun i j =>
  if j.val = i.val + k then 1 else 0

private def stripe (n k : ℕ) : Matrix (Fin n) (Fin n) (ZMod 9) := fun i _ =>
  if i.val + k + 1 = n then 1 else 0

private theorem shift_split (n : ℕ) : shift n = advance n 1 + stripe n 0 := by
  ext i j
  simp only [shift, advance, stripe, Matrix.add_apply, Nat.add_zero]
  by_cases last : i.val + 1 = n
  · simp [last, ne_of_lt j.isLt]
  · simp [last]

private theorem advance_mul (n k h : ℕ) : advance n k * advance n h = advance n (k+h) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases inside : i.val + k < n
  · let t : Fin n := ⟨i.val+k,inside⟩
    have pick (v : Fin n) : v.val=i.val+k ↔ v=t := by change v.val=t.val ↔ v=t; exact Fin.ext_iff.symm
    rw [Finset.sum_eq_single t]
    · simp [advance,t,Nat.add_assoc]
    · intro j _ ne; simp [advance,pick,ne]
    · simp
  · have outside (v : Fin n) : v.val ≠ i.val + k := by have := v.isLt; omega
    have nohit : j.val ≠ i.val + (k+h) := by have := j.isLt; omega
    simp [advance,outside,nohit]

private theorem advance_tail (n k : ℕ) : advance n k * stripe n 0 = stripe n k := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases inside : i.val + k < n
  · let t : Fin n := ⟨i.val+k,inside⟩
    have pick (v : Fin n) : v.val=i.val+k ↔ v=t := by change v.val=t.val ↔ v=t; exact Fin.ext_iff.symm
    rw [Finset.sum_eq_single t]
    · simp [advance,stripe,t]
    · intro j _ ne; simp [advance,pick,ne]
    · simp
  · have outside (v : Fin n) : v.val ≠ i.val+k := by have := v.isLt;omega
    have nohit : i.val+k+1≠n := by omega
    simp [advance,stripe,outside,nohit]

private theorem stripe_trace (n k : ℕ) : (stripe n k).trace = if k < n then 1 else 0 := by
  by_cases h : k < n
  · let t : Fin n := ⟨n-(k+1),by omega⟩
    have eq (v : Fin n) : v.val+k+1=n ↔ v=t := by rw [Fin.ext_iff];change _ ↔ v.val=n-(k+1);omega
    simp [Matrix.trace,stripe,eq,h]
  · have never (v : Fin n) : v.val+k+1≠n := by omega
    simp [Matrix.trace,stripe,never,h]

private theorem tail_sq (n : ℕ) : stripe n 0 * stripe n 0 = stripe n 0 := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases last : i.val+1=n
  · have h := stripe_trace n 0
    have positive : 0 < n := by omega
    simpa [stripe,Matrix.trace,last,positive] using h
  · simp [stripe,last]

private theorem advance_trace (n k : ℕ) (hk : 0 < k) : (advance n k).trace = 0 := by
  simp [Matrix.trace,advance,hk.ne']

private theorem cube_trace {n : ℕ} (s u : Matrix (Fin n) (Fin n) (ZMod 9)) :
    ((s+u)^3).trace = (s*s*s).trace + 3*((s*s)*u).trace + 3*(s*(u*u)).trace + (u*u*u).trace := by
  rw [show (s+u)^3 = s*s*s + (s*s)*u + (s*u)*s + u*(s*s) + s*(u*u) + (u*s)*u + (u*u)*s + u*u*u by noncomm_ring]
  simp only [Matrix.trace_add]
  rw [Matrix.trace_mul_comm (s*u) s, ← Matrix.mul_assoc s s u, Matrix.trace_mul_comm u (s*s),
    Matrix.trace_mul_comm (u*s) u, ← Matrix.mul_assoc u u s, Matrix.trace_mul_comm (u*u) s]
  ring

theorem shift_traces (n : ℕ) (hn : 2≤n) :
    (shift n).trace=1 ∧ (shift n ^ 3).trace=if n=2 then 4 else 7 := by
  rw [shift_split,Matrix.trace_add,advance_trace _ _ (by decide),stripe_trace]
  have h1 : 1 < n := by omega
  have h0 : 0 < n := by omega
  refine ⟨by simp [h0],?_⟩
  rw [cube_trace,advance_mul,advance_mul,advance_trace _ _ (by decide),tail_sq,
    advance_tail,advance_tail,tail_sq,stripe_trace,stripe_trace,stripe_trace]
  by_cases e : n=2
  · subst n;decide
  · have gt : 1+1 < n := by omega
    simp [gt,e,h0,h1];decide

theorem shift_trace_ne_cubic (n : ℕ) (hn : 2≤n) : (shift n ^ 3).trace ≠ (shift n).trace := by
  obtain ⟨one,cube⟩ := shift_traces n hn
  rw [one,cube];split <;> decide

end Multinacci

/-
For the matrix Gauss congruences see A. V. Zarelua, Proc. Steklov Inst. Math. 263
(2008), 78–98 (https://doi.org/10.1134/S008154380804007X), and H. Steinlein,
Amer. Math. Monthly 124 (2017), 548–553 (https://doi.org/10.4169/amer.math.monthly.124.6.548).
The proof below certifies the required ninth and third power trace identity directly
using the binary cyclic words in the expansion of (X+Y)^9.
-/

namespace TriTrace

def words : ℕ → List (List Bool)
  | 0 => [[]]
  | k+1 => (words k).map (false :: ·) ++ (words k).map (true :: ·)

/-- Rotate without a remainder operation: a cut at or beyond the end is the identity. -/
def cut (w : List Bool) (i : ℕ) := w.drop i ++ w.take i

def rotations (r : ℕ) (w : List Bool) := (List.range r).map (cut w)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Mat (ι : Type*) := Matrix ι ι (ZMod 9)

def val (X Y : Mat ι) (w : List Bool) : Mat ι := (w.map fun b => if b then Y else X).prod

theorem power_words (X Y : Mat ι) (k : ℕ) :
    ((words k).map (val X Y)).sum = (X+Y)^k := by
  induction k with
  | zero => simp [words,val]
  | succ k ih =>
    simp only [words,List.map_append,List.sum_append,List.map_map]
    change ((words k).map (fun w => X*val X Y w)).sum +
      ((words k).map (fun w => Y*val X Y w)).sum = _
    rw [List.sum_map_mul_left,List.sum_map_mul_left,ih,← add_mul,pow_succ']

theorem trace_words (X Y : Mat ι) (k : ℕ) :
    ((words k).map (fun w => (val X Y w).trace)).sum = ((X+Y)^k).trace := by
  simpa [Matrix.trace_list_sum, List.map_map,Function.comp_def] using
    congrArg Matrix.trace (power_words X Y k)

theorem cut_trace (X Y : Mat ι) (w : List Bool) (i : ℕ) :
    (val X Y (cut w i)).trace = (val X Y w).trace := by
  have e := congrArg (fun a => (val X Y a).trace) (List.take_append_drop i w)
  unfold cut val at *
  simp only [List.map_append,List.prod_append] at *
  rw [Matrix.trace_mul_comm]
  exact e

theorem rotations_sum (X Y : Mat ι) (r : ℕ) (w : List Bool) :
    ((rotations r w).map (fun v => (val X Y v).trace)).sum = (r : ZMod 9)*(val X Y w).trace := by
  simp only [rotations,List.map_map,Function.comp_def,cut_trace]
  change (((List.range r).map (Function.const ℕ (val X Y w).trace)).sum : ZMod 9) = _
  simp only [List.map_const,List.length_range,List.sum_replicate,nsmul_eq_mul]

theorem full_rotations_zero (X Y : Mat ι) (ws : List (List Bool)) :
    ((ws.flatMap (rotations 9)).map (fun v => (val X Y v).trace)).sum = 0 := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    simp only [List.flatMap_cons,List.map_append,List.sum_append,ih,rotations_sum]
    change (0 : ZMod 9)*_ + 0 = 0
    simp

end TriTrace

namespace TriTrace

def mixedA : List Bool := [false,false,true]
def mixedB : List Bool := [false,true,true]
def threefold (w : List Bool) := w ++ w ++ w

private def bits (n : ℕ) := (List.range 9).map n.testBit

/-- One encoded representative for every full rotation class of binary words of length nine. -/
private def representatives : List (List Bool) :=
  ([1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 35, 37, 39, 41, 43, 45, 47, 51, 53, 55, 57, 59, 61, 63, 75, 77, 79, 83, 85, 87, 91, 93, 95, 103, 107, 109, 111, 117, 119, 123, 125, 127, 171, 175, 183, 187, 191, 223, 239, 255] : List ℕ).map bits

def grouped3 : List (List Bool) :=
  [List.replicate 3 false,List.replicate 3 true] ++ rotations 3 mixedA ++ rotations 3 mixedB

def grouped9 : List (List Bool) :=
  [List.replicate 9 false,List.replicate 9 true] ++ rotations 3 (threefold mixedA) ++
    rotations 3 (threefold mixedB) ++ representatives.flatMap (rotations 9)

private def digit (i : ℕ) (w : List Bool) := w[i]?.getD false

private def radix : ℕ → List (List Bool) → List (List Bool)
  | 0, ws => ws
  | i+1, ws => radix i (ws.filter (digit i)) ++ radix i (ws.filter fun w => !digit i w)

private theorem split_perm {α : Type*} (f : α → Bool) (xs : List α) :
    (xs.filter f ++ xs.filter (fun x => !f x)).Perm xs := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases h : f a with
    | false => simpa [h] using (List.perm_middle.trans (ih.cons a))
    | true => simpa [h] using ih.cons a

private theorem radix_perm (i : ℕ) (ws : List (List Bool)) : (radix i ws).Perm ws := by
  induction i generalizing ws with
  | zero => exact .refl _
  | succ i ih => exact ((ih _).append (ih _)).trans (split_perm _ _)

private theorem perm_of_sort (i : ℕ) {u v : List (List Bool)}
    (eq : radix i u = radix i v) : u.Perm v := by
  apply (radix_perm i u).symm.trans
  rw [eq]
  exact radix_perm i v

theorem group3 : (words 3).Perm grouped3 := perm_of_sort 3 (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem group9 : (words 9).Perm grouped9 := perm_of_sort 9 (by decide +kernel)

theorem value_replicate {ι : Type*} [Fintype ι] [DecidableEq ι] (X Y : Mat ι)
    (b : Bool) (n : ℕ) : val X Y (List.replicate n b) = (if b then Y else X)^n := by
  simp [val]

theorem value_threefold {ι : Type*} [Fintype ι] [DecidableEq ι] (X Y : Mat ι)
    (w : List Bool) : val X Y (threefold w) = (val X Y w)^3 := by
  unfold val threefold
  simp only [List.map_append,List.prod_append]
  rw [pow_succ,pow_two]

theorem cube_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] (X Y : Mat ι) :
    ((X+Y)^3).trace = (X^3).trace+(Y^3).trace+
      3*(val X Y mixedA).trace+3*(val X Y mixedB).trace := by
  rw [← trace_words]
  rw [(group3.map _).sum_eq]
  simp only [grouped3,List.map_append,List.sum_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,value_replicate,rotations_sum]
  rfl

theorem ninth_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] (X Y : Mat ι) :
    ((X+Y)^9).trace = (X^9).trace+(Y^9).trace+
      3*((val X Y mixedA)^3).trace+3*((val X Y mixedB)^3).trace := by
  rw [← trace_words]
  rw [(group9.map _).sum_eq]
  simp only [grouped9,List.map_append,List.sum_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,value_replicate,rotations_sum,value_threefold,full_rotations_zero]
  rfl

end TriTrace

namespace A210456

/-- Reduction modulo three commutes with matrix powers and trace. Equality
after this reduction gives equality after multiplication by three modulo nine. -/
theorem triple_trace_cube {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (ZMod 9)) : 3*(M^3).trace = 3*M.trace := by
  let f : ZMod 9 →+* ZMod 3 := ZMod.castHom (by decide : 3 ∣ 9) (ZMod 3)
  have lift : ∀ x y : ZMod 9, f x = f y → 3*x = 3*y := by decide +kernel
  apply lift
  rw [AddMonoidHom.map_trace f, AddMonoidHom.map_trace f, Matrix.map_pow,
      ZMod.trace_pow_card]
  exact ZMod.pow_card _

end A210456

namespace A210456Trace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def traceGap (A : Matrix ι ι (ZMod 9)) : ZMod 9 := (A^9).trace - (A^3).trace

private theorem gap_single (i j : ι) (a : ZMod 9) : traceGap (Matrix.single i j a) = 0 := by
  by_cases same : i=j
  · subst j
    have diag_pow (k : ℕ) : (Matrix.single i i a)^(k+1) = Matrix.single i i (a^(k+1)) := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ _ (k+1),ih,Matrix.single_mul_single_same,pow_succ a (k+1)]
    have scalar : ∀ z : ZMod 9, z^9=z^3 := by decide
    simp only [traceGap,diag_pow 8,diag_pow 2,Matrix.trace_single_eq_same,scalar,sub_self]
  · have square : (Matrix.single i j a)^2 = 0 := by
      rw [pow_two,Matrix.single_mul_single_of_ne a i j i (Ne.symm same) a]
    have vanish (k : ℕ) : (Matrix.single i j a)^(2+k)=0 := by rw [pow_add,square,zero_mul]
    simp only [traceGap,vanish 7,vanish 1,sub_self]

theorem traceGap_zero
    (add : ∀ A B : Matrix ι ι (ZMod 9), traceGap (A+B) = traceGap A + traceGap B)
    (A : Matrix ι ι (ZMod 9)) : traceGap A = 0 := by
  let H : Matrix ι ι (ZMod 9) →+ ZMod 9 :=
    { toFun := traceGap
      map_zero' := by simp [traceGap]
      map_add' := add }
  change H A = 0
  rw [Matrix.matrix_eq_sum_single A, map_sum]
  simp only [map_sum]
  have h (i j : ι) : H (Matrix.single i j (A i j)) = 0 := gap_single i j (A i j)
  simp [h]

/-- Cubing acts bijectively on the cyclic group generated by A when the given
order is coprime to three. Apply the ninth-to-third trace identity to a cube root. -/
theorem trace_order
    (add : ∀ A B : Matrix ι ι (ZMod 9), traceGap (A+B) = traceGap A + traceGap B)
    (A : Matrix ι ι (ZMod 9)) (m : ℕ) (_hm : 0 < m) (hc : ¬ 3 ∣ m) (period : A ^ m = 1) :
    (A^3).trace = A.trace := by
  have lift : ∃ B : Matrix ι ι (ZMod 9), B^3=A := by
    by_cases one : m%3=1
    · refine ⟨A^((2*m+1)/3),?_⟩
      rw [←pow_mul, show (2*m+1)/3*3=2*m+1 by omega,
        pow_succ,Nat.mul_comm 2 m,pow_mul,period,one_pow,one_mul]
    · refine ⟨A^((m+1)/3),?_⟩
      rw [←pow_mul, show (m+1)/3*3=m+1 by omega, pow_succ,period,one_mul]
  obtain ⟨B,hB⟩ := lift
  have h := traceGap_zero add B
  change (B^(3*3)).trace-(B^3).trace=0 at h
  rw [pow_mul,hB,sub_eq_zero] at h
  exact h

end A210456Trace

namespace A210456Trace

theorem gap_add {ι : Type*} [Fintype ι] [DecidableEq ι] (X Y : Matrix ι ι (ZMod 9)) :
    traceGap (X+Y) = traceGap X + traceGap Y := by
  unfold traceGap
  rw [TriTrace.ninth_expansion,TriTrace.cube_expansion,
    A210456.triple_trace_cube,A210456.triple_trace_cube]
  abel

/-- The p=3, exponent-2 instance of the matrix Gauss congruences. -/
theorem trace_ninth_eq_cube {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι (ZMod 9)) :
    (A^9).trace = (A^3).trace :=
  sub_eq_zero.mp (traceGap_zero gap_add A)

/-- A matrix over ℤ/9ℤ whose order divides a positive integer coprime to 3
has the same trace as its cube. -/
theorem trace_order_coprime {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (ZMod 9)) (m : ℕ) (hm : 0 < m) (hc : ¬3 ∣ m) (period : A ^ m = 1) :
    (A^3).trace = A.trace := trace_order gap_add A m hm hc period

end A210456Trace

namespace Quadratic210456

/-- Solve simultaneously `u+σ(u)=-1` and `zu+σ(zu)=-1`. -/
theorem ratio_on_trace_line {K : Type*} [Field K] (σ : K →+* K)
    (invol : ∀ x, σ (σ x) = x) (z : K) (hz : σ z ≠ z) :
    ∃ u : K, u ≠ 0 ∧ u + σ u = -1 ∧ z * u + σ (z * u) = -1 := by
  have den : z - σ z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have num : σ z - 1 ≠ 0 := by
    intro h
    have e := congrArg σ (sub_eq_zero.mp h)
    exact hz ((sub_eq_zero.mp h).trans (by simpa only [invol, map_one] using e.symm))
  refine ⟨(σ z-1)/(z-σ z), div_ne_zero num den, ?_, ?_⟩
  all_goals simp only [map_div₀, map_mul, map_sub, map_one, invol]
  all_goals field_simp [den, sub_ne_zero.mpr hz]
  all_goals ring

/-- A quotient-closed property on the affine trace line holds throughout the multiplicative group. -/
theorem trace_generates {K : Type*} [Field K] (σ : K →+* K)
    (invol : ∀ x, σ (σ x) = x) (nontriv : ∃ t, σ t ≠ t)
    (P : K → Prop) (quot : ∀ a b, P a → P b → P (a/b))
    (on_trace : ∀ x, x + σ x = -1 → P x) (x : K) (hx : x ≠ 0) : P x := by
  have outside (z : K) (hz : σ z ≠ z) : P z := by
    obtain ⟨u,hu,tu,tzu⟩ := ratio_on_trace_line σ invol z hz
    simpa [hu] using quot (z*u) u (on_trace _ tzu) (on_trace _ tu)
  by_cases fixed : σ x = x
  · obtain ⟨t, ht⟩ := nontriv
    have nt : t ≠ 0 := fun e => ht (by simp [e])
    have hxt : σ (x*t) ≠ x*t := by
      rw [map_mul, fixed]
      exact fun eq => ht (mul_left_cancel₀ hx eq)
    simpa [nt] using quot (x*t) t (outside _ hxt) (outside _ ht)
  · exact outside x fixed

theorem trace_roots_detect_exponent {K : Type*} [Field K] (σ : K →+* K)
    (invol : ∀ x, σ (σ x) = x) (nontriv : ∃ t, σ t ≠ t) (p : ℕ)
    (roots : ∀ x, x + σ x = -1 → x ^ p = 1) (x : K) (hx : x ≠ 0) : x^p=1 :=
  trace_generates σ invol nontriv (fun z => z^p=1)
    (fun a b ha hb => by rw [div_pow,ha,hb,div_one]) roots x hx

end Quadratic210456

namespace Quadratic210456

/-- A common exponent of all nonzero field elements is divisible by the multiplicative order. -/
theorem all_exponents {K : Type*} [Field K] [Finite K] {p : ℕ}
    (all : ∀ x : K, x ≠ 0 → x^p = 1) : Nat.card K - 1 ∣ p := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [← Nat.card_units, ← hg, orderOf_dvd_iff_pow_eq_one]
  exact Units.ext (by simpa using all (g : K) g.ne_zero)

theorem frobenius_data (k : ℕ) (hk : 0 < k) :
    let K := GaloisField 3 (2*k)
    let σ := iterateFrobenius K 3 k
    (∀ x, σ (σ x) = x) ∧ ∃ t, σ t ≠ t := by
  classical
  let K := GaloisField 3 (2*k)
  let : Fintype K := Fintype.ofFinite K
  have hcard : Nat.card K = 3^(2*k) := GaloisField.card 3 _ (by omega)
  have hq : 1 < 3^k := one_lt_pow₀ (by decide) (Nat.ne_of_gt hk)
  have hpow : 3^k * 3^k = 3^(2*k) := by rw [two_mul, pow_add]
  constructor
  · intro x
    change (x^(3^k))^(3^k)=x
    rw [← pow_mul, hpow, ← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  · by_contra! h
    have exp : Nat.card K - 1 ∣ 3^k-1 := by
      apply all_exponents
      intro x hx
      have f := h x
      change x^(3^k)=x at f
      rw [show (3:ℕ)^k = (3^k-1)+1 by omega, pow_succ] at f
      exact mul_right_cancel₀ hx (by simpa using f : x^(3^k-1)*x=1*x)
    rw [hcard, ← hpow] at exp
    have small := Nat.le_of_dvd (by omega : 0 < 3^k-1) exp
    nlinarith [Nat.sub_add_cancel (by omega : 1≤3^k), Nat.sub_add_cancel (by nlinarith : 1 ≤ 3^k*3^k)]

/-- The affine trace line detects the exact multiplicative order of the quadratic field. -/
theorem root_exponent_dvd (k p : ℕ) (hk : 0 < k)
    (roots : ∀ x : GaloisField 3 (2*k), x+x^(3^k) = -1 → x^p=1) : 3^(2*k)-1 ∣ p := by
  obtain ⟨invol,moved⟩ := frobenius_data k hk
  rw [← GaloisField.card 3 (2*k) (by omega)]
  exact all_exponents (trace_roots_detect_exponent (iterateFrobenius _ 3 k) invol moved p roots)

end Quadratic210456

namespace Quadratic210456
open Polynomial

private theorem factor_ne_zero : (X-1 : (ZMod 3)[X]) ≠ 0 := by
  simpa only [C_1] using (monic_X_sub_C (1 : ZMod 3)).ne_zero

private theorem factor_at_one (q : ℕ) :
    (X - 1 : (ZMod 3)[X]) ∣ X^q + X + 1 := by
  rw [← C_1, dvd_iff_isRoot]
  change (X ^ q + X + 1 : (ZMod 3)[X]).eval 1 = 0
  simp only [eval_add,eval_pow,eval_X,one_pow,eval_one]
  decide

/-- Removing the root `1` from the trace polynomial does not affect the universal exponent. -/
theorem exponent_of_dvd (k p : ℕ) (hk : 0 < k)
    (h : (X^(3^k) + X + 1) / (X-1 : (ZMod 3)[X]) ∣ X^p-1) : 3^(2*k)-1 ∣ p := by
  apply root_exponent_dvd k p hk
  intro x root
  by_cases one : x=1
  · simp [one]
  let ev := aeval (R := ZMod 3) x
  have hx : ev (X-1) ≠ 0 := by simpa [ev] using sub_ne_zero.mpr one
  have whole : ev (X^(3^k)+X+1) = 0 := by
    simp only [map_add, map_pow, aeval_X, map_one, ev]
    rw [add_comm (x^(3^k)) x, root, neg_add_cancel]
  let f := (X^(3^k)+X+1) / (X-1 : (ZMod 3)[X])
  have restore : (X-1) * f = X^(3^k)+X+1 := EuclideanDomain.mul_div_cancel' factor_ne_zero (factor_at_one _)
  have zero : ev f = 0 := by
    have eq := congrArg ev restore
    exact (mul_eq_zero.mp (by simpa only [map_mul,whole] using eq)).resolve_left hx
  obtain ⟨w, hw⟩ := h
  change X^p-1 = f*w at hw
  have hpow := congrArg ev hw
  rw [map_sub,map_pow,map_one,map_mul,zero,zero_mul] at hpow
  simpa [ev] using sub_eq_zero.mp hpow

/-- The identity `g^q-g = X^(q*q)-X` gives the reverse divisibility without counting roots. -/
theorem full_trace_dvd (k : ℕ) :
    (X^(3^k)+X+1 : (ZMod 3)[X]) ∣ X^(3^(2*k)-1) - 1 := by
  let q := 3^k
  let g : (ZMod 3)[X] := X^q+X+1
  have pos : 0 < q := Nat.pow_pos (by decide)
  have pos2 : 0 < q*q := Nat.mul_pos pos pos
  have cop : IsCoprime g X := by
    refine ⟨1, -(X^(q-1)+1), ?_⟩
    dsimp only [g]
    conv_lhs => lhs; rhs; lhs; lhs; rw [show q = q-1+1 by omega,pow_succ]
    ring
  have power : g^q = X^(q*q)+X^q+1 := by
    change iterateFrobenius ((ZMod 3)[X]) 3 k (X^q+X+1) = _
    rw [map_add,map_add,map_one,iterateFrobenius_def,iterateFrobenius_def,← pow_mul]
  have multiple : g ∣ g^q-g := dvd_sub (dvd_pow_self g pos.ne') (dvd_refl g)
  have value : g^q-g = X*(X^(q*q-1)-1) := by
    rw [power]
    dsimp only [g]
    conv_lhs => lhs; lhs; lhs; rw [show q*q = q*q-1+1 by omega, pow_succ]
    ring
  rw [value] at multiple
  simpa only [two_mul,pow_add,q] using cop.dvd_of_dvd_mul_left multiple

theorem quadratic_trace_iff (k p : ℕ) (hk : 0 < k) :
    (X^(3^k)+X+1)/(X-1 : (ZMod 3)[X]) ∣ X^p-1 ↔ 3^(2*k)-1 ∣ p := by
  refine ⟨exponent_of_dvd k p hk, fun h => ?_⟩
  have restore := EuclideanDomain.mul_div_cancel' factor_ne_zero (factor_at_one (3^k))
  exact (Dvd.intro_left _ restore).trans ((full_trace_dvd k).trans (dvd_pow_sub_one_of_dvd h))

end Quadratic210456

namespace A210456Cubic

open Polynomial

noncomputable def cubicNumerator (q : ℕ) : (ZMod 3)[X] := X^(q+1) + X + 1

noncomputable def cubicQuotient (q : ℕ) : (ZMod 3)[X] := cubicNumerator q / (X-1)

theorem cubic_factor (q : ℕ) :
    (X-1) * cubicQuotient q = cubicNumerator q := by
  apply EuclideanDomain.mul_div_cancel'
  · simpa only [Polynomial.C_1] using (Polynomial.X_sub_C_ne_zero (1 : ZMod 3))
  · rw [← Polynomial.C_1,Polynomial.dvd_iff_isRoot]
    change (cubicNumerator q).eval 1 = 0
    simp [cubicNumerator]
    decide

theorem eq_cubicQuotient_of_factor {q : ℕ} {P : (ZMod 3)[X]}
    (h : (X-1)*P = cubicNumerator q) : P = cubicQuotient q := by
  have hn : (X : (ZMod 3)[X])-1 ≠ 0 := by
    simpa only [Polynomial.C_1] using (Polynomial.X_sub_C_ne_zero (1 : ZMod 3))
  exact mul_left_cancel₀ hn (h.trans (cubic_factor q).symm)

/-- In characteristic three, X times the q-th Frobenius power of the
numerator minus the numerator is X raised to the norm exponent minus one. -/
theorem cubic_frobenius_identity (k : ℕ) :
    let q := 3^k
    X * (cubicNumerator q)^q - cubicNumerator q = (X : (ZMod 3)[X])^(q^2+q+1)-1 := by
  dsimp only
  let q := 3^k
  have fr : (cubicNumerator q)^q = ((X : (ZMod 3)[X])^(q+1))^q + X^q + 1 := by
    simp only [cubicNumerator,q,add_pow_char_pow _ _ 3 k,one_pow]
  have lead : (X : (ZMod 3)[X])^(q^2+q+1) = X * (X^(q+1))^q := by
    rw [show q^2+q+1 = (q+1)*q+1 by ring, pow_succ' X ((q+1)*q), pow_mul]
  change _ = (X : (ZMod 3)[X])^(q^2+q+1)-1
  rw [lead,fr,cubicNumerator,pow_succ' X q]
  ring

theorem cubic_norm_dvd (k : ℕ) :
    cubicQuotient (3^k) ∣ (X : (ZMod 3)[X])^((3^k)^2+3^k+1)-1 := by
  let q := 3^k
  have pos : q ≠ 0 := pow_ne_zero _ (by decide)
  have qn : cubicQuotient q ∣ cubicNumerator q := cubic_factor q ▸ dvd_mul_left _ _
  rw [← cubic_frobenius_identity]
  exact dvd_sub (dvd_mul_of_dvd_right (qn.trans (dvd_pow_self _ pos)) _) qn

/-- A trace-zero element gives a root of the numerator after raising it to
q−1. Any divisor certificate for the quotient forces that root to have period p. -/
theorem trace_power_one {K : Type*} [Field K] [Algebra (ZMod 3) K]
    {q p : ℕ} (hq : 0 < q) (period : cubicQuotient q ∣ (X : (ZMod 3)[X])^p-1)
    {t : K} (ht : t ≠ 0) (trace : t+t^q+t^(q^2)=0) :
    (t^(q-1))^p = 1 := by
  let a := t^(q-1)
  change a^p = 1
  by_cases trivial : a=1
  · simp [trivial]
  have e : (q-1)*(q+1)+1 = q^2 := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
    simp only [Nat.succ_sub_one,Nat.succ_eq_add_one]
    ring
  have e' : q-1+1=q := by omega
  have h1 : t*a^(q+1) = t^(q^2) := by rw [show a = t^(q-1) from rfl,←pow_mul,←pow_succ',e]
  have h2 : t*a = t^q := by rw [show a = t^(q-1) from rfl,←pow_succ',e']
  have vanish : a^(q+1)+a+1=0 := by
    apply (mul_eq_zero.mp (show t*(a^(q+1)+a+1)=0 by
      rw [mul_add,mul_add,mul_one,h1,h2]
      simpa only [add_comm,add_left_comm,add_assoc] using trace)).resolve_left ht
  have factors := congrArg (aeval (R:=ZMod 3) a) (cubic_factor q)
  simp only [map_mul,map_sub,aeval_X,map_one,cubicNumerator,map_add,map_pow,vanish] at factors
  have root := (mul_eq_zero.mp factors).resolve_left (sub_ne_zero.mpr trivial)
  obtain ⟨s,hs⟩ := period
  have hp := congrArg (aeval (R:=ZMod 3) a) hs
  simpa only [map_sub,map_pow,aeval_X,map_one,map_mul,root,zero_mul,sub_eq_zero] using hp

end A210456Cubic

namespace A210456Cubic

/-- Multiplicative quotients of two trace-zero elements detect all norm-one orders. -/
theorem trace_forces_order {K : Type*} [Field K] [Fintype K] {q p : ℕ}
    (hq : 1 < q) (card : Fintype.card K = q ^ 3)
    (subpow : ∀ x y : K, (x-y)^q = x^q-y^q)
    (period : ∀ t : K, t ≠ 0 → t+t^q+t^(q^2) = 0 → (t^(q-1))^p = 1) :
    q^2+q+1 ∣ p := by
  have cycle (z : K) : (z^(q^2))^q = z := by
    rw [← pow_mul, ← pow_succ, ← card, FiniteField.pow_card]
  have sq (z : K) : (z^q)^q = z^(q^2) := by rw [← pow_mul, pow_two]
  have each (z : K) (hz : z ≠ 0) : z^((q-1)*p) = 1 := by
    let t : K := z^q - z^(q^2)
    have next : t^q = z^(q^2)-z := by
      dsimp [t]
      rw [subpow, sq, cycle]
    by_cases ht : t = 0
    · have e : z^q = z^(q^2) := sub_eq_zero.mp ht
      have e' : z^(q^2) = z := by simpa only [sq, cycle] using congrArg (· ^ q) e
      have h : z^(q-1)*z = (1:K)*z := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ q), one_mul, e, e']
      rw [pow_mul, (mul_right_cancel₀ hz h), one_pow]
    · have next₂ : t^(q^2) = z-z^q := by
        rw [← sq, next, subpow, cycle]
      have ttrace : t+t^q+t^(q^2) = 0 := by
        rw [next, next₂]
        dsimp [t]
        ring
      have zttrace : z*t+(z*t)^q+(z*t)^(q^2) = 0 := by
        rw [mul_pow, mul_pow, next, next₂]
        dsimp [t]
        ring
      have e := period (z*t) (mul_ne_zero hz ht) zttrace
      rw [mul_pow, mul_pow, period t ht ttrace, mul_one, ← pow_mul] at e
      exact e
  have allUnits (z : Kˣ) : z^((q-1)*p) = 1 := by
    apply Units.ext
    simpa using each (z : K) z.ne_zero
  have divides := (FiniteField.forall_pow_eq_one_iff K ((q-1)*p)).mp allUnits
  rw [card] at divides
  have identity : q^3-1 = (q-1)*(q^2+q+1) := by
    obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    simp only [Nat.succ_sub_one]
    have eq : (u+1)^3 = u*((u+1)^2+(u+1)+1)+1 := by ring
    rw [eq, Nat.add_sub_cancel]
  rw [identity] at divides
  exact Nat.dvd_of_mul_dvd_mul_left (by omega) divides

end A210456Cubic

namespace A210456Cubic

/-- In the cubic field over the q-element field, the trace-zero powers generate
the subgroup of order q²+q+1. -/
theorem cubic_trace_order (k p : ℕ) (hk : 0 < k)
    (period : ∀ t : GaloisField 3 (3*k), t ≠ 0 →
      t + t^(3^k) + t^((3^k)^2) = 0 → (t^(3^k-1))^p = 1) :
    (3^k)^2+3^k+1 ∣ p := by
  let K := GaloisField 3 (3*k)
  let : Fintype K := Fintype.ofFinite K
  apply trace_forces_order (K := K) (by exact one_lt_pow₀ (by decide : 1 < (3:ℕ)) hk.ne')
  · change Fintype.card (GaloisField 3 (3*k)) = _
    rw [← Nat.card_eq_fintype_card, GaloisField.card _ _ (by omega), ← pow_mul, Nat.mul_comm]
  · exact fun x y => sub_pow_char_pow (p := 3) x y k
  · exact period

end A210456Cubic

open Polynomial

namespace A210456Cubic

/-- The least exponent splitting the order polynomial for the cubic case is q²+q+1. -/
theorem cubic_dvd_iff (k p : ℕ) (hk : 0 < k) :
    cubicQuotient (3^k) ∣ X^p-1 ↔ (3^k)^2+3^k+1 ∣ p := by
  constructor
  · intro hd
    exact cubic_trace_order k p hk (fun _ ht htrace => trace_power_one (by positivity) hd ht htrace)
  · rintro ⟨c,rfl⟩
    exact dvd_trans (cubic_norm_dvd k) (by
      rw [pow_mul]
      exact sub_one_dvd_pow_sub_one _ _)

end A210456Cubic

namespace A210456Lift

open Polynomial

def reduce : ZMod 9 →+* ZMod 3 := ZMod.castHom (by decide) (ZMod 3)

theorem reduce_poly_surjective : Function.Surjective (Polynomial.map reduce) :=
  Polynomial.map_surjective reduce (ZMod.castHom_surjective (by decide : 3 ∣ 9))

private def third (a : ZMod 9) : ZMod 9 := ((a.val / 3 : ℕ) : ZMod 9)

private theorem triple (a : ZMod 9) (h : reduce a = 0) : a = 3*third a := by
  have check : ∀ z : ZMod 9, reduce z = 0 → z = 3*third z := by decide
  exact check a h

/-- A polynomial that reduces to zero modulo three has all coefficients
in the ideal generated by three in ZMod 9. -/
theorem error_multiple {P : (ZMod 9)[X]} (h : P.map reduce = 0) :
    ∃ E : (ZMod 9)[X], P = 3*E := by
  refine ⟨P.sum (fun n a => monomial n (third a)),?_⟩
  calc
    P = P.sum (fun n a => monomial n a) := P.sum_monomial_eq.symm
    _ = 3*P.sum (fun n a => monomial n (third a)) := by
      unfold Polynomial.sum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      have hc := congrArg (fun Q : (ZMod 3)[X] => Q.coeff n) h
      simp only [coeff_map,coeff_zero] at hc
      rw [show (3 : (ZMod 9)[X]) = C (3 : ZMod 9) by exact (C_ofNat 3).symm, C_mul_monomial, ←triple _ hc]

end A210456Lift

namespace A210456Lift

open Polynomial

/-- Cubing any element of 1 + 3R gives 1 in characteristic nine. -/
theorem cube_one_sub_three {R : Type*} [CommRing R] [CharP R 9] (e : R) :
    (1-3*e)^3 = 1 := by
  calc
    _ = 1 + 9*(-e + 3*e^2 - 3*e^3) := by ring
    _ = 1 := by
      have h : (9 : R) = 0 := CharP.cast_eq_zero R 9
      rw [h,zero_mul,add_zero]

/-- A polynomial period modulo three lifts after multiplying its exponent by three. -/
theorem cube_period_of_decomposition {R : Type*} [CommRing R] [CharP R 9]
    {P g h e : R} (decomp : 1-g-P*h=3*e) : P ∣ 1-g^3 := by
  have rem : P ∣ (1-3*e)-g := by
    refine ⟨h,?_⟩
    rw [←decomp]
    ring
  simpa only [cube_one_sub_three] using
    (rem.trans (sub_dvd_pow_sub_pow (1-3*e) g 3))

end A210456Lift

namespace A210456Lift

open Polynomial

/-- Cubing restores a divisibility relation lifted from characteristic three. -/
theorem lift_period (P : (ZMod 9)[X]) (m : ℕ)
    (hd : P.map reduce ∣ 1-(X : (ZMod 3)[X])^m) :
    P ∣ 1-(X : (ZMod 9)[X])^(3*m) := by
  obtain ⟨h,hh⟩ := hd
  obtain ⟨H, hH⟩ := reduce_poly_surjective h
  have vanish : (1-(X : (ZMod 9)[X])^m-P*H).map reduce = 0 := by
    simp only [Polynomial.map_sub,Polynomial.map_one,Polynomial.map_pow,Polynomial.map_X,
      Polynomial.map_mul,hH,hh,sub_self]
  obtain ⟨E, hE⟩ := error_multiple vanish
  rw [Nat.mul_comm,pow_mul]
  exact cube_period_of_decomposition hE

/-- A period in characteristic nine remains a period in characteristic three. -/
theorem reduce_period (P : (ZMod 9)[X]) (m : ℕ)
    (hd : P ∣ 1-(X : (ZMod 9)[X])^m) :
    P.map reduce ∣ 1-(X : (ZMod 3)[X])^m := by
  simpa using (map_dvd (Polynomial.mapRingHom reduce) hd)

end A210456Lift

namespace A210456Lift

open Polynomial

/-- If the characteristic-three denominator has exact order e prime to three,
and every true period is divisible by three, its lifted least positive period is 3e. -/
theorem least_of_dvd {period : ℕ → Prop} (P : (ZMod 9)[X]) (e : ℕ)
    (epos : 0 < e) (cop : Nat.Coprime 3 e)
    (characterize : ∀ m, period m ↔ P ∣ 1-(X : (ZMod 9)[X])^m)
    (mod3 : ∀ m, P.map reduce ∣ 1-(X : (ZMod 3)[X])^m ↔ e ∣ m)
    (three : ∀ m, period m → 3 ∣ m) :
    sInf {m | 0 < m ∧ period m} = 3*e := by
  have yes : period (3*e) :=
    (characterize _).mpr (lift_period P e ((mod3 e).mpr dvd_rfl))
  have bound (m : ℕ) (hm : 0 < m ∧ period m) : 3*e ≤ m := by
    have h := (mod3 m).mp (reduce_period P m ((characterize m).mp hm.2))
    exact Nat.le_of_dvd hm.1 (cop.mul_dvd_of_dvd_of_dvd (three m hm.2) h)
  exact IsLeast.csInf_eq ⟨⟨by omega,yes⟩,fun m hm => bound m hm⟩

end A210456Lift

namespace A210456Lift

open Multinacci Polynomial Finset

theorem denom_mod (n : ℕ) : (denom (ZMod 9) n).map reduce = denom (ZMod 3) n := by
  simp [denom, Polynomial.map_sum]

/-- Multiplying the negative recurrence denominator by X−1 uncovers a trinomial. -/
theorem denom_factor (n : ℕ) :
    ((X-1)*(-denom (ZMod 3) n) : (ZMod 3)[X]) = X^(n+1)+X+1 := by
  let x : (ZMod 3)[X] := X
  change (x-1)*-(1-x*∑ i ∈ range n, x^i) = x^(n+1)+x+1
  have three : (3 : (ZMod 3)[X]) = 0 := CharP.cast_eq_zero _ 3
  calc
    _ = x*((∑ i ∈ range n, x^i)*(x-1)) - x + 1 := by ring
    _ = x^(n+1)+x+1 - 3*x := by rw [geom_sum_mul, pow_succ]; ring
    _ = _ := by rw [three,zero_mul,sub_zero]

theorem denom_cubic (k p : ℕ) (hk : 0 < k) :
    denom (ZMod 3) (3^k) ∣ 1-X^p ↔ (3^k)^2+3^k+1 ∣ p := by
  have e := A210456Cubic.eq_cubicQuotient_of_factor (denom_factor (3^k))
  rw [← A210456Cubic.cubic_dvd_iff k p hk, ←e]
  rw [show (X : (ZMod 3)[X])^p-1 = -(1-X^p) by ring, neg_dvd, dvd_neg]

theorem denom_quadratic (k p : ℕ) (hk : 0 < k) :
    denom (ZMod 3) (3^k-1) ∣ 1-X^p ↔ 3^(2*k)-1 ∣ p := by
  have factor := denom_factor (3^k-1)
  have qpos : 0 < (3:ℕ)^k := by positivity
  rw [Nat.sub_add_cancel (by omega : 1 ≤ 3^k)] at factor
  have e : ((X^(3^k)+X+1)/(X-1 : (ZMod 3)[X])) = -denom (ZMod 3) (3^k-1) := by
    have hn : (X-1 : (ZMod 3)[X]) ≠ 0 := by
      simpa only [Polynomial.C_1] using (Polynomial.X_sub_C_ne_zero (1 : ZMod 3))
    apply mul_left_cancel₀ hn
    rw [EuclideanDomain.mul_div_cancel' hn ⟨_,factor.symm⟩,factor]
  rw [← Quadratic210456.quadratic_trace_iff k p hk,e]
  rw [show (X : (ZMod 3)[X])^p-1 = -(1-X^p) by ring, neg_dvd, dvd_neg]

end A210456Lift

namespace A210456Lift

open Multinacci Polynomial

/-- The characteristic-three quadratic order and a compulsory factor of three
determine the exact least period of width 3^k−1 over ZMod 9. -/
theorem least_quadratic {period : ℕ → Prop} (k : ℕ) (hk : 0 < k)
    (characterize : ∀ m, period m ↔ denom (ZMod 9) (3^k-1) ∣ 1-(X : (ZMod 9)[X])^m)
    (three : ∀ m, period m → 3 ∣ m) :
    sInf {m | 0 < m ∧ period m} = 3^(2*k+1)-3 := by
  have big : 1 < (3:ℕ)^(2*k) := one_lt_pow₀ (by decide) (by omega)
  have mult : 3 ∣ (3:ℕ)^(2*k) := dvd_pow_self _ (by omega)
  have cop : Nat.Coprime 3 (3^(2*k)-1) :=
    Nat.prime_three.coprime_iff_not_dvd.mpr (by omega)
  have result := least_of_dvd (denom (ZMod 9) (3^k-1)) (3^(2*k)-1)
    (by omega) cop characterize (fun m => by rw [denom_mod]; exact denom_quadratic k m hk) three
  rw [result,pow_succ]
  omega

/-- The norm-one cubic group similarly controls width 3^k. -/
theorem least_cubic {period : ℕ → Prop} (k : ℕ) (hk : 0 < k)
    (characterize : ∀ m, period m ↔ denom (ZMod 9) (3^k) ∣ 1-(X : (ZMod 9)[X])^m)
    (three : ∀ m, period m → 3 ∣ m) :
    sInf {m | 0 < m ∧ period m} = 3^(2*k+1)+3^(k+1)+3 := by
  have mult : 3 ∣ (3:ℕ)^k := dvd_pow_self _ hk.ne'
  have mult2 : 3 ∣ ((3:ℕ)^k)^2 := mult.trans (dvd_pow_self _ (by decide))
  have cop : Nat.Coprime 3 (((3:ℕ)^k)^2+3^k+1) :=
    Nat.prime_three.coprime_iff_not_dvd.mpr (by omega)
  have result := least_of_dvd (denom (ZMod 9) (3^k)) ((3^k)^2+3^k+1)
    (Nat.zero_lt_succ _) cop characterize (fun m => by rw [denom_mod]; exact denom_cubic k m hk) three
  rw [result,pow_succ (3:ℕ) (2*k),pow_succ (3:ℕ) k, Nat.mul_comm 2 k,pow_mul]
  ring

end A210456Lift

namespace Multinacci
open OMA.S_oeis_a210456

theorem period_multiple_of_three {n p : ℕ} (hn : 2 ≤ n) (per : IsEventualPeriod n p) :
    3 ∣ p := by
  by_contra h
  have npos : 0 < n := by omega
  have pos : 0 < p := by
    by_contra! le
    exact h (by simp [show p=0 by omega])
  have power := matrix_period_of_denominator npos (shift n) shift_mulVec_next
    (fun v => shift_mulVec_last v ⟨n-1,by omega⟩ (by simp; omega))
    ((actual_period_iff npos).1 per)
  exact shift_trace_ne_cubic n hn (A210456Trace.trace_order_coprime _ p pos h power)

theorem solution : type_of% @OMA.S_oeis_a210456.main := by
  constructor
  · intro n h
    have hn : 2 ≤ n := by
      by_contra! small
      rw [period_small (by omega : n ≤ 1)] at h
      omega
    have ne : (periodSet n).Nonempty := by
      by_contra! empty
      rw [a210456, empty, Nat.sInf_empty] at h
      omega
    exact period_multiple_of_three hn (Nat.sInf_mem ne).2
  · intro k hk
    have big : 3 ≤ (3:ℕ)^k := by
      simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 3) hk
    constructor
    · exact A210456Lift.least_quadratic k hk (fun p => actual_period_iff (by omega))
        (fun p => period_multiple_of_three (by omega))
    · exact A210456Lift.least_cubic k hk (fun p => actual_period_iff (by omega))
        (fun p => period_multiple_of_three (by omega))

end Multinacci

theorem OMA.solution : type_of% @OMA.S_oeis_a210456.main :=
  Multinacci.solution
