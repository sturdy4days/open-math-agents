import OMAStatements.S_mo_288399
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# A sharp column bound for coordinate deletion

This companion to Observation 2 of [MathOverflow 288399](https://mathoverflow.net/questions/288399)
proves the inequality asked for in the question's final paragraph for every column.
The same equicorrelation matrices that refute the stronger registered conjecture
give equality in the corrected bound.
-/

namespace CorrelationFamily
open Finset OMA.S_mo_288399

noncomputable def equicorrelation (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then 1 else -1 / ((n:ℝ)-1)

private theorem scaled_quad {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    ((n:ℝ)-1) * quad (equicorrelation n) x = n * normSq x - (∑ i, x i)^2 := by
  have hp : (0:ℝ) < n-1 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold quad
  rw [mul_sum]
  calc
    _ = ∑ i, ∑ j, ((if i=j then (n:ℝ)*(x i)^2 else 0) - x i * x j) := by
      refine sum_congr rfl fun i _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      by_cases h : i=j
      · subst j; simp [equicorrelation]; ring
      · simp [equicorrelation,h]
        field_simp
    _ = _ := by
      simp_rw [sum_sub_distrib]
      simp only [sum_ite_eq, mem_univ, if_true, ← mul_sum, ← sum_mul, normSq, pow_two]

/-- The full Rayleigh minimum of the equicorrelation matrix is zero, and each
of its coordinate-deleted Rayleigh minima is exactly 1/(n−1). -/
theorem equicorrelation_least {n : ℕ} (hn : 2 ≤ n) :
    (equicorrelation n).IsSymm ∧ (∀ i, equicorrelation n i i = 1) ∧
      LeastOn (equicorrelation n) (fun _ => True) 0 ∧
      ∀ i, LeastOn (equicorrelation n) (fun x => x i = 0) (1/((n:ℝ)-1)) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hc : (0:ℝ)<n-1 := by linarith
  have restrict (x : Fin n → ℝ) (i : Fin n) (hi : x i = 0) :
      (∑ a, x a)^2 ≤ ((n:ℝ)-1)*normSq x := by
    have er (g : Fin n → ℝ) (hg : g i = 0) : ∑ a ∈ univ.erase i, g a = ∑ a, g a := by
      rw [← sum_erase_add univ g (mem_univ i),hg,add_zero]
    have bound := sq_sum_le_card_mul_sum_sq (s:=univ.erase i) (f:=x)
    rw [er x hi, er (fun a => x a^2) (by simp [hi]), card_erase_of_mem (mem_univ i), card_univ,
      Fintype.card_fin, Nat.cast_sub (by omega : 1≤n)] at bound
    simpa only [Nat.cast_one,normSq] using bound
  refine ⟨?_,fun i => by simp [equicorrelation],⟨?_,?_⟩,?_⟩
  · ext i j
    simp only [Matrix.transpose_apply,equicorrelation,eq_comm]
  · intro x _
    rw [zero_mul]
    have bound := sq_sum_le_card_mul_sum_sq (s:=univ) (f:=x)
    simp only [card_univ,Fintype.card_fin] at bound
    apply nonneg_of_mul_nonneg_right _ hc
    rw [scaled_quad hn]
    exact sub_nonneg.mpr bound
  · refine ⟨fun _ => 1,trivial,?_,?_⟩
    · simp only [normSq,one_pow,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
      linarith
    · apply (mul_right_inj' hc.ne').mp
      rw [scaled_quad hn]
      simp [normSq,pow_two]
  · intro i
    refine ⟨?_,?_⟩
    · intro x hx
      apply (mul_le_mul_iff_right₀ hc).mp
      rw [scaled_quad hn]
      have c : ((n:ℝ)-1)*(1/((n:ℝ)-1)*normSq x) = normSq x := by field_simp
      rw [c]
      linarith [restrict x i hx]
    · let x : Fin n → ℝ := fun j => if j=i then 0 else 1
      have xi : x i = 0 := by simp [x]
      have summ (g : Fin n → ℝ) (hi : g i = 0) (h : ∀ j, j≠i → g j=1) :
          ∑ j,g j = (n:ℝ)-1 := by
        rw [← sum_erase_add univ g (mem_univ i),hi,add_zero]
        calc
          _ = ∑ _j ∈ (univ : Finset (Fin n)).erase i, (1:ℝ) :=
            sum_congr rfl fun j hj => h j (mem_erase.mp hj).1
          _ = _ := by simp [card_erase_of_mem,Nat.cast_sub (by omega : 1≤n)]
      have sx : ∑ j,x j = (n:ℝ)-1 := summ x xi (fun j hj => by simp [x,hj])
      have sqx : normSq x = (n:ℝ)-1 := summ (fun j => x j^2) (by simp [xi])
        (fun j hj => by simp [x,hj])
      refine ⟨x,xi,sqx.symm ▸ hc,?_⟩
      apply (mul_right_inj' hc.ne').mp
      rw [scaled_quad hn,sx,sqx,one_div_mul_cancel hc.ne']
      ring

/-- The column norm squared is 1/(n−1). Thus every deletion violates the
proposed bound whenever there are at least three coordinates. -/
theorem column_witness {n : ℕ} (hn : 3 ≤ n) (j : Fin n) :
    (∑ k, if k=j then 0 else (equicorrelation n k j)^2) = 1/((n:ℝ)-1) ∧
      Real.sqrt (∑ k, if k=j then 0 else (equicorrelation n k j)^2) <
        ((n:ℝ)-1) * (1/((n:ℝ)-1) - 0) := by
  have h : (3:ℝ) ≤ n := by exact_mod_cast hn
  have h' : 1 < (n:ℝ)-1 := by linarith
  have c : (0:ℝ) < n-1 := by linarith
  have total : (∑ k, if k=j then 0 else (equicorrelation n k j)^2) = 1/((n:ℝ)-1) := by
    rw [← sum_erase_add univ (fun k => if k=j then 0 else (equicorrelation n k j)^2) (mem_univ j)]
    simp only [ite_true, add_zero]
    calc
      _ = ∑ _k ∈ (univ : Finset (Fin n)).erase j, (-1/((n:ℝ)-1))^2 :=
        sum_congr rfl fun k hk => by simp [equicorrelation,(mem_erase.mp hk).1]
      _ = _ := by
        simp only [sum_const,card_erase_of_mem (mem_univ j),card_univ,Fintype.card_fin,
          nsmul_eq_mul,Nat.cast_sub (by omega : 1≤n), Nat.cast_one]
        field_simp
  refine ⟨total,?_⟩
  rw [total, sub_zero, mul_one_div_cancel c.ne']
  exact (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).mpr (by
    rw [one_pow,div_lt_iff₀ c]
    simpa only [one_mul] using h')

end CorrelationFamily

namespace CorrelationFamily
open OMA.S_mo_288399

/-- The factor `√(n−1)` is attained in every dimension at least three. -/
theorem sharp_factor {n : ℕ} (hn : 3≤n) (j : Fin n) :
    Real.sqrt ((n:ℝ)-1)*(1/((n:ℝ)-1)-0) =
      Real.sqrt (∑ k, if k=j then 0 else (equicorrelation n k j)^2) := by
  have hn' : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < (n:ℝ)-1 := by linarith
  have hs := Real.sq_sqrt hp.le
  have root : 0 < Real.sqrt ((n:ℝ)-1) := Real.sqrt_pos.mpr hp
  rw [(column_witness hn j).1, sub_zero,Real.sqrt_div (by positivity), Real.sqrt_one]
  field_simp
  nlinarith

end CorrelationFamily

open OMA.S_mo_288399

namespace RayleighDeletion

/-- Deleting each coordinate once retains each square in exactly `n - 1` summands. -/
theorem norm_sum {n : ℕ} (x : Fin n → ℝ) :
    (∑ i : Fin n, normSq (fun j => if i = j then 0 else x j)) =
      ((n : ℝ)-1) * normSq x := by
  classical
  have cell (i j : Fin n) : (if i = j then 0 else x j)^2 =
      (x j)^2 - (if i = j then (x j)^2 else 0) := by
    by_cases h : i = j <;> simp [h]
  unfold normSq
  rw [Finset.sum_comm]
  simp_rw [cell, Finset.sum_sub_distrib]
  simp [nsmul_eq_mul, sub_mul, Finset.mul_sum, Finset.sum_sub_distrib]

/-- Each off-diagonal entry appears in `n - 2` deletions, each diagonal entry once more. -/
theorem quad_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (diag : ∀ i, A i i = 1) :
    (∑ i : Fin n, quad A (fun j => if i = j then 0 else x j)) =
      ((n : ℝ)-2) * quad A x + normSq x := by
  classical
  let v (j k : Fin n) := x j * A j k * x k
  have cell (i j k : Fin n) :
      (if i = j then 0 else x j) * A j k * (if i = k then 0 else x k) =
        v j k - (if i = j then v j k else 0) - (if i = k then v j k else 0) +
        (if i = j ∧ j = k then v j k else 0) := by
    by_cases h : i = j <;> by_cases h' : i = k <;> by_cases hh : j = k <;> simp_all [v]
  have coefficient (j k : Fin n) :
      (∑ i : Fin n, (if i = j then 0 else x j) * A j k * (if i = k then 0 else x k)) =
        ((n:ℝ)-2) * v j k + (if j = k then v j k else 0) := by
    simp_rw [cell, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    by_cases h : j = k <;> simp [h, nsmul_eq_mul] <;> ring
  unfold quad
  rw [Finset.sum_comm]
  calc
    _ = ∑ j, ∑ k, ∑ i : Fin n,
        (if i = j then 0 else x j) * A j k * (if i = k then 0 else x k) := by
      apply Finset.sum_congr rfl
      intro _ _
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [coefficient, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [v, normSq, diag, pow_two]

/-- Averaging the restricted Rayleigh inequalities at a whole-space minimizer
bounds the smallest increase after deleting one coordinate. -/
theorem dimension_bound {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (diag : ∀ i, A i i = 1) (l : ℝ) (d : Fin n → ℝ)
    (least : LeastOn A (fun _ => True) l)
    (restricted : ∀ i, LeastOn A (fun x => x i = 0) (d i)) :
    ∃ i, ((n : ℝ)-1) * (d i-l) ≤ 1-l := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i, _, best⟩ := Finset.exists_min_image Finset.univ d Finset.univ_nonempty
  obtain ⟨x, _, xpos, energy⟩ := least.2
  let y (j k : Fin n) := if j = k then 0 else x k
  have bound (j : Fin n) : d i * normSq (y j) ≤ quad A (y j) := by
    have hy : 0 ≤ normSq (y j) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    exact (mul_le_mul_of_nonneg_right (best j (Finset.mem_univ j)) hy).trans
      ((restricted j).1 _ (by simp [y]))
  have total := Finset.sum_le_sum (s := Finset.univ) (fun j _ => bound j)
  rw [← Finset.mul_sum, show (∑ j, normSq (y j)) = _ from norm_sum x,
      show (∑ j, quad A (y j)) = _ from quad_sum A x diag, energy] at total
  refine ⟨i, ?_⟩
  by_contra! bad
  have impossible := mul_lt_mul_of_pos_right bad xpos
  nlinarith only [impossible, total]

/-- For a positive-semidefinite matrix this gives an increase of at most `1 / (n - 1)`. -/
theorem dimension_bound_psd {n : ℕ} (hn : 2 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ)
    (diag : ∀ i, A i i = 1) (psd : ∀ x, 0 ≤ quad A x) (l : ℝ) (d : Fin n → ℝ)
    (least : LeastOn A (fun _ => True) l)
    (restricted : ∀ i, LeastOn A (fun x => x i = 0) (d i)) :
    ∃ i, d i-l ≤ 1 / ((n : ℝ)-1) := by
  obtain ⟨i, hi⟩ := dimension_bound hn A diag l d least restricted
  obtain ⟨x, _, xpos, energy⟩ := least.2
  have prod : 0 ≤ l * normSq x := energy ▸ psd x
  have hl := nonneg_of_mul_nonneg_left prod xpos
  have npos : 0 < (n : ℝ)-1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨i, (le_div_iff₀ npos).mpr ?_⟩
  linarith [mul_comm (d i-l) ((n:ℝ)-1)]

end RayleighDeletion

open OMA.S_mo_288399

namespace RayleighDeletion

/-- A number bounds the least deletion increase of all correlation matrices of order
`n` exactly when it is at least `1 / (n - 1)`. -/
theorem uniform_bound_iff {n : ℕ} (hn : 2 ≤ n) (b : ℝ) :
    (∀ (A : Matrix (Fin n) (Fin n) ℝ), A.IsSymm → (∀ i, A i i = 1) →
      (∀ x, 0 ≤ quad A x) → ∀ (l : ℝ) (d : Fin n → ℝ),
      LeastOn A (fun _ => True) l → (∀ i, LeastOn A (fun x => x i = 0) (d i)) →
      ∃ i, d i - l ≤ b) ↔ 1 / ((n : ℝ) - 1) ≤ b := by
  constructor
  · intro bound
    obtain ⟨symm, diag, least, restricted⟩ := CorrelationFamily.equicorrelation_least hn
    have psd (x : Fin n → ℝ) : 0 ≤ quad (CorrelationFamily.equicorrelation n) x := by
      simpa only [zero_mul] using least.1 x trivial
    obtain ⟨_, hi⟩ := bound _ symm diag psd _ _ least restricted
    simpa only [sub_zero] using hi
  · intro bound A _ diag psd l d least restricted
    obtain ⟨i, hi⟩ := dimension_bound_psd hn A diag psd l d least restricted
    exact ⟨i, hi.trans bound⟩

end RayleighDeletion

namespace CorrelationBounds
open OMA.S_mo_288399 Finset

private lemma quad_at {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (symm : A.IsSymm)
    (j : Fin n) (x : Fin n → ℝ) :
    quad A x =
      (∑ a ∈ univ.erase j, ∑ b ∈ univ.erase j, x a*A a b*x b) +
      2*x j*(∑ a ∈ univ.erase j, A a j*x a) + A j j*(x j)^2 := by
  have row (a : Fin n) : (∑ b, x a*A a b*x b) =
      (∑ b ∈ univ.erase j, x a*A a b*x b) + x a*A a j*x j :=
    (sum_erase_add univ _ (mem_univ j)).symm
  have c₁ : (∑ a ∈ univ.erase j, x a*A a j*x j) = x j*(∑ a ∈ univ.erase j, A a j*x a) := by
    rw [mul_sum]
    exact sum_congr rfl fun _ _ => by ring
  have c₂ : (∑ a ∈ univ.erase j, x j*A j a*x a) = x j*(∑ a ∈ univ.erase j, A a j*x a) := by
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    have e : A j a = A a j := congrFun (congrFun symm a) j
    rw [e]; ring
  unfold quad
  rw [← sum_erase_add univ (fun a => ∑ b, x a * A a b * x b) (mem_univ j)]
  simp_rw [row]
  rw [sum_add_distrib,c₁,c₂]
  ring

/-- A coordinate-deleted Rayleigh minimum controls that same off-diagonal column. -/
theorem local_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (symm : A.IsSymm) (diag : ∀ i, A i i = 1) (l : ℝ) (d : Fin n → ℝ)
    (full : LeastOn A (fun _ => True) l)
    (del : ∀ i, LeastOn A (fun x => x i=0) (d i)) (j : Fin n) :
    (1-l)*(d j-l) ≤ ∑ k, if k=j then 0 else (A k j)^2 := by
  let J := (univ : Finset (Fin n)).erase j
  let e : Fin n → ℝ := fun k => if k=j then 1 else 0
  have en : normSq e = 1 := by simp [normSq,e,ite_pow]
  have eq : quad A e = 1 := by
    rw [quad_at A symm j]
    simp +contextual [e,diag]
  have nonneg : 0 ≤ 1-l := by
    have test := full.1 e trivial
    rw [en,eq,mul_one] at test
    linarith
  obtain ⟨x,_,npos,eval⟩ := full.2
  let R := ∑ k ∈ J, (x k)^2
  let S := ∑ k ∈ J, A k j*x k
  let C := ∑ k ∈ J, (A k j)^2
  let Q := ∑ a ∈ J, ∑ b ∈ J, x a*A a b*x b
  have total : normSq x = R+(x j)^2 := (sum_erase_add univ _ (mem_univ j)).symm
  have decomp : quad A x = Q+2*x j*S+(x j)^2 := by simpa only [diag,one_mul] using quad_at A symm j x
  let y : Fin n → ℝ := fun i => if i=j then 0 else x i
  have yz : y j=0 := if_pos rfl
  have agree (i : Fin n) (hi : i ∈ J) : y i = x i := if_neg (mem_erase.mp hi).1
  have yn : normSq y=R := by
    unfold normSq
    rw [← sum_erase_add univ (fun i => (y i)^2) (mem_univ j),yz]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,add_zero]
    exact sum_congr rfl fun k hk => by rw [agree k hk]
  have yq : quad A y=Q := by
    rw [quad_at A symm j,yz]
    simp only [mul_zero,zero_mul,add_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]
    refine sum_congr rfl fun a ha => sum_congr rfl fun b hb => ?_
    rw [agree a ha,agree b hb]
  have restricted := (del j).1 y yz
  rw [yn,yq] at restricted
  rw [total,decomp] at eval
  rw [total] at npos
  have square : S^2 ≤ C*R := sum_mul_sq_le_sq_mul_sq J (fun k => A k j) x
  have csum : (∑ k, if k=j then 0 else (A k j)^2) = C := by
    rw [← sum_erase_add univ (fun k => if k=j then 0 else (A k j)^2) (mem_univ j)]
    simp only [ite_true,add_zero]
    exact sum_congr rfl fun k hk => if_neg (mem_erase.mp hk).1
  rw [csum]
  have positiveR : 0 ≤ R := sum_nonneg fun k _ => sq_nonneg (x k)
  have positiveC : 0 ≤ C := sum_nonneg fun k _ => sq_nonneg (A k j)
  rcases positiveR.eq_or_lt with zero | positive
  · have zr : R=0 := zero.symm
    rw [zr,mul_zero] at square
    have zs : S=0 := by nlinarith [sq_nonneg S]
    rw [zr] at npos eval restricted
    rw [zs] at eval
    have bound : (1-l)*(x j)^2 ≤ 0 := by linarith
    have vpos : 0 < (x j)^2 := by linarith
    have eq0 : 1-l=0 := by
      by_contra! hh
      exact (not_lt_of_ge bound) (mul_pos (lt_of_le_of_ne nonneg (Ne.symm hh)) vpos)
    simpa only [eq0,zero_mul] using positiveC
  · apply (mul_le_mul_iff_left₀ positive).mp
    calc
      (1-l)*(d j-l)*R ≤ (1-l)*(Q-l*R) := by
        calc
          _ = (1-l)*(d j*R-l*R) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) nonneg
      _ ≤ S^2 := by
        have root : Q-l*R = -(1-l)*(x j)^2 - 2*x j*S := by linarith
        rw [root]
        nlinarith [sq_nonneg ((1-l)*x j+S)]
      _ ≤ C*R := square

end CorrelationBounds

namespace SharpColumn
open Finset

/-- Combine the dimension bound and the individual squared column bounds. -/
theorem combine {n : ℕ} (hn : 2≤n) (l : ℝ) (d c : Fin n → ℝ)
    (nonneg : ∀ j, 0≤c j)
    (global : ∃ i, ((n:ℝ)-1)*(d i-l) ≤ 1-l)
    (local_bound : ∀ j, (1-l)*(d j-l) ≤ c j) :
    ∃ i, ∀ j, Real.sqrt ((n:ℝ)-1)*(d i-l) ≤ Real.sqrt (c j) := by
  have hdim : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (n:ℝ)-1 := by linarith
  have hn' : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  obtain ⟨i,_,best⟩ := exists_min_image (univ : Finset (Fin n)) d univ_nonempty
  refine ⟨i,?_⟩
  intro j
  by_cases hgap : 0 ≤ d i-l
  · obtain ⟨k,hk⟩ := global
    have h₁ : ((n:ℝ)-1)*(d i-l) ≤ 1-l :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_right (best k (mem_univ _)) _) hpos.le).trans hk
    have h₂ : 0≤1-l := (mul_nonneg hpos.le hgap).trans h₁
    have h₃ : (1-l)*(d i-l) ≤ c j :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_right (best j (mem_univ _)) _) h₂).trans (local_bound j)
    have product := (mul_le_mul_of_nonneg_right h₁ hgap).trans h₃
    apply (Real.le_sqrt (mul_nonneg (Real.sqrt_nonneg _) hgap) (nonneg j)).2
    rw [mul_pow, Real.sq_sqrt hpos.le]
    nlinarith only [product]
  · exact (mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) (le_of_not_ge hgap)).trans
      (Real.sqrt_nonneg _)

end SharpColumn

namespace SharpColumn
open Finset OMA.S_mo_288399

/-- For the least increase over the coordinate deletions, the bound with
denominator `√(n−1)` holds for every column of the matrix. -/
theorem every_column {n : ℕ} (hn : 2≤n) (A : Matrix (Fin n) (Fin n) ℝ)
    (symm : A.IsSymm) (diag : ∀ i,A i i=1) (l : ℝ) (d : Fin n → ℝ)
    (least : LeastOn A (fun _ => True) l)
    (restricted : ∀ i, LeastOn A (fun x => x i=0) (d i)) :
    ∃ i, ∀ j, Real.sqrt ((n:ℝ)-1)*(d i-l) ≤
      Real.sqrt (∑ k, if k=j then 0 else A k j ^ 2) := by
  apply combine hn l d (fun j => ∑ k, if k=j then 0 else A k j ^ 2)
  · intro j
    exact sum_nonneg fun k _ => by split_ifs <;> positivity
  · exact RayleighDeletion.dimension_bound hn A diag l d least restricted
  · intro j
    exact CorrelationBounds.local_bound A symm diag l d least restricted j

end SharpColumn
