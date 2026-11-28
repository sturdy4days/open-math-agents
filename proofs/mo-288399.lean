import OMAStatements.S_mo_288399
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# Counterexamples to the column bound for the least-eigenvalue gap

The edit to MathOverflow question 288399 highlights the equicorrelation
matrix with off-diagonal entries `-1/(n-1)`. Computing both Rayleigh minima
and the off-diagonal column norm shows that this matrix contradicts Observation
2 in every dimension at least three. The registered statement was formalized
by Hengzhi He (@hehz2020).
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

open CorrelationFamily OMA.S_mo_288399

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_288399.main) := by
  intro claim
  obtain ⟨symm,diag,least,restricted⟩ := equicorrelation_least (n:=3) (by decide)
  have psd (x : Fin 3 → ℝ) : 0 ≤ quad (equicorrelation 3) x := by
    simpa only [zero_mul] using least.1 x trivial
  obtain ⟨i,bound⟩ := claim 3 (by decide) _ symm diag psd 0 (fun _ => _) least restricted 0
  exact (not_le_of_gt (column_witness (n:=3) (by decide) 0).2) bound
