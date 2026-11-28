import OMAStatements.S_mo_344923

/-!
This formalizes e.lipnowski's counterexample from MathOverflow answer 344926.
Two equal fair bits have a joint law different from the product of their
marginals. The constant map takes their joint law to a point mass.
-/

open MeasureTheory Set
open scoped ENNReal
open OMA.S_mo_344923

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_344923.main) := by
  intro preserve
  let μ : Measure (ℝ × ℝ) := (2 : ℝ≥0∞)⁻¹ •
    (Measure.dirac (0, 0) + Measure.dirac (1, 1))
  have : IsProbabilityMeasure μ := by
    constructor
    simp [μ, Measure.smul_apply, Measure.add_apply, ENNReal.inv_two_add_inv_two]
  have eq := preserve ℝ ℝ μ inferInstance (fun _ => (0 : ℝ)) (LipschitzWith.const' (0 : ℝ))
  have mapped : μ.map (fun _ : ℝ × ℝ => ((0 : ℝ), (0 : ℝ))) = Measure.dirac (0,0) := by
    simp [Measure.map_const]
  have collapsed : mutualInformation (Measure.dirac ((0 : ℝ),(0 : ℝ))) = 0 := by
    simp [mutualInformation, Measure.fst, Measure.snd, measurable_fst,
      measurable_snd, Measure.dirac_prod_dirac, InformationTheory.klDiv_self]
  rw [mapped, collapsed] at eq
  have independent : μ = μ.fst.prod μ.snd := InformationTheory.klDiv_eq_zero_iff.mp eq.symm
  have joint : μ (({0} : Set ℝ) ×ˢ ({1} : Set ℝ)) = 0 := by
    simp [μ, Measure.add_apply, Measure.smul_apply]
  have first : μ.fst ({0} : Set ℝ) = (2 : ℝ≥0∞)⁻¹ := by
    rw [Measure.fst_apply (measurableSet_singleton _)]
    simp [μ, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply]
  have second : μ.snd ({1} : Set ℝ) = (2 : ℝ≥0∞)⁻¹ := by
    rw [Measure.snd_apply (measurableSet_singleton _)]
    simp [μ, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply]
  rw [independent, Measure.prod_prod, first, second] at joint
  simp at joint
