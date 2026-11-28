import OMAStatements.S_mo_344923
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# Mutual information under measurable maps

For the mutual information defined in MathOverflow 344923, separate measurable
transformations can only decrease information. Equality holds when both original
coordinates can be recovered measurably, almost everywhere under their joint law.
-/

open MeasureTheory
open OMA.S_mo_344923

namespace MutualInformation

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Both coordinates can be processed by different measurable functions. -/
theorem processing (μ : Measure (A × A)) [IsFiniteMeasure μ] {f g : A → B}
    (hf : Measurable f) (hg : Measurable g) :
    mutualInformation (μ.map (Prod.map f g)) ≤ mutualInformation μ := by
  have hfst : (μ.map (Prod.map f g)).fst = μ.fst.map f := by
    unfold Measure.fst
    rw [Measure.map_map measurable_fst (hf.prodMap hg), Measure.map_map hf measurable_fst]
    rfl
  have hsnd : (μ.map (Prod.map f g)).snd = μ.snd.map g := by
    unfold Measure.snd
    rw [Measure.map_map measurable_snd (hf.prodMap hg), Measure.map_map hg measurable_snd]
    rfl
  rw [mutualInformation, hfst, hsnd, Measure.map_prod_map _ _ hf hg]
  exact InformationTheory.klDiv_map_le _ _ (hf.prodMap hg)

/-- Measurably recovering the two coordinates almost surely preserves information. -/
theorem recoverable (μ : Measure (A × A)) [IsFiniteMeasure μ] {f g : A → B}
    {u v : B → A} (hf : Measurable f) (hg : Measurable g)
    (hu : Measurable u) (hv : Measurable v)
    (left : ∀ᵐ z ∂μ, u (f z.1) = z.1) (right : ∀ᵐ z ∂μ, v (g z.2) = z.2) :
    mutualInformation (μ.map (Prod.map f g)) = mutualInformation μ := by
  refine le_antisymm (processing μ hf hg) ?_
  have h := processing (μ.map (Prod.map f g)) hu hv
  have undo : (μ.map (Prod.map f g)).map (Prod.map u v) = μ := by
    rw [Measure.map_map (hu.prodMap hv) (hf.prodMap hg)]
    refine Eq.trans ?_ (Measure.map_id (μ := μ))
    apply Measure.map_congr
    filter_upwards [left,right] with z hz hz'
    exact Prod.ext hz hz'
  rwa [undo] at h

/-- In particular a measurable left inverse suffices on every point. -/
theorem left_inverses (μ : Measure (A × A)) [IsFiniteMeasure μ] {f g : A → B}
    {u v : B → A} (hf : Measurable f) (hg : Measurable g)
    (hu : Measurable u) (hv : Measurable v)
    (left : Function.LeftInverse u f) (right : Function.LeftInverse v g) :
    mutualInformation (μ.map (Prod.map f g)) = mutualInformation μ :=
  recoverable μ hf hg hu hv (Filter.Eventually.of_forall fun z => left z.1)
    (Filter.Eventually.of_forall fun z => right z.2)

end MutualInformation
#print axioms MutualInformation.processing
#print axioms MutualInformation.recoverable
#print axioms MutualInformation.left_inverses
