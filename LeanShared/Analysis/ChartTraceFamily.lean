module
public import LeanShared.Analysis.RegularizedTraceFunctional
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Regularized trace families indexed by finitely many charts and a translation parameter.
The family on `Fin n × E` with the counting measure in the chart index has regularized trace
and smoothing given by finite sums of translation integrals. -/
public noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory
namespace LeanShared.ChartTraceFamily

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {n : ℕ}
  (μE : Measure E) [SFinite μE]
  (ψ : Fin n → E → X →L[ℂ] ℂ) (e : Fin n → E → X)
  (hψ : ∀ k, Continuous (ψ k)) (he : ∀ k, Continuous (e k))
  (hint : ∀ k, Integrable (fun y => ‖ψ k y‖ * ‖e k y‖) μE)

/-- The chart trace family. -/
@[expose] def family : RegularizedTraceFunctional.Family X (Fin n × E) where
  measure := (Measure.count : Measure (Fin n)).prod μE
  test := fun p => ψ p.1 p.2
  vector := fun p => e p.1 p.2
  continuous_test := continuous_prod_of_discrete_left.mpr hψ
  continuous_vector := continuous_prod_of_discrete_left.mpr he
  integrable := by
    have cont : Continuous (fun p : Fin n × E => ‖ψ p.1 p.2‖ * ‖e p.1 p.2‖) :=
      (continuous_prod_of_discrete_left.mpr hψ).norm.mul
        (continuous_prod_of_discrete_left.mpr he).norm
    exact (integrable_prod_iff cont.aestronglyMeasurable).mpr
      ⟨ae_of_all _ fun k => hint k, Integrable.of_finite⟩

theorem traceL_apply' (A : X →L[ℂ] X) :
    (family μE ψ e hψ he hint).traceL A = ∑ k, ∫ y, ψ k y (A (e k y)) ∂μE := by
  rw [RegularizedTraceFunctional.Family.traceL_apply]
  change ∫ p, ψ p.1 p.2 (A (e p.1 p.2)) ∂((Measure.count : Measure (Fin n)).prod μE) = _
  rw [integral_prod (fun p : Fin n × E => ψ p.1 p.2 (A (e p.1 p.2)))
    ((family μE ψ e hψ he hint).integrable_apply A), integral_count]

theorem smoothing_apply' (v : X) :
    (family μE ψ e hψ he hint).smoothing v = ∑ k, ∫ y, ψ k y v • e k y ∂μE := by
  change ∫ p, ψ p.1 p.2 v • e p.1 p.2 ∂((Measure.count : Measure (Fin n)).prod μE) = _
  rw [integral_prod (fun p : Fin n × E => ψ p.1 p.2 v • e p.1 p.2)
    ((family μE ψ e hψ he hint).integrable_smul v), integral_count]

end LeanShared.ChartTraceFamily
