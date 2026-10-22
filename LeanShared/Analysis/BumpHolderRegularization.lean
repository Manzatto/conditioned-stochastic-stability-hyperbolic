module
public import LeanShared.Probability.TranslationHolderAverage
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Literal normalized smooth bump convolution: its law is a probability,
its Hölder constant does not increase, and its uniform error is bounded
by the Hölder constant times the actual bump radius to the exponent. -/
public noncomputable section
open MeasureTheory Filter Set ContinuousLinearMap
open scoped Topology Convolution BoundedContinuousFunction
namespace LeanShared.BumpHolderRegularization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] (φ : ContDiffBump (0 : E))

def law : Measure E := μ.withDensity (fun x => ENNReal.ofReal (φ.normed μ x))

instance law_probability : IsProbabilityMeasure (law μ φ) where
  measure_univ := by
    rw [law, withDensity_apply _ MeasurableSet.univ]
    rw [Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal (φ.integrable_normed (μ := μ))
      (Eventually.of_forall (φ.nonneg_normed (μ := μ))), φ.integral_normed]
    norm_num

theorem law_radius : ∀ᵐ w ∂law μ φ, ‖w‖ ≤ φ.rOut := by
  rw [law, ae_withDensity_iff ((φ.continuous_normed (μ := μ)).measurable.ennreal_ofReal)]
  apply Eventually.of_forall
  intro w hw
  have hn : φ.normed μ w ≠ 0 := by
    intro hz
    exact hw (by simp [hz])
  have hball : w ∈ Metric.ball (0 : E) φ.rOut := by
    rw [← φ.support_normed_eq (μ := μ)]
    exact hn
  exact (by simpa only [Metric.mem_ball, dist_zero_right] using hball : ‖w‖ < φ.rOut).le

omit [μ.IsAddHaarMeasure] in
/-- Our average is exactly the usual physical mollifier convolution. -/
theorem average_eq (f : E →ᵇ ℂ) (x : E) :
    TranslationHolderAverage.average (law μ φ) f x =
      (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (fun y => f y)) x := by
  rw [TranslationHolderAverage.average, law,
    integral_withDensity_eq_integral_toReal_smul
      ((φ.continuous_normed (μ := μ)).measurable.ennreal_ofReal)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (φ.nonneg_normed _)]
  rfl

/-- Actual convolution, not a supplied smoothing operator, preserves the
higher Hölder constant. -/
theorem convolution_increment (f : E →ᵇ ℂ) {a C : ℝ}
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ a) (x y : E) :
    ‖(φ.normed μ ⋆[lsmul ℝ ℝ, μ] (fun z => f z)) x -
      (φ.normed μ ⋆[lsmul ℝ ℝ, μ] (fun z => f z)) y‖ ≤ C * ‖x - y‖ ^ a := by
  rw [← average_eq μ φ f x, ← average_eq μ φ f y]
  exact TranslationHolderAverage.increment_bound (law μ φ) f hf x y

theorem convolution_error (f : E →ᵇ ℂ) {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ a) (x : E) :
    ‖(φ.normed μ ⋆[lsmul ℝ ℝ, μ] (fun z => f z)) x - f x‖ ≤ C * φ.rOut ^ a := by
  rw [← average_eq μ φ f x]
  exact TranslationHolderAverage.error_bound (law μ φ) f ha hC hf (law_radius μ φ) x

end LeanShared.BumpHolderRegularization
