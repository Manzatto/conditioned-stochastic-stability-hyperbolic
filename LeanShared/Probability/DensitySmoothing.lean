module

public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Strong-Feller integrals from a bounded continuous transition density -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace LeanShared.DensitySmoothing

variable {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X] [MeasurableSpace X] [MeasurableSpace Y]

theorem continuous_integral_of_bounded_density
    (K : Kernel X Y) (σ : Measure Y) [IsFiniteMeasure σ]
    (q : X × Y → ℝ) (hq : Measurable q) (hq0 : ∀ x y, 0 ≤ q (x, y))
    (hK : ∀ x, K x = σ.withDensity (fun y => ENNReal.ofReal (q (x, y))))
    (M : ℝ) (hM : 0 ≤ M) (hqM : ∀ x y, ‖q (x, y)‖ ≤ M)
    (hc : ∀ᵐ y ∂σ, Continuous (fun x => q (x, y)))
    (f : Y → ℝ) (hf : Measurable f) (B : ℝ)
    (hbound : ∀ y, ‖f y‖ ≤ B) : Continuous (fun x => ∫ y, f y ∂K x) := by
  have hi : ∀ x, (∫ y, f y ∂K x) = ∫ y, q (x, y) * f y ∂σ := by
    intro x
    rw [hK x, integral_withDensity_eq_integral_toReal_smul]
    · simp only [ENNReal.toReal_ofReal (hq0 x _), smul_eq_mul]
    · exact (hq.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
    · exact Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top)
  simp_rw [hi]
  apply continuous_of_dominated
    (bound := fun _ : Y => M * B)
  · intro x
    exact ((hq.comp (measurable_const.prodMk measurable_id)).mul hf).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall (fun y => by
      rw [norm_mul]
      exact mul_le_mul (hqM x y) (hbound y) (norm_nonneg _) hM)
  · exact integrable_const _
  · filter_upwards [hc] with y hy
    exact hy.mul continuous_const

end LeanShared.DensitySmoothing
