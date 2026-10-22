module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! A normalized nonnegative eigenfunction times a finite eigenmeasure. -/

@[expose] public noncomputable section

open MeasureTheory

namespace LeanShared

variable {X : Type*} [MeasurableSpace X]

/-- The product measure `g μ`, without requiring the eigenmeasure to have mass one. -/
def eigenvectorMeasure (μ : Measure X) (g : X → ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (g x))

/-- The product measure charges only points where its real density is positive.
This supplies the starting-state qualification for a quasi-ergodic limit. -/
theorem eigenvectorMeasure_ae_pos (μ : Measure X) (g : X → ℝ)
    (hgm : Measurable g) : ∀ᵐ x ∂eigenvectorMeasure μ g, 0 < g x := by
  unfold eigenvectorMeasure
  rw [ae_withDensity_iff hgm.ennreal_ofReal]
  exact ae_of_all μ fun _ hx => ENNReal.ofReal_ne_zero_iff.mp hx

theorem eigenvectorMeasure_isProbability (μ : Measure X) (g : X → ℝ)
    (hg : Integrable g μ) (hg0 : ∀ x, 0 ≤ g x) (hnorm : ∫ x, g x ∂μ = 1) :
    IsProbabilityMeasure (eigenvectorMeasure μ g) := by
  constructor
  unfold eigenvectorMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hg (ae_of_all μ hg0), hnorm,
    ENNReal.ofReal_one]

/-- Integration against the product measure is multiplication by the eigenfunction. -/
theorem integral_eigenvectorMeasure (μ : Measure X) (g : X → ℝ)
    (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (h : X → ℝ) :
    (∫ x, h x ∂eigenvectorMeasure μ g) = ∫ x, h x * g x ∂μ := by
  unfold eigenvectorMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hgm.ennreal_ofReal
    (ae_of_all μ fun x => ENNReal.ofReal_lt_top) h]
  apply integral_congr_ae
  exact ae_of_all μ fun x => by
    change (ENNReal.ofReal (g x)).toReal • h x = h x * g x
    rw [ENNReal.toReal_ofReal (hg0 x), smul_eq_mul, mul_comm]

end LeanShared
