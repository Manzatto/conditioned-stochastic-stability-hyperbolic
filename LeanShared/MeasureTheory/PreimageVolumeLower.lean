module

public import Mathlib.MeasureTheory.Function.Jacobian

/-! A differentiable shooting map with a bounded Jacobian cannot map a set of
arbitrarily small volume onto a fixed endpoint box. These estimates use the
actual derivative and Haar measure, rather than a supplied volume comparison. -/
public noncomputable section
namespace LeanShared.PreimageVolumeLower
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]

theorem image_le (f : E → E) (s : Set E) (hs : MeasurableSet s)
    (A : E → E →L[ℝ] E) (derivative : ∀ x ∈ s, HasFDerivWithinAt f (A x) s x)
    (J : ℝ) (bound : ∀ x ∈ s, |(A x).det| ≤ J) :
    μ (f '' s) ≤ ENNReal.ofReal J * μ s := by
  calc
    μ (f '' s) ≤ ∫⁻ x in s, ENNReal.ofReal |(A x).det| ∂μ :=
      addHaar_image_le_lintegral_abs_det_fderiv μ hs derivative
    _ ≤ ∫⁻ _ in s, ENNReal.ofReal J ∂μ :=
      setLIntegral_mono' hs (fun x hx => ENNReal.ofReal_le_ofReal (bound x hx))
    _ = _ := by rw [setLIntegral_const]

theorem preimage_le (f : E ≃ₜ E) (B : Set E) (hB : MeasurableSet B)
    (A : E → E →L[ℝ] E)
    (derivative : ∀ x ∈ f ⁻¹' B, HasFDerivWithinAt f (A x) (f ⁻¹' B) x)
    (J : ℝ) (bound : ∀ x ∈ f ⁻¹' B, |(A x).det| ≤ J) :
    μ B ≤ ENNReal.ofReal J * μ (f ⁻¹' B) := by
  have estimate := image_le μ f (f ⁻¹' B) (hB.preimage f.continuous.measurable)
    A derivative J bound
  simpa only [f.surjective.image_preimage] using estimate

end LeanShared.PreimageVolumeLower
