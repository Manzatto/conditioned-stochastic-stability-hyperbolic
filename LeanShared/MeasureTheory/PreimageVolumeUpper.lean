module
public import Mathlib.MeasureTheory.Function.Jacobian

/-! Lower Jacobian bounds give upper preimage volume bounds through the
injective Haar change-of-variables theorem. The multiplicative formulation
also applies when the measured set has infinite volume. -/
public noncomputable section
namespace LeanShared.PreimageVolumeUpper
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ:Measure E) [IsAddHaarMeasure μ]

theorem image_bound (f:E→E) (s:Set E) (measurable:MeasurableSet s)
    (A:E→E→L[ℝ]E) (derivative:∀x∈s,HasFDerivWithinAt f (A x) s x)
    (injective:InjOn f s) (J C:ℝ) (nonnegative:0≤C)
    (bound:∀x∈s,J≤C*|(A x).det|) :
    ENNReal.ofReal J*μ s≤ENNReal.ofReal C*μ (f '' s) := by
  calc
    ENNReal.ofReal J*μ s = ∫⁻ _ in s,ENNReal.ofReal J ∂μ := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in s,ENNReal.ofReal (C*|(A x).det|) ∂μ :=
      setLIntegral_mono' measurable (fun x hx=>ENNReal.ofReal_le_ofReal (bound x hx))
    _ = ENNReal.ofReal C*(∫⁻ x in s,ENNReal.ofReal |(A x).det| ∂μ) := by
      simp_rw [ENNReal.ofReal_mul nonnegative]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := congrArg (fun z=>ENNReal.ofReal C*z)
      (lintegral_abs_det_fderiv_eq_addHaar_image μ measurable derivative injective)

theorem preimage_bound (f:E≃ₜE) (B:Set E) (measurable:MeasurableSet B)
    (A:E→E→L[ℝ]E)
    (derivative:∀x∈f ⁻¹' B,HasFDerivWithinAt f (A x) (f ⁻¹' B) x)
    (J C:ℝ) (nonnegative:0≤C)
    (bound:∀x∈f ⁻¹' B,J≤C*|(A x).det|) :
    ENNReal.ofReal J*μ (f ⁻¹' B)≤ENNReal.ofReal C*μ B := by
  have estimate := image_bound μ f (f ⁻¹' B) (measurable.preimage f.continuous.measurable)
    A derivative f.injective.injOn J C nonnegative bound
  simpa only [f.surjective.image_preimage] using estimate
end LeanShared.PreimageVolumeUpper
