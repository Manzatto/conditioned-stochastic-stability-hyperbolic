module
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! The complex bilinear transfer identity follows from the proved scalar
Jacobian pushforward law. No bilinear change-of-variables source is needed. -/
public noncomputable section
namespace LeanShared.JacobianBilinearDuality
open MeasureTheory Measure
open scoped ENNReal

set_option maxHeartbeats 1600000 in
theorem integral
    {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (σ : Measure M) (H : M ≃ₜ M) (j : M → ℝ) (measurableJ : Measurable j)
    (nonnegativeJ : ∀ x, 0 ≤ j x)
    (law : σ.map H = σ.withDensity (fun x => ENNReal.ofReal (j x)))
    (w : M → ℝ) (f g : M → ℂ) :
    (∫ x, (w x : ℂ) * f (H x) * g x ∂σ) =
      ∫ y, f y * (((j y * w (H.symm y) : ℝ) : ℂ) * g (H.symm y)) ∂σ := by
  let h : M → ℂ := fun y => (w (H.symm y) : ℂ) * f y * g (H.symm y)
  calc
    _ = ∫ y, h y ∂σ.map H := by
      have actual := integral_map_equiv (μ := σ) H.toMeasurableEquiv h
      exact (by simpa only [h,Homeomorph.toMeasurableEquiv_coe,H.symm_apply_apply] using actual.symm)
    _ = ∫ y, h y ∂σ.withDensity (fun x => ENNReal.ofReal (j x)) := by rw [law]
    _ = ∫ y, (ENNReal.ofReal (j y)).toReal • h y ∂σ :=
      integral_withDensity_eq_integral_toReal_smul measurableJ.ennreal_ofReal
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) h
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        simp only [ENNReal.toReal_ofReal (nonnegativeJ y),h,Complex.real_smul,Complex.ofReal_mul]
        ring)

end LeanShared.JacobianBilinearDuality
