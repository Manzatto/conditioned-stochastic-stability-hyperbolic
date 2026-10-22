module
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Literal scalar killed duality is derived from the actual Jacobian
pushforward law. Source and target killing indicators are retained exactly. -/
public noncomputable section
namespace LeanShared.KilledJacobianDuality
open Set MeasureTheory Measure
open scoped ENNReal

set_option maxHeartbeats 1600000 in
theorem lintegral
    {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (σ : Measure M) (H : M ≃ₜ M) (K : Set M) (measurableK : MeasurableSet K)
    (j : M → ℝ) (measurableJ : Measurable j)
    (law : σ.map H = σ.withDensity (fun x => ENNReal.ofReal (j x)))
    (w : M → ℝ) (measurableW : Measurable w) (R : ℝ)
    (f g : M → ℝ≥0∞) (measurableF : Measurable f) (measurableG : Measurable g) :
    (∫⁻ x, g x * (ENNReal.ofReal (w (H.symm x) / R) * ENNReal.ofReal (j x) *
      K.indicator f (H.symm x)) ∂σ.restrict K) =
      ∫⁻ x, f x * (ENNReal.ofReal (w x / R) * K.indicator g (H x)) ∂σ.restrict K := by
  let h : M → ℝ≥0∞ := fun y => K.indicator g y *
    (ENNReal.ofReal (w (H.symm y) / R) * K.indicator f (H.symm y))
  have measurableH : Measurable h :=
    (measurableG.indicator measurableK).mul
      (((measurableW.comp H.symm.continuous.measurable).div_const R).ennreal_ofReal.mul
        ((measurableF.indicator measurableK).comp H.symm.continuous.measurable))
  calc
    _ = ∫⁻ x, ENNReal.ofReal (j x) * h x ∂σ := by
      rw [←lintegral_indicator measurableK]
      apply lintegral_congr
      intro x
      by_cases inside : x ∈ K
      · simp only [indicator_of_mem inside,h]
        ac_rfl
      · simp only [indicator_of_notMem inside,h,mul_zero,zero_mul]
    _ = ∫⁻ x, h x ∂σ.withDensity (fun y => ENNReal.ofReal (j y)) :=
      (lintegral_withDensity_eq_lintegral_mul σ measurableJ.ennreal_ofReal measurableH).symm
    _ = ∫⁻ x, h x ∂σ.map H := by rw [law]
    _ = ∫⁻ x, h (H x) ∂σ := lintegral_map' measurableH.aemeasurable H.continuous.measurable.aemeasurable
    _ = _ := by
      rw [←lintegral_indicator measurableK]
      apply lintegral_congr
      intro x
      by_cases inside : x ∈ K
      · simp only [h,H.symm_apply_apply,indicator_of_mem inside]
        ac_rfl
      · simp only [h,H.symm_apply_apply,indicator_of_notMem inside,mul_zero]

end LeanShared.KilledJacobianDuality
