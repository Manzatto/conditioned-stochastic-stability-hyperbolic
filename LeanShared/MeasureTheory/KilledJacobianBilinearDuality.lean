module
public import LeanShared.MeasureTheory.JacobianBilinearDuality
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Exact complex killed transfer duality, including the boundary indicators.
A departure weight supported on the live region removes the inverse-side
source indicator without any assumption on the boundary measure. -/
public noncomputable section
namespace LeanShared.JacobianBilinearDuality
open Set MeasureTheory Measure
open scoped ENNReal

set_option maxHeartbeats 1600000 in
theorem killed_integral
    {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (σ : Measure M) (H : M ≃ₜ M) (j : M → ℝ) (measurableJ : Measurable j)
    (nonnegativeJ : ∀ x, 0 ≤ j x)
    (law : σ.map H = σ.withDensity (fun x => ENNReal.ofReal (j x)))
    (K : Set M) (measurableK : MeasurableSet K) (w : M → ℝ) (f g : M → ℂ) :
    (∫ x, (w x : ℂ) * K.indicator f (H x) * g x ∂σ.restrict K) =
      ∫ y, f y * (((j y * w (H.symm y) : ℝ) : ℂ) *
        K.indicator g (H.symm y)) ∂σ.restrict K := by
  have actual := integral σ H j measurableJ nonnegativeJ law w (K.indicator f) (K.indicator g)
  calc
    _ = ∫ x, (w x : ℂ) * K.indicator f (H x) * K.indicator g x ∂σ := by
      rw [←integral_indicator measurableK]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        by_cases hx : x ∈ K <;> simp [hx])
    _ = _ := actual
    _ = _ := by
      rw [←integral_indicator measurableK]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        by_cases hy : y ∈ K <;> simp [hy])

set_option maxHeartbeats 1600000 in
theorem supported_killed_integral
    {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (σ : Measure M) (H : M ≃ₜ M) (j : M → ℝ) (measurableJ : Measurable j)
    (nonnegativeJ : ∀ x, 0 ≤ j x)
    (law : σ.map H = σ.withDensity (fun x => ENNReal.ofReal (j x)))
    (K : Set M) (measurableK : MeasurableSet K) (w : M → ℝ)
    (support : Function.support w ⊆ K) (f g : M → ℂ) :
    (∫ x, (w x : ℂ) * K.indicator f (H x) * g x ∂σ.restrict K) =
      ∫ y, f y * (((j y * w (H.symm y) : ℝ) : ℂ) * g (H.symm y)) ∂σ.restrict K := by
  refine (killed_integral σ H j measurableJ nonnegativeJ law K measurableK w f g).trans ?_
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    by_cases inside : H.symm y ∈ K
    · rw [indicator_of_mem inside]
    · have zero : w (H.symm y) = 0 := by
        by_contra notzero
        exact inside (support (Function.mem_support.mpr notzero))
      simp only [zero,mul_zero,Complex.ofReal_zero,zero_mul])

end LeanShared.JacobianBilinearDuality
