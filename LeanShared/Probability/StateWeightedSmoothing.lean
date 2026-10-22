module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! State-dependent bounded continuous weights preserve scalar smoothing.
Freeze the weight at the reference state and control the error by dominated
convergence. No derivative of the noise density or the weight is needed. -/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LeanShared.StateWeightedSmoothing
variable {X Ω : Type*} [TopologicalSpace X] [FirstCountableTopology X]
  [MeasurableSpace X] [MeasurableSpace Ω]

theorem continuous_weighted_integral
    (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (H : X × Ω → X) (hH : Measurable H)
    (W : X × Ω → ℝ) (hW : Measurable W)
    (weight_continuous : ∀ z, Continuous (fun x => W (x, z)))
    (B : ℝ) (hB : 0 ≤ B) (bound : ∀ x z, ‖W (x, z)‖ ≤ B)
    (f : X → ℝ) (hf : Measurable f) (C : ℝ) (_hC : 0 ≤ C)
    (fbound : ∀ x, ‖f x‖ ≤ C)
    (frozen : ∀ b : Ω → ℝ, Measurable b → (∀ z, ‖b z‖ ≤ B) →
      Continuous (fun x => ∫ z, b z * f (H (x, z)) ∂ρ)) :
    Continuous (fun x => ∫ z, W (x, z) * f (H (x, z)) ∂ρ) := by
  have meas (x : X) : Measurable (fun z => f (H (x, z))) :=
    hf.comp (hH.comp measurable_prodMk_left)
  have integ (x y : X) : Integrable (fun z => W (x, z) * f (H (y, z))) ρ := by
    apply (integrable_const (B * C)).mono'
      (((hW.comp measurable_prodMk_left).mul (meas y)).aestronglyMeasurable)
    exact ae_of_all _ (fun z => by
      change ‖W (x, z) * f (H (y, z))‖ ≤ B * C
      rw [norm_mul]
      exact mul_le_mul (bound x z) (fbound _) (norm_nonneg _) hB)
  apply continuous_iff_continuousAt.mpr
  intro x₀
  have hd : Continuous (fun x => ∫ z, ‖W (x, z) - W (x₀, z)‖ ∂ρ) := by
    apply continuous_of_dominated (bound := fun _ => 2 * B)
    · intro x
      exact (((hW.comp measurable_prodMk_left).sub
        (hW.comp measurable_prodMk_left)).norm).aestronglyMeasurable
    · intro x
      exact ae_of_all _ (fun z => by
        change ‖‖W (x, z) - W (x₀, z)‖‖ ≤ 2 * B
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact (norm_sub_le _ _).trans (by linarith [bound x z, bound x₀ z]))
    · exact integrable_const _
    · exact ae_of_all _ (fun z => ((weight_continuous z).sub continuous_const).norm)
  have hzero : Tendsto (fun x => C * ∫ z, ‖W (x, z) - W (x₀, z)‖ ∂ρ)
      (𝓝 x₀) (𝓝 0) := by
    simpa only [sub_self, norm_zero, integral_zero, mul_zero] using
      (hd.continuousAt (x := x₀)).tendsto.const_mul C
  have error (x : X) :
      ‖(∫ z, W (x, z) * f (H (x, z)) ∂ρ) -
        ∫ z, W (x₀, z) * f (H (x, z)) ∂ρ‖ ≤
      C * ∫ z, ‖W (x, z) - W (x₀, z)‖ ∂ρ := by
    rw [← integral_sub (integ x x) (integ x₀ x)]
    have hi : Integrable (fun z => C * ‖W (x, z) - W (x₀, z)‖) ρ := by
      apply ((integrable_const (2 * B)).mono'
        (((hW.comp measurable_prodMk_left).sub
          (hW.comp measurable_prodMk_left)).norm).aestronglyMeasurable ?_).const_mul C
      exact ae_of_all _ (fun z => by
        change ‖‖W (x, z) - W (x₀, z)‖‖ ≤ 2 * B
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact (norm_sub_le _ _).trans (by linarith [bound x z, bound x₀ z]))
    calc
      _ ≤ ∫ z, C * ‖W (x, z) - W (x₀, z)‖ ∂ρ := by
        apply norm_integral_le_of_norm_le hi
        exact ae_of_all _ (fun z => by
          rw [← sub_mul, norm_mul]
          exact (mul_le_mul_of_nonneg_left (fbound _) (norm_nonneg _)).trans_eq
            (mul_comm _ _))
      _ = _ := integral_const_mul _ _
  have he := squeeze_zero_norm error hzero
  have hh := (frozen (fun z => W (x₀, z)) (hW.comp measurable_prodMk_left)
    (bound x₀)).continuousAt.tendsto.add he
  have same : (fun x => (∫ z, W (x₀, z) * f (H (x, z)) ∂ρ) +
      ((∫ z, W (x, z) * f (H (x, z)) ∂ρ) -
        ∫ z, W (x₀, z) * f (H (x, z)) ∂ρ)) =
      (fun x => ∫ z, W (x, z) * f (H (x, z)) ∂ρ) := by
    funext x
    ring
  rw [same, add_zero] at hh
  exact hh

end LeanShared.StateWeightedSmoothing
