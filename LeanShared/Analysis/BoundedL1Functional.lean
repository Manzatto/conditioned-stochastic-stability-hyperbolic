module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Complex.Basic

/-! A bounded measurable amplitude defines an actual continuous linear
functional on L1 by integration, with its explicit bound. -/
public noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace LeanShared.BoundedL1Functional
variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)

theorem integrable_product (f : Y → ℂ) (B : ℝ)
    (measurable : AEStronglyMeasurable f μ) (bound : ∀ᵐ y ∂μ, ‖f y‖ ≤ B)
    (g : Lp ℂ 1 μ) : Integrable (fun y => f y*g y) μ :=
  (L1.integrable_coeFn g).bdd_mul measurable bound

@[expose] def linear (f : Y → ℂ) (B : ℝ)
    (measurable : AEStronglyMeasurable f μ) (bound : ∀ᵐ y ∂μ, ‖f y‖ ≤ B) :
    Lp ℂ 1 μ →ₗ[ℂ] ℂ where
  toFun g := ∫ y, f y*g y ∂μ
  map_add' g h := by
    calc
      _ = ∫ y, f y*g y+f y*h y ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add g h] with y hy
        rw [hy,Pi.add_apply,mul_add]
      _ = _ := integral_add (integrable_product μ f B measurable bound g)
        (integrable_product μ f B measurable bound h)
  map_smul' c g := by
    calc
      _ = ∫ y, c*(f y*g y) ∂μ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c g] with y hy
        rw [hy]
        simp only [Pi.smul_apply,smul_eq_mul,mul_left_comm]
      _ = _ := by rw [integral_const_mul]; rfl

theorem linear_bound (f : Y → ℂ) (B : ℝ)
    (measurable : AEStronglyMeasurable f μ) (bound : ∀ᵐ y ∂μ, ‖f y‖ ≤ B)
    (g : Lp ℂ 1 μ) : ‖linear μ f B measurable bound g‖ ≤ B*‖g‖ := by
  change ‖∫ y, f y*g y ∂μ‖ ≤ _
  calc
    _ ≤ ∫ y, ‖f y*g y‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, B*‖g y‖ ∂μ := by
      apply integral_mono_ae (integrable_product μ f B measurable bound g).norm
        ((L1.integrable_coeFn g).norm.const_mul B)
      filter_upwards [bound] with y hy
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
    _ = B*‖g‖ := by rw [integral_const_mul,← L1.norm_eq_integral_norm]

@[expose] def functional (f : Y → ℂ) (B : ℝ)
    (measurable : AEStronglyMeasurable f μ) (bound : ∀ᵐ y ∂μ, ‖f y‖ ≤ B) :
    Lp ℂ 1 μ →L[ℂ] ℂ :=
  (linear μ f B measurable bound).mkContinuous B (linear_bound μ f B measurable bound)

theorem functional_apply (f : Y → ℂ) (B : ℝ)
    (measurable : AEStronglyMeasurable f μ) (bound : ∀ᵐ y ∂μ, ‖f y‖ ≤ B)
    (g : Lp ℂ 1 μ) : functional μ f B measurable bound g=∫ y, f y*g y ∂μ := rfl

theorem functional_norm_le (f : Y → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (measurable : AEStronglyMeasurable f μ) (bound : ∀ᵐ y ∂μ, ‖f y‖ ≤ B) :
    ‖functional μ f B measurable bound‖ ≤ B :=
  LinearMap.mkContinuous_norm_le _ hB (linear_bound μ f B measurable bound)
end LeanShared.BoundedL1Functional
