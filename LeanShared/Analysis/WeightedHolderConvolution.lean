module
public import LeanShared.Analysis.HolderConvolutionCancellation
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! Compact support upgrades actual Hölder cancellation to a radial envelope. -/
public noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction
namespace LeanShared.WeightedHolderConvolution
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E}

omit [MeasurableSpace E] [BorelSpace E] in
theorem difference_bound (f : E →ᵇ ℂ) {a C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (support : ∀ z, f z ≠ 0 → ‖z‖ ≤ R)
    (holder : ∀ x y, ‖f x-f y‖ ≤ C * ‖x-y‖ ^ a)
    (m : ℕ) (x y : E) :
    (1+‖x‖)^m * ‖f (x-y)-f x‖ ≤
      C * ‖y‖^a * (1+R+‖y‖)^m := by
  have estimate : ‖f (x-y)-f x‖ ≤ C * ‖y‖^a := by
    simpa only [sub_sub_cancel_left, norm_neg] using holder (x-y) x
  by_cases zero : f (x-y)-f x = 0
  · rw [zero, norm_zero, mul_zero]
    positivity
  have spatial : ‖x‖ ≤ R+‖y‖ := by
    by_cases first : f (x-y) = 0
    · have second : f x ≠ 0 := by
        intro hx
        exact zero (by rw [first, hx, sub_self])
      exact (support x second).trans (by linarith [norm_nonneg y])
    · have bound := support (x-y) first
      have triangle := norm_add_le (x-y) y
      rw [sub_add_cancel] at triangle
      linarith
  have weight : (1+‖x‖)^m ≤ (1+R+‖y‖)^m :=
    pow_le_pow_left₀ (by positivity) (by linarith) m
  calc
    _ ≤ (1+R+‖y‖)^m * (C * ‖y‖^a) :=
      mul_le_mul weight estimate (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem bound (k : E → ℂ) (integrable : Integrable k μ) (zero : ∫ y, k y ∂μ=0)
    (f : E →ᵇ ℂ) {a C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (support : ∀z, f z ≠ 0 → ‖z‖≤R)
    (holder : ∀x y, ‖f x-f y‖≤C*‖x-y‖^a) (m : ℕ)
    (moment : Integrable (fun y => ‖k y‖*‖y‖^a*(1+R+‖y‖)^m) μ) (x : E) :
    (1+‖x‖)^m * ‖∫ y, k y*f (x-y) ∂μ‖ ≤
      C * ∫ y, ‖k y‖*‖y‖^a*(1+R+‖y‖)^m ∂μ := by
  have product : Integrable (fun y => k y*f (x-y)) μ :=
    integrable.mul_bdd
      (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun y => f.norm_coe_le_norm (x-y))
  have subtract : (∫ y, k y*(f (x-y)-f x) ∂μ) = ∫ y, k y*f (x-y) ∂μ := by
    simp_rw [mul_sub]
    rw [integral_sub product (integrable.mul_const (f x)), integral_mul_const,zero,zero_mul,sub_zero]
  rw [←subtract]
  calc
    _ ≤ (1+‖x‖)^m * ∫ y, ‖k y*(f (x-y)-f x)‖ ∂μ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = ∫ y, (1+‖x‖)^m * ‖k y*(f (x-y)-f x)‖ ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ y, C*(‖k y‖*‖y‖^a*(1+R+‖y‖)^m) ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ fun y => by positivity)
        (moment.const_mul C) (ae_of_all _ fun y => by
          have estimate := difference_bound f hC hR support holder m x y
          have multiplied := mul_le_mul_of_nonneg_left estimate (norm_nonneg (k y))
          change (1+‖x‖)^m * ‖k y*(f (x-y)-f x)‖ ≤ C*(‖k y‖*‖y‖^a*(1+R+‖y‖)^m)
          rw [norm_mul]
          nlinarith only [multiplied])
    _ = _ := integral_const_mul _ _
end LeanShared.WeightedHolderConvolution
