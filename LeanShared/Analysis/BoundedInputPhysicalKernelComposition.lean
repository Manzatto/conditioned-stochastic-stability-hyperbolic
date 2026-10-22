module
public import LeanShared.Analysis.PhysicalKernelComposition
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Tactic

/-! The physical two-kernel identity applies to bounded input blocks,
including genuine Schwartz dyadic blocks which need not have compact support.
Fubini integrability follows from the actual L1 kernel and compact amplitude. -/
public noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace LeanShared.BoundedInputPhysicalKernelComposition
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem identity (μ ν : Measure E) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (G : E → E) (continuousG : Continuous G) (g : E → ℂ)
    (continuousg : Continuous g) (compactg : HasCompactSupport g)
    (u k₀ : E →ᵇ ℂ) (k₁ : E → ℂ) (continuous₁ : Continuous k₁)
    (integrable₁ : Integrable k₁ ν) (x : E) :
    (∫ w,k₀ (x-w)*g w*(∫ y,k₁ (G w-y)*u y ∂ν) ∂μ) =
      ∫ y,(∫ w,g w*k₀ (x-w)*k₁ (G w-y) ∂μ)*u y ∂ν := by
  let f : E → E → ℂ := fun w y => g w*k₀ (x-w)*k₁ (G w-y)*u y
  have joint : Continuous f.uncurry := by dsimp [f]; fun_prop
  have magnitude (w y : E) : ‖f w y‖ ≤
      (‖g w‖*‖k₀‖*‖u‖)*‖k₁ (G w-y)‖ := by
    dsimp [f]
    simp only [norm_mul]
    have first := mul_le_mul_of_nonneg_left (k₀.norm_coe_le_norm (x-w)) (norm_nonneg (g w))
    have second := mul_le_mul_of_nonneg_right first (norm_nonneg (k₁ (G w-y)))
    exact (mul_le_mul second (u.norm_coe_le_norm y) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have slice (w : E) : Integrable (fun y => f w y) ν := by
    apply (((integrable₁.comp_sub_left (G w)).norm).const_mul (‖g w‖*‖k₀‖*‖u‖)).mono'
      (by have : Continuous (fun y => f w y) := by dsimp [f]; fun_prop
          exact this.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (magnitude w)
  have innerBound (w : E) : (∫ y,‖f w y‖ ∂ν) ≤
      ‖g w‖*(‖k₀‖*‖u‖*(∫ y,‖k₁ y‖ ∂ν)) := by
    have estimate := integral_mono_ae (slice w).norm
      (((integrable₁.comp_sub_left (G w)).norm).const_mul (‖g w‖*‖k₀‖*‖u‖))
      (Filter.Eventually.of_forall (magnitude w))
    rw [integral_const_mul, integral_sub_left_eq_self (fun z => ‖k₁ z‖) ν (G w)] at estimate
    exact estimate.trans_eq (by ring)
  have integrableg := continuousg.integrable_of_hasCompactSupport compactg (μ := μ)
  have outer : Integrable (fun w => ∫ y,‖f w y‖ ∂ν) μ := by
    apply (integrableg.norm.mul_const (‖k₀‖*‖u‖*(∫ y,‖k₁ y‖ ∂ν))).mono'
      joint.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards with w
    have nonnegative : (0 : ℝ) ≤ ∫ y,‖f w y‖ ∂ν := integral_nonneg (fun y => norm_nonneg (f w y))
    change |∫ y,‖f w y‖ ∂ν| ≤ _
    rw [abs_of_nonneg nonnegative]
    exact innerBound w
  have integrable : Integrable f.uncurry (μ.prod ν) :=
    (integrable_prod_iff joint.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall slice,outer⟩
  calc
    _ = ∫ w,∫ y,f w y ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards with w
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      dsimp [f]
      ring
    _ = ∫ y,∫ w,f w y ∂μ ∂ν := integral_integral_swap integrable
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [←integral_mul_const]

end LeanShared.BoundedInputPhysicalKernelComposition
