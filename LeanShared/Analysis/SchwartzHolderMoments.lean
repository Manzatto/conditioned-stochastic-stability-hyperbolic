module
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The fractional absolute moment of an actual Schwartz kernel is
finite. This discharges integrability in the Hölder cancellation estimate. -/
public noncomputable section
open MeasureTheory
open scoped SchwartzMap
namespace LeanShared.SchwartzHolderMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem integrable (k : 𝓢(E,ℂ)) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    Integrable (fun y => ‖k y‖ * ‖y‖ ^ a) μ := by
  have major := (k.integrable (μ := μ)).norm.add (k.integrable_pow_mul μ 1)
  have identity : ((fun y : E => ‖k y‖) + fun y => ‖y‖ ^ (1 : ℕ) * ‖k y‖) =
      (fun y => ‖k y‖ + ‖y‖ * ‖k y‖) := by
    funext y
    exact congrArg (fun r : ℝ => ‖k y‖ + r * ‖k y‖) (pow_one ‖y‖)
  rw [identity] at major
  apply major.mono'
  · exact (k.continuous.norm.mul
      (continuous_norm.rpow_const (fun _ => Or.inr ha.le))).aestronglyMeasurable
  · filter_upwards with y
    have power : ‖y‖ ^ a ≤ 1 + ‖y‖ := by
      by_cases small : ‖y‖ ≤ 1
      · exact (Real.rpow_le_one (norm_nonneg _) small ha.le).trans (by linarith [norm_nonneg y])
      · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge small) ha1
        exact (h.trans_eq (Real.rpow_one _)).trans (by linarith [norm_nonneg y])
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
    nlinarith [mul_le_mul_of_nonneg_left power (norm_nonneg (k y))]
end LeanShared.SchwartzHolderMoments
