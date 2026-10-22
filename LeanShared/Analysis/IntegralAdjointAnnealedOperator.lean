module

public import LeanShared.Geometry.SupportedRegularPairing
public import LeanShared.Analysis.AdjointAnnealedOperator
public import Mathlib.MeasureTheory.Integral.Prod

/-! Ordinary scalar change of variables and Fubini construct the common
ambient transpose for actual killed averages. Individual killed maps need
not act continuously on all continuous functions on the closed live set. -/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace LeanShared.IntegralAdjointAnnealedOperator
variable {X Ω Test : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace Ω] [NormedAddCommGroup Test] [NormedSpace ℂ Test] [CompleteSpace Test]
  (σ : Measure X) [IsFiniteMeasure σ] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (physical : Test →L[ℂ] (X →ᵇ ℂ))
  (Q : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ))
  (raw : Ω → (X →ᵇ ℂ) → X → ℂ)
  (measurableRaw : ∀ f, Measurable (fun p : X × Ω => raw p.2 f p.1))
  (M : ℝ) (hM : 0 ≤ M) (boundRaw : ∀ ω f x, ‖raw ω f x‖ ≤ M * ‖f‖)
  (forward : ∀ f x, Q f x = ∫ ω, raw ω f x ∂μ)
  (J : Ω → Test →L[ℂ] Test)
  (measurableJ : ∀ v, AEStronglyMeasurable (fun ω => J ω v) μ)
  (MJ : ℝ) (boundJ : ∀ ω, ‖J ω‖ ≤ MJ)

include measurableRaw hM boundRaw forward in
theorem pairing_intertwining
    (changeVariables : ∀ ω f v,
      (∫ x, raw ω f x * physical v x ∂σ) =
        ∫ x, f x * physical (J ω v) x ∂σ) :
    (SupportedRegularPairing.embedding σ physical).comp Q =
      (AdjointAnnealedOperator.transpose
        (AnnealedOperatorBounds.pointwiseAnnealed μ J measurableJ MJ boundJ)).comp
        (SupportedRegularPairing.embedding σ physical) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ContinuousLinearMap.ext
  intro v
  have hint : Integrable
      (fun p : X × Ω => raw p.2 f p.1 * physical v p.1) (σ.prod μ) := by
    apply Integrable.of_bound
      ((measurableRaw f).mul ((physical v).continuous.measurable.comp measurable_fst)).aestronglyMeasurable
      (M * ‖f‖ * ‖physical v‖)
    exact Filter.Eventually.of_forall fun p => by
      change ‖raw p.2 f p.1 * physical v p.1‖ ≤ M * ‖f‖ * ‖physical v‖
      rw [norm_mul]
      exact mul_le_mul (boundRaw p.2 f p.1) ((physical v).norm_coe_le_norm p.1)
        (norm_nonneg _) (mul_nonneg hM (norm_nonneg f))
  change (∫ x, Q f x * physical v x ∂σ) =
    SupportedRegularPairing.embedding σ physical f
      (AnnealedOperatorBounds.pointwiseAnnealed μ J measurableJ MJ boundJ v)
  calc
    _ = ∫ x, ∫ ω, raw ω f x * physical v x ∂μ ∂σ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change Q f x * physical v x = ∫ ω, raw ω f x * physical v x ∂μ
        rw [forward]
        exact (integral_mul_const (physical v x) (fun ω => raw ω f x)).symm
    _ = ∫ ω, ∫ x, raw ω f x * physical v x ∂σ ∂μ := integral_integral_swap hint
    _ = ∫ ω, SupportedRegularPairing.embedding σ physical f (J ω v) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => changeVariables ω f v
    _ = _ := (SupportedRegularPairing.embedding σ physical f).integral_comp_comm
      (AnnealedOperatorBounds.random_apply_integrable μ J measurableJ MJ boundJ v)

end LeanShared.IntegralAdjointAnnealedOperator
