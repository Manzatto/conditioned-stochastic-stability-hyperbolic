module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ComplexRestrictedNoiseIntegral
public import LeanShared.Analysis.IntegralAdjointAnnealedOperator
import Mathlib.Tactic.FieldSimp

/-! Scalar ordinary Jacobian identities produce the actual cutoff adjoint.
Individual killed maps need not define continuous operators on all C0(K).
Joint measurability and bounds follow directly from the noise map and weight. -/
@[expose] public noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ActualCutoffAdjoint
variable {M Ω Test : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Ω] [NormedAddCommGroup Test] [NormedSpace ℂ Test] [CompleteSpace Test]
  (K : Set M) (hK : MeasurableSet K)
  (F : M × Ω → M) (hF : Measurable F) (w : K → ℝ) (hw : Measurable w)

def raw (ω : Ω) (f : K →ᵇ ℂ) (x : K) : ℂ :=
  (w x : ℂ) * ComplexStrongFeller.zeroExtend K f (F (x.val, ω))

include hK hF hw in
theorem raw_measurable (f : K →ᵇ ℂ) :
    Measurable (fun p : K × Ω => raw K F w p.2 f p.1) := by
  exact ((Complex.continuous_ofReal.measurable.comp hw).comp measurable_fst).mul
    ((ComplexStrongFeller.measurable_zeroExtend K hK f f.continuous.measurable).comp
      (hF.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)))

omit [MeasurableSpace M] [BorelSpace M] [MeasurableSpace Ω] in
theorem raw_bound (R : ℝ) (hw0 : ∀ x, 0 ≤ w x) (hwR : ∀ x, w x ≤ R)
    (ω : Ω) (f : K →ᵇ ℂ) (x : K) : ‖raw K F w ω f x‖ ≤ R * ‖f‖ := by
  rw [raw, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 x)]
  exact mul_le_mul (hwR x)
    (ComplexStrongFeller.norm_zeroExtend_le K f (norm_nonneg f) f.norm_coe_le_norm _)
    (norm_nonneg _) ((hw0 x).trans (hwR x))

variable (ρ : Measure Ω) [IsProbabilityMeasure ρ]
  (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
  (sf : HasStrongFellerKernel (RestrictedNoise.chain ρ F hF K hK w hw R hR hwR))

theorem raw_average (hw0 : ∀ x, 0 ≤ w x) (f : K →ᵇ ℂ) (x : K) :
    ((R : ℂ) • ComplexStrongFeller.transferOperator
      (RestrictedNoise.chain ρ F hF K hK w hw R hR hwR) sf) f x =
      ∫ ω, raw K F w ω f x ∂ρ := by
  change (R : ℂ) * (∫ y, f y ∂(RestrictedNoise.chain ρ F hF K hK w hw R hR hwR).killedTransition x) = _
  rw [RestrictedNoise.integral_chain_complex ρ F hF K hK w hw hw0 R hR hwR
      f f.continuous.measurable x]
  simp only [raw]
  rw [integral_const_mul, Complex.real_smul]
  push_cast
  field_simp [hR.ne']

theorem pairing_intertwining
    (hw0 : ∀ x, 0 ≤ w x) (σ : Measure K) [IsFiniteMeasure σ]
    (physical : Test →L[ℂ] (K →ᵇ ℂ))
    (J : Ω → Test →L[ℂ] Test)
    (measurableJ : ∀ v, AEStronglyMeasurable (fun ω => J ω v) ρ)
    (MJ : ℝ) (boundJ : ∀ ω, ‖J ω‖ ≤ MJ)
    (changeVariables : ∀ ω f v,
      (∫ x, raw K F w ω f x * physical v x ∂σ) =
        ∫ x, f x * physical (J ω v) x ∂σ) :
    (LeanShared.SupportedRegularPairing.embedding σ physical).comp
      ((R : ℂ) • ComplexStrongFeller.transferOperator
        (RestrictedNoise.chain ρ F hF K hK w hw R hR hwR) sf) =
      (LeanShared.AdjointAnnealedOperator.transpose
        (LeanShared.AnnealedOperatorBounds.pointwiseAnnealed ρ J measurableJ MJ boundJ)).comp
        (LeanShared.SupportedRegularPairing.embedding σ physical) :=
  LeanShared.IntegralAdjointAnnealedOperator.pairing_intertwining σ ρ physical _
    (raw K F w) (raw_measurable K hK F hF w hw) R hR.le
    (raw_bound K F w R hw0 hwR) (raw_average K hK F hF w hw ρ R hR hwR sf hw0)
    J measurableJ MJ boundJ changeVariables

end ConditionedStochasticStabilityHyperbolic.ActualCutoffAdjoint
