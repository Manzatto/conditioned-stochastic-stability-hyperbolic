module

public import ConditionedStochasticStabilityHyperbolic.Spectral.RegularAveragePhysicalTransfer
public import LeanShared.Analysis.InvariantFiniteRegularTransfer

/-! Both realizations of the actual regular averaged transfer. The analytic
law is extended from literal smooth functions; the physical law is derived
from the actual killed kernel. Noise laws are arbitrary at each scale. -/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ActualInvariantCoreAverage
open LeanShared InvariantFiniteRegularTransfer

variable {Reg H Core X Ω : Type*}
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompleteSpace Reg]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]
  (ρ : Measure Ω) [IsProbabilityMeasure ρ]
  (view : Reg →ₗ[ℂ] (X → ℂ)) (hview : Function.Injective view)
  (F : Ω → X → X) (g : X → ℝ)
  (hregular : ∀ a f, FiniteRegularTransferRealization.weightedComposition (F a) g (view f) ∈ view.range)
  (CR : ℝ) (hCR : 0 ≤ CR)
  (hbound : ∀ a f, ‖action view hview F g hregular a f‖ ≤ CR * ‖f‖)
  (hmeas : ∀ f, AEStronglyMeasurable
    (fun a => operator view hview F g hregular CR hbound a f) ρ)
  (smooth : Core → Reg) (dense : DenseRange smooth)
  (realize : Reg →L[ℂ] H) (P : Ω → H →L[ℂ] H)
  (hPmeas : ∀ f, AEStronglyMeasurable (fun a => P a f) ρ)
  (CP : ℝ) (hPbound : ∀ a, ‖P a‖ ≤ CP)
  (hcore : ∀ a c, realize (action view hview F g hregular a (smooth c)) = P a (realize (smooth c)))
  (K : Set X) (hK : MeasurableSet K)
  (hF : Measurable (fun z : X × Ω => F z.2 z.1))
  (w : K → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
  (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
  (hweight : ∀ x : K, g x.val = w x)
  (hSF : HasStrongFellerKernel
    (RestrictedNoise.chain ρ (fun z => F z.2 z.1) hF K hK w hw R hR hwR))
  (physical : Reg →L[ℂ] (K →ᵇ ℂ))
  (hphysical : ∀ v (x : K), physical v x = view v x.val)
  (hzero : ∀ v x, x ∉ K → view v x = 0)

include dense hcore hw0 hphysical hzero hweight in
/-- The common regular action is a constructed averaged weighted composition;
its normalization realizes both the analytic and actual killed operators. -/
theorem normalized_realizations :
    realize.comp (((R⁻¹ : ℝ) : ℂ) • average view hview F g hregular CR hbound ρ hmeas hCR) =
      (((R⁻¹ : ℝ) : ℂ) • AnnealedOperatorBounds.pointwiseAnnealed ρ P hPmeas CP hPbound).comp realize ∧
    physical.comp (((R⁻¹ : ℝ) : ℂ) • average view hview F g hregular CR hbound ρ hmeas hCR) =
      (ComplexStrongFeller.transferOperator (𝕜 := ℂ)
        (RestrictedNoise.chain ρ (fun z => F z.2 z.1) hF K hK w hw R hR hwR) hSF).comp physical := by
  constructor
  · have hh := average_intertwining view hview F g hregular CR hbound smooth dense
      realize P ρ hmeas hCR hPmeas CP hPbound hcore
    apply ContinuousLinearMap.ext
    intro v
    simpa only [ContinuousLinearMap.comp_apply, smul_apply, map_smul] using
      congrArg (((R⁻¹ : ℝ) : ℂ) • ·) (congrArg (fun T : Reg →L[ℂ] H => T v) hh)
  · apply RegularAveragePhysicalTransfer.average_intertwining ρ
      (fun z => F z.2 z.1) hF K hK w hw hw0 R hR hwR hSF view physical hphysical hzero
      (operator view hview F g hregular CR hbound) hmeas CR
      (operator_norm_le view hview F g hregular CR hbound hCR)
    intro a v x
    rw [operator_function, hweight]

end ConditionedStochasticStabilityHyperbolic.ActualInvariantCoreAverage
