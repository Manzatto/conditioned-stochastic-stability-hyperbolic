module

public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedAllScaleMaps
public import ConditionedStochasticStabilityHyperbolic.Spectral.NoiseKernel

/-! Exact equality of ambient canonical chains for represented fixed-cube
noise and the original shrinking-cube noise, including the absorbing states. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι Parameters : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] [MetricSpace Parameters]
  {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
  {evaluate : Parameters → M → M}
namespace Representation
variable (p : Representation F Parameters evaluate)

omit [FiniteDimensional ℝ E] in
/-- Equality of the complete ambient killed process, before restricting its
starting states or selecting observables. -/
theorem global_chain_literal_cube (L : Laws (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ p.window)
    (K : Set M) (hK : MeasurableSet K)
    (w : M → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R)
    (hwR : ∀ x, w x ≤ R) :
    NoiseKernel.chain (L.fixedLaw ε)
      (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
      (p.allScale_measurable ε) K hK w hw R hR hwR =
    NoiseKernel.chain (L.law ε)
      (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
      (F.raw_measurable ε hε (hwindow.trans p.window_le)) K hK w hw R hR hwR := by
  have heq : (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1) =
      (fun z => F.fixedMap ε z.1 z.2) :=
    funext fun z => p.actual_fixedMap ε hε hwindow z.1 z.2
  unfold NoiseKernel.chain
  congr 1
  simpa only [heq] using F.killed_fixed_cube L ε hε (hwindow.trans p.window_le) K hK

end Representation
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
