module

public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedFixedCubeNoise
public import ConditionedStochasticStabilityHyperbolic.Paper.FixedCubeChains

/-! Exact process correspondence between the ordinary represented map family
used in completed transfer estimates and the paper's literal shrinking cube. -/

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
theorem actual_measurable (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ p.window) :
    Measurable (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1) := by
  have heq : (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1) =
      (fun z => F.fixedMap ε z.1 z.2) := funext fun z => p.actual_fixedMap ε hε hw z.1 z.2
  rw [heq]
  exact F.fixedMap_measurable ε hε (hw.trans p.window_le)

omit [FiniteDimensional ℝ E] in
theorem chain_literal_cube (L : Laws (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ p.window)
    (K : Set M) (hK : MeasurableSet K)
    (w : K → ℝ) (hwgt : Measurable w) (R : ℝ) (hR : 0 < R)
    (hwR : ∀ x, w x ≤ R) :
    RestrictedNoise.chain (L.fixedLaw ε)
      (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
      (p.actual_measurable ε hε hw) K hK w hwgt R hR hwR =
    RestrictedNoise.chain (L.law ε)
      (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
      (F.raw_measurable ε hε (hw.trans p.window_le)) K hK w hwgt R hR hwR := by
  have heq : (fun z : M × FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1) =
      (fun z => F.fixedMap ε z.1 z.2) := funext fun z => p.actual_fixedMap ε hε hw z.1 z.2
  simpa only [heq] using F.chain_fixed_cube L ε hε (hw.trans p.window_le) K hK w hwgt R hR hwR

end Representation
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
