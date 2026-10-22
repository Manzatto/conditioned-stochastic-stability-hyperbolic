module

public import ConditionedStochasticStabilityHyperbolic.Paper.FixedCubeNoise
public import ConditionedStochasticStabilityHyperbolic.Spectral.RestrictedNoise

/-! The rescaled and literal shrinking-cube models construct the same weighted
absorbing chain, hence the same path laws and quasi-ergodic statements. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]
  [MeasurableSpace M] [BorelSpace M] {T : M ≃ₜ M} {r : ℝ}
namespace Maps
variable (F : Maps (E := E) (ι := ι) T r)

omit [FiniteDimensional ℝ E] in
theorem chain_fixed_cube (L : Laws (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hwindow : ε ≤ F.window)
    (K : Set M) (hK : MeasurableSet K)
    (w : K → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R)
    (hwR : ∀ x, w x ≤ R) :
    RestrictedNoise.chain (L.fixedLaw ε)
      (fun z : M × FixedControl (ι := ι) => F.fixedMap ε z.1 z.2)
      (F.fixedMap_measurable ε hε hwindow) K hK w hw R hR hwR =
    RestrictedNoise.chain (L.law ε)
      (fun z : M × cube (ι := ι) ε => F.family ε z.2.val z.1)
      (F.raw_measurable ε hε hwindow) K hK w hw R hR hwR := by
  unfold RestrictedNoise.chain RestrictedNoise.liveKernel
  congr 1
  exact congrArg (fun P => SubtypeKernel.restrict P K hK)
    (F.transition_fixed_cube L ε hε hwindow)

end Maps
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
