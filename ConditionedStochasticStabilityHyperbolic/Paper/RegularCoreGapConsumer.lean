module

public import ConditionedStochasticStabilityHyperbolic.Paper.LocalProducedGaps
public import LeanShared.Geometry.RetainedRegularTests

/-! Specialize the two dual spaces before the actual Holder model appears.
This is the gap-retaining counterpart of RegularCoreLocalConsumer. -/

public noncomputable section
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularCoreGapConsumer
open LeanShared
variable {H W Reg X E Ω : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]

-- This private proof-valued definition retains the inferred theorem telescope.
set_option linter.defProp false in
private def consume
    (V : Set X) (B : TopologicalSpace.Opens X)
    (q : SmoothSupportedManifoldCore.core (E := E) V →ₗ[ℂ] Reg)
    (hBV : closure (B : Set X) ⊆ V) :=
  LocalConclusions.eventual_gaps_of_nofull_sources_and_qem_family
    (H := H) (W := W) (Z := Reg →L[ℂ] ℂ)
    (Zret := RetainedRegularTests.space B V q (subset_closure.trans hBV) →L[ℂ] ℂ)
    (Core := Reg) (X := X) (Ω := Ω)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularCoreGapConsumer
