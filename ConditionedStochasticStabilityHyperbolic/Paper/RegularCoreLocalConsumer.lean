module

public import ConditionedStochasticStabilityHyperbolic.Paper.HLNoFullSupportLocalStability
public import LeanShared.Geometry.RetainedRegularTests

/-! Instantiate the two dual spaces while the regular core is abstract.
Specializing this checked consumer avoids re-synthesizing nested closed-core
scalar dictionaries at the concrete physical application boundary. -/
public noncomputable section
open Set MeasureTheory Bundle IsManifold
open scoped Manifold ContDiff Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularCoreLocalConsumer
open LeanShared
variable {S H W Reg X E Parameters ι : Type*}
  [NormedAddCommGroup S] [NormedSpace ℂ S] [CompleteSpace S]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [MetricSpace Parameters] [Fintype ι]
  {evaluate : Parameters → X → X} {g : X → ℝ} {Λ : Set X}

-- The inferred result is a proof-valued partially applied theorem; keeping the
-- type inferred avoids expanding the concrete dual-space dictionaries.
set_option linter.defProp false in
private def consume
    (V : Set X) (B : TopologicalSpace.Opens X)
    (q : SmoothSupportedManifoldCore.core (E := E) V →ₗ[ℂ] Reg)
    (hBV : closure (B : Set X) ⊆ V) :=
  HLNoFullSupportProducedLocalStability.stability_from_produced_pair
    (S := S) (H := H) (W := W)
    (Z := Reg →L[ℂ] ℂ)
    (Zret := RetainedRegularTests.space B V q (subset_closure.trans hBV) →L[ℂ] ℂ)
    (Core := Reg) (X := X) (E := E) (Parameters := Parameters) (ι := ι)
    (evaluate := evaluate) (g := g) (Λ := Λ)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularCoreLocalConsumer
