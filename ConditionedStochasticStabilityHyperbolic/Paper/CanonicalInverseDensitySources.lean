module
public import ConditionedStochasticStabilityHyperbolic.Paper.ComputedInverseDensityWeights
public import LeanShared.Geometry.CanonicalSmoothReferenceMeasure

/-! Source-free scalar Jacobian and inverse plaque assembly for the
constructed smooth reference. Only literal regular noise, deterministic
hyperbolicity, compact isolation and ordinary weight geometry remain. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set MeasureTheory Measure IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle NNReal

set_option maxHeartbeats 3200000 in
def InverseFamily.canonicalDensityWeights
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
    (J : InverseFamily F) (μ : Measure E) [IsAddHaarMeasure μ]
    (K G : Set M) (measurableK : MeasurableSet K)
    (w : M → ℝ) (continuousW : Continuous w) (nonnegativeW : ∀ x ∈ K, 0 ≤ w x)
    (positiveW : ∀ x ∈ closure G, 0 < w (T.symm x)) (R : ℝ) (positiveR : 0 < R) :
    InverseDensityWeights J (LeanShared.FiniteSmoothReferenceCharts.referenceMeasure (M := M) μ)
      K G (fun x => w x.val) R :=
  J.densityWeights LeanShared.FiniteSmoothReferenceCharts.canonicalData μ
    K G measurableK w continuousW nonnegativeW positiveW R positiveR

set_option maxHeartbeats 3200000 in
def InverseFamily.canonicalDensitySources
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Fintype ι]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
    {Λ V₀ V K G : Set M}
    (J : InverseFamily F) (μ : Measure E) [IsAddHaarMeasure μ]
    (w : M → ℝ) (continuousW : Continuous w) (nonnegativeW : ∀ x ∈ K, 0 ≤ w x)
    (positiveW : ∀ x ∈ closure G, 0 < w (T.symm x)) (R : ℝ) (positiveR : 0 < R)
    (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (basic : LeanShared.HyperbolicBasicSet.BasicData (E := E) T Λ V₀)
    (compactK : IsCompact K) (core : LeanShared.isolatedCore T K ⊆ Λ)
    (openV : IsOpen V) (insideK : V ⊆ K) (containsV : Λ ⊆ V)
    (openG : IsOpen G) (containsG : Λ ⊆ G) :
    InverseDensityOrdinarySources F
      (LeanShared.FiniteSmoothReferenceCharts.referenceMeasure (M := M) μ)
      V K G (fun x => w x.val) R :=
  (J.canonicalDensityWeights μ K G compactK.measurableSet w continuousW nonnegativeW
    positiveW R positiveR).produce regularity deterministic inverse basic compactK core
      openV insideK containsV openG containsG

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
