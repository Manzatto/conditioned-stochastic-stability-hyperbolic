module
public import ConditionedStochasticStabilityHyperbolic.Paper.ComputedAnalyticInverseInputs

/-! Fully computed scalar/geometric ordinary layer source. Only genuine
regular-space bounds and interpolation for the actual inverse action remain;
all random plaques, inverse density, Jacobian identities and joint
continuities are produced internally on a positive noise window. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularLayerClassicalInputs
open Set MeasureTheory Measure IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle NNReal
open LeanShared RegularNoise HyperbolicBasicSet

set_option maxHeartbeats 3200000 in
def TestActionInputs.classicalInputs
    {E M ι Parameters Test TestCore : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [MetricSpace Parameters]
    [NormedAddCommGroup Test] [NormedSpace ℂ Test] [CompleteSpace Test]
    [AddCommGroup TestCore] [Module ℂ TestCore]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
    {evaluate : Parameters → M → M} (p : Representation F Parameters evaluate)
    {Λ V₀ V K G : Set M} (hK : IsCompact K) [CompactSpace K]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (w : M → ℝ) (continuousW : Continuous w) (nonnegativeW : ∀ x ∈ K, 0 ≤ w x)
    (positiveW : ∀ x ∈ closure G, 0 < w (T.symm x))
    (cutoff : M → ℝ) (cutoff_continuous : Continuous cutoff)
    (cutoff_support : Function.support cutoff ⊆ K) (cutoff_nonnegative : ∀ x, 0 ≤ cutoff x)
    (R : ℝ) (positiveR : 0 < R) (view : Test →ₗ[ℂ] (M → ℂ)) (inj : Function.Injective view)
    (qt : TestCore →ₗ[ℂ] Test) (J : InverseFamily F)
    (c : TestActionInputs J (FiniteSmoothReferenceCharts.canonicalData (E := E) (M := M)) cutoff view inj qt)
    (regularity : 1 ≤ r) (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (basic : BasicData (E := E) T Λ V₀) (core : isolatedCore T K ⊆ Λ)
    (openV : IsOpen V) (insideK : V ⊆ K) (containsV : Λ ⊆ V)
    (openG : IsOpen G) (containsG : Λ ⊆ G) :
    ClassicalInputs p (FiniteSmoothReferenceCharts.referenceMeasure (M := M) μ)
      V K G hK (fun x => w x.val) (fun x => cutoff x.val) R view inj qt :=
  (c.analyticInputs p hK (fun x => w x.val) cutoff cutoff_continuous cutoff_support cutoff_nonnegative
    R view inj qt J μ).produce μ w continuousW nonnegativeW positiveW positiveR J
      regularity deterministic inverse basic core openV insideK containsV openG containsG

end ConditionedStochasticStabilityHyperbolic.Paper.RegularLayerClassicalInputs
