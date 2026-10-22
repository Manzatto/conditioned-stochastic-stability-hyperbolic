module
public import ConditionedStochasticStabilityHyperbolic.Paper.HLCanonicalPhysicalApplication
import all ConditionedStochasticStabilityHyperbolic.Paper.HLCanonicalPhysicalApplication
public import ConditionedStochasticStabilityHyperbolic.Paper.HLSelectedPhysicalFamily
import all ConditionedStochasticStabilityHyperbolic.Paper.HLSelectedPhysicalConsumer
import all ConditionedStochasticStabilityHyperbolic.Paper.HLSelectedPhysicalGaps
import all ConditionedStochasticStabilityHyperbolic.Paper.HLBoundedSelectedAnalyticPair

public noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 20000
open Set IsManifold MeasureTheory Filter Bundle
open scoped Manifold ContDiff BoundedContinuousFunction Topology NNReal ComplexConjugate
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLCanonicalPhysicalApplication
open LeanShared DyadicCompletion SmoothSupportedManifoldCore KellerLiverani1999
open PhysicalHolderClassicalSources.SourceData
universe uX
private theorem stability_and_retention
  {M : Type uX} {E U AtlasIndex A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] [MetricSpace Ω]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ : Set M}
  (h : Paper.HL (E := E) T g Λ V)
  (u : ℝ)
  (holder : ∀ c : SmoothSupportedManifoldCore.core (E := E) (univ : Set M),
    ∃ C : ℝ, ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ u)
  (n : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex)
    (Reg := SmoothHolderTestSpaces.space u holder V)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  {ι Order : Type*} [Fintype ι] [Fintype Order]
  (d : HLBTBoundedSelectedSources.Data h (SmoothHolderTestSpaces.view u holder V) n
    (ι := ι) (Order := Order))
  (K : Set M) [CompactSpace K] (hK : IsCompact K)
  (hΛ : isolatedCore T K = Λ) (hΛK : Λ ⊆ K)
  (w : K → ℝ) (φ : M → ℝ)
  (σ : Measure M) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
  (c : Inputs h u holder n d K hK hΛ hΛK w φ σ) :
  ∃ (hw : Continuous w) (hwR : ∀ x, w x ≤ (HLBoundedSelectedAnalyticPair.Data.scale h (SmoothHolderTestSpaces.view u holder V) n
          (HLBTBoundedSelectedSources.Data.classical h (SmoothHolderTestSpaces.view u holder V) n d))),
    LocalConclusions.Stability d.maps d.laws K Λ hK.measurableSet w hw.measurable
      (HLBoundedSelectedAnalyticPair.Data.scale h (SmoothHolderTestSpaces.view u holder V) n
          (HLBTBoundedSelectedSources.Data.classical h (SmoothHolderTestSpaces.view u holder V) n d)) (HLBoundedSelectedAnalyticPair.Data.scale_positive h (SmoothHolderTestSpaces.view u holder V) n
          (HLBTBoundedSelectedSources.Data.classical h (SmoothHolderTestSpaces.view u holder V) n d)) hwR
      (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) ∧
    ∀ ν : ℝ≥0 → ProbabilityMeasure K,
      (∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), LocalConclusions.PointAt d.maps d.laws K Λ
        hK.measurableSet w hw.measurable (HLBoundedSelectedAnalyticPair.Data.scale h (SmoothHolderTestSpaces.view u holder V) n
          (HLBTBoundedSelectedSources.Data.classical h (SmoothHolderTestSpaces.view u holder V) n d)) (HLBoundedSelectedAnalyticPair.Data.scale_positive h (SmoothHolderTestSpaces.view u holder V) n
          (HLBTBoundedSelectedSources.Data.classical h (SmoothHolderTestSpaces.view u holder V) n d)) hwR (ν ε) ε) →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), LocalConclusions.NormalizedGapAt d.maps d.laws K Λ
        hK.measurableSet w hw.measurable (HLBoundedSelectedAnalyticPair.Data.scale h (SmoothHolderTestSpaces.view u holder V) n
          (HLBTBoundedSelectedSources.Data.classical h (SmoothHolderTestSpaces.view u holder V) n d)) (HLBoundedSelectedAnalyticPair.Data.scale_positive h (SmoothHolderTestSpaces.view u holder V) n
          (HLBTBoundedSelectedSources.Data.classical h (SmoothHolderTestSpaces.view u holder V) n d)) hwR (ν ε) ε := by
  let classical := HLBTBoundedSelectedSources.Data.classical h
    (SmoothHolderTestSpaces.view u holder V) n d
  let pair := (HLBoundedSelectedAnalyticPair.Data.produced h
    (SmoothHolderTestSpaces.view u holder V) n classical).pair
  let := ProducedAnnealedPair.weakNormed pair
  let := ProducedAnnealedPair.weakSemi pair
  let := ProducedAnnealedPair.weakScalar pair
  let := ProducedAnnealedPair.weakUniform pair
  let := ProducedAnnealedPair.weakComplete pair
  let ordinary := c.val
  have potential : ordinary.φ = φ := c.property
  have principalS := HLBoundedSelectedAnalyticPair.Data.strong_principal_lt_equilibrium h
    (SmoothHolderTestSpaces.view u holder V) n classical ordinary.equilibrium
  have principalH := HLBoundedSelectedAnalyticPair.Data.intermediate_principal_lt_equilibrium h
    (SmoothHolderTestSpaces.view u holder V) n classical ordinary.equilibrium
  have weak := HLBoundedSelectedAnalyticPair.Data.weakRates_ge_equilibrium h
    (SmoothHolderTestSpaces.view u holder V) n classical ordinary.equilibrium
  have stability := HLSelectedPhysicalInputs.consume h u holder
    (HLBoundedSelectedAnalyticPair.strongModel h n)
    (HLBoundedSelectedAnalyticPair.intermediateModel h n)
    K hK hΛ hΛK d.maps d.laws d.representation w
    (HLBoundedSelectedAnalyticPair.Data.scale h (SmoothHolderTestSpaces.view u holder V) n classical)
    (HLBoundedSelectedAnalyticPair.Data.scale_positive h (SmoothHolderTestSpaces.view u holder V) n classical)
    σ ordinary _ _ pair principalS principalH weak.1 weak.2
  have retention (ν : ℝ≥0 → ProbabilityMeasure K) :=
    HLSelectedPhysicalInputs.retain_gaps h u holder
      (HLBoundedSelectedAnalyticPair.strongModel h n)
      (HLBoundedSelectedAnalyticPair.intermediateModel h n)
      K hK hΛ hΛK d.maps d.laws d.representation w
      (HLBoundedSelectedAnalyticPair.Data.scale h (SmoothHolderTestSpaces.view u holder V) n classical)
      (HLBoundedSelectedAnalyticPair.Data.scale_positive h (SmoothHolderTestSpaces.view u holder V) n classical)
      σ ordinary _ _ pair principalH weak.2 ν
  refine ⟨ordinary.hw, ordinary.hwR, ?_, ?_⟩
  · exact potential ▸ stability
  · exact fun ν points => retention ν points
end ConditionedStochasticStabilityHyperbolic.Paper.HLCanonicalPhysicalApplication
