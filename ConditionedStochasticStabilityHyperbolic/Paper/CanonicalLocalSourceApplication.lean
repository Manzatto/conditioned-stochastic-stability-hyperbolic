module
public import ConditionedStochasticStabilityHyperbolic.Paper.CanonicalLocalSourceParameters
import all ConditionedStochasticStabilityHyperbolic.Paper.CanonicalLocalSourceParameters
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalStableGapWindow
import all ConditionedStochasticStabilityHyperbolic.Paper.HLCanonicalPhysicalFamily

/-! Applying the ordinary source record constructs both the literal local
stability theorem and retention of its exact probability's normalized gap. -/
public noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 20000
open Set IsManifold MeasureTheory Bundle Filter
open scoped Manifold ContDiff NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.CanonicalLocalSources
open LeanShared
universe uX
variable
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
  {h : HL (E := E) T g Λ V}
  {ι Order : Type*} [Fintype ι] [Fintype Order]
  {K : Set M} [CompactSpace K] {hK : IsCompact K}
  {hΛ : isolatedCore T K = Λ} {hΛK : Λ ⊆ K}
  {w : K → ℝ} {φ : M → ℝ}
  {σ : Measure M} [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
  (d : CanonicalLocalSources (U := U) (AtlasIndex := AtlasIndex) (A := A) (Ω := Ω)
    (LocalReg := LocalReg) (S := S) (μ := μ) (ι := ι) (Order := Order)
    h K hK hΛ hΛK w φ σ)

private theorem stability_and_retention :
  ∃ (hw : Continuous w) (bound : ∀ x, w x ≤ d.scale),
    LocalConclusions.Stability d.maps d.laws K Λ hK.measurableSet w hw.measurable
      d.scale d.scale_positive bound
      (fun x => φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) ∧
    ∀ ν : ℝ≥0 → ProbabilityMeasure K,
      (∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), LocalConclusions.PointAt d.maps d.laws K Λ
        hK.measurableSet w hw.measurable d.scale d.scale_positive bound (ν ε) ε) →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), LocalConclusions.NormalizedGapAt d.maps d.laws K Λ
        hK.measurableSet w hw.measurable d.scale d.scale_positive bound (ν ε) ε := by
  exact HLCanonicalPhysicalApplication.stability_and_retention h d.order d.smoothHolder
    d.model d.classical K hK hΛ hΛK w φ σ d.physical

end ConditionedStochasticStabilityHyperbolic.Paper.CanonicalLocalSources
