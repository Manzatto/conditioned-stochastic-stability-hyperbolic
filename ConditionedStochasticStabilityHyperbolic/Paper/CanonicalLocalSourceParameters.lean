module
public import ConditionedStochasticStabilityHyperbolic.Paper.CanonicalLocalSources

public noncomputable section
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff NNReal
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

def maps : RegularNoise.Maps (E := E) (ι := ι) T h.r := d.classical.maps

def laws : RegularNoise.Laws (ι := ι) := d.classical.laws

def scale : ℝ := HLBoundedSelectedAnalyticPair.Data.scale h
  (SmoothHolderTestSpaces.view d.order d.smoothHolder V) d.model
  (HLBTBoundedSelectedSources.Data.classical h
    (SmoothHolderTestSpaces.view d.order d.smoothHolder V) d.model d.classical)

theorem scale_positive : 0 < d.scale :=
  HLBoundedSelectedAnalyticPair.Data.scale_positive h
    (SmoothHolderTestSpaces.view d.order d.smoothHolder V) d.model
    (HLBTBoundedSelectedSources.Data.classical h
      (SmoothHolderTestSpaces.view d.order d.smoothHolder V) d.model d.classical)

end ConditionedStochasticStabilityHyperbolic.Paper.CanonicalLocalSources
