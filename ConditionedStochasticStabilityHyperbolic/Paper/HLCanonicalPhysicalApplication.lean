module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ProducedPairCarriers
public import ConditionedStochasticStabilityHyperbolic.Paper.HLSelectedPhysicalInputs
public import ConditionedStochasticStabilityHyperbolic.Paper.HLBTBoundedSelectedSources
public import ConditionedStochasticStabilityHyperbolic.Paper.HLBoundedSelectedAnalyticPair
import all ConditionedStochasticStabilityHyperbolic.Paper.HLBoundedSelectedAnalyticPair

/-! The actual pair and its exact third carrier are constructed from ordinary
BT sources. The input below contains only the ordinary physical facts. -/
public noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 20000
open Set IsManifold MeasureTheory Filter Bundle
open scoped Manifold ContDiff BoundedContinuousFunction Topology NNReal ComplexConjugate
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLCanonicalPhysicalApplication
open LeanShared DyadicCompletion SmoothSupportedManifoldCore KellerLiverani1999
open PhysicalHolderClassicalSources.SourceData
universe uX

def Inputs
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
    : Type _ :=
  let classical := HLBTBoundedSelectedSources.Data.classical h
    (SmoothHolderTestSpaces.view u holder V) n d
  let pair := (HLBoundedSelectedAnalyticPair.Data.produced h
    (SmoothHolderTestSpaces.view u holder V) n classical).pair
  letI := ProducedAnnealedPair.weakNormed pair
  letI := ProducedAnnealedPair.weakSemi pair
  letI := ProducedAnnealedPair.weakScalar pair
  letI := ProducedAnnealedPair.weakUniform pair
  letI := ProducedAnnealedPair.weakComplete pair
  { c : HLSelectedPhysicalInputs.Data
      (Carrier := (HLBoundedSelectedAnalyticPair.intermediateModel h n).StrongSpace)
      (W := ProducedAnnealedPair.weakSpace pair)
      h u holder (HLBoundedSelectedAnalyticPair.strongModel h n)
      (HLBoundedSelectedAnalyticPair.intermediateModel h n) K hK hΛ hΛK
      d.maps d.laws d.representation w
      (HLBoundedSelectedAnalyticPair.Data.scale h
        (SmoothHolderTestSpaces.view u holder V) n classical)
      (HLBoundedSelectedAnalyticPair.Data.scale_positive h
        (SmoothHolderTestSpaces.view u holder V) n classical) σ //
    c.φ = φ }

end ConditionedStochasticStabilityHyperbolic.Paper.HLCanonicalPhysicalApplication
