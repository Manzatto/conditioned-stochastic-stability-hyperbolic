module
public import ConditionedStochasticStabilityHyperbolic.Paper.PrescribedAdaptedLocalApplication
import all ConditionedStochasticStabilityHyperbolic.Paper.PrescribedAdaptedLocalApplication
import all ConditionedStochasticStabilityHyperbolic.Paper.CanonicalLocalSourceParameters

public noncomputable section
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.PrescribedAdaptedLocalSources
open LeanShared RegularNoise PhysicalHolderClassicalSources.SourceData
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
  {V V0 S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  {T : M ≃ₜ M} {g g0 : M → ℝ} {Λ : Set M}
  (h : HL (E := E) T g Λ V) (outer : HL (E := E) T g0 Λ V0) (ambient : M → ℝ)
  (setup : AdaptedLocalWeightSetup.Data outer ambient V)
  {ι Order : Type*} [Fintype ι] [Fintype Order]
  (P : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι))
  [CompactSpace (closure V0)] (hΛK : Λ ⊆ closure V0)
  (σ : Measure M) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
  (d : Data (U := U) (AtlasIndex := AtlasIndex) (A := A) (Ω := Ω)
    (LocalReg := LocalReg) (S := S) (μ := μ) (Order := Order)
    h outer ambient setup P L hΛK σ)

  (φ : M → ℝ) (hφ : ∀ x ∈ Λ, g x = Real.exp (φ x))
  (hVV0 : V ⊆ V0) (hw : Continuous ambient)
  (hwn : ∀ x ∈ closure V0, 0 ≤ ambient x)

private theorem canonical_maps : (canonical h outer ambient setup P L hΛK σ d φ hφ hVV0 hw hwn).maps = P := rfl

private theorem canonical_laws : (canonical h outer ambient setup P L hΛK σ d φ hφ hVV0 hw hwn).laws = L := rfl

private theorem canonical_bound (x : M) :
    ambient x ≤ (canonical h outer ambient setup P L hΛK σ d φ hφ hVV0 hw hwn).scale := by
  exact (d.floor x).trans (HLBoundedSelectedAnalyticPair.Data.scale_ge_floor h
    (SmoothHolderTestSpaces.view d.order d.smoothHolder V) d.model
    (HLBTBoundedSelectedSources.Data.classical h
      (SmoothHolderTestSpaces.view d.order d.smoothHolder V) d.model
      (d.bt.ordinary d.model h (HLBTBoundedSelectedSources.strongModel h d.model)
        (HLBTBoundedSelectedSources.intermediateModel h d.model)
        (SmoothHolderTestSpaces.view d.order d.smoothHolder V))))

end ConditionedStochasticStabilityHyperbolic.Paper.PrescribedAdaptedLocalSources
