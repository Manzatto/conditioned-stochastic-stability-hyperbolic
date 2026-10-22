module
public import ConditionedStochasticStabilityHyperbolic.Paper.HLBTBoundedOrdinarySources

public noncomputable section
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLBTPrescribedNoiseSources
open LeanShared Paper.RegularNoise
variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*}
  [∀ k, NormedAddCommGroup (LocalReg k)] [∀ k, NormedSpace ℂ (LocalReg k)]
  [∀ k, CompleteSpace (LocalReg k)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
variable [MetricSpace Ω]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ : Set M}
  (h : Paper.HL (E := E) T g Λ V)
  {Order ι : Type*} [Fintype Order] [Fintype ι]

variable (mStrong mIntermediate : PhysicalManifoldModel.Data (E := E) (U := U)
  (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg)
  (A := A) (Ω := Ω) V S μ) (expectedView : Reg → M → ℂ)

/-- The maps and the varying laws are prescribed literal data, rather than
free fields requiring a later process-matching hypothesis. Every stored field
is an ordinary geometric, analytic or fixed-map BT source. -/
structure Data (P : Maps (E := E) (ι := ι) T h.r) (L : Laws (ι := ι)) where
  view_identity : m.view = expectedView
  representation : Representation P Ω m.maps
  strong : HLBTPreDistortionPrimitiveSources.Data mStrong h (Order := Order)
  intermediate : HLBTPreDistortionPrimitiveSources.Data mIntermediate h (Order := Order)
  reference : representation.reference = strong.pressure.reference
  reference_intermediate : intermediate.pressure.reference = strong.pressure.reference
  normalizationFloor : ℝ := 0

namespace Data
variable {P : Maps (E := E) (ι := ι) T h.r} {L : Laws (ι := ι)}
  (d : Data m h mStrong mIntermediate expectedView P L (Order := Order))

@[expose] def ordinary : HLBTBoundedOrdinarySources.Data m h mStrong mIntermediate
    expectedView (Order := Order) (ι := ι) where
  view_identity := d.view_identity
  maps := P
  laws := L
  representation := d.representation
  strong := d.strong
  intermediate := d.intermediate
  reference := d.reference
  reference_intermediate := d.reference_intermediate
  normalizationFloor := d.normalizationFloor

end Data
end ConditionedStochasticStabilityHyperbolic.Paper.HLBTPrescribedNoiseSources
