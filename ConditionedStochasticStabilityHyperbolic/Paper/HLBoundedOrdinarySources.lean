module
public import ConditionedStochasticStabilityHyperbolic.Paper.HLPreDistortionPrimitiveSources
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedFixedCubeNoise
public noncomputable section
open Set IsManifold MeasureTheory Bundle
open scoped Manifold ContDiff SchwartzMap BigOperators Topology Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLBoundedOrdinarySources
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

/-- Ordinary sources at two physical models, before all stochastic deductions. -/
structure Data where
  view_identity : m.view = expectedView
  maps : Maps (E := E) (ι := ι) T h.r
  laws : Laws (ι := ι)
  representation : Representation maps Ω m.maps
  strong : HLPreDistortionPrimitiveSources.Data mStrong h (Order := Order)
  intermediate : HLPreDistortionPrimitiveSources.Data mIntermediate h (Order := Order)
  reference : representation.reference = strong.pressure.reference
  reference_intermediate : intermediate.pressure.reference = strong.pressure.reference
  normalizationFloor : ℝ := 0

end ConditionedStochasticStabilityHyperbolic.Paper.HLBoundedOrdinarySources
