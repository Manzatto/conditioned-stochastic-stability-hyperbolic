module

public import ConditionedStochasticStabilityHyperbolic.Paper.HLPreControlPressureSources
import all ConditionedStochasticStabilityHyperbolic.Paper.HLPreControlPressureSources

/-! Exact reference and equilibrium metadata for the constructed faithful pre-control source. -/

public noncomputable section
open Set IsManifold MeasureTheory Filter Bundle
open scoped Manifold ContDiff SchwartzMap BigOperators Topology Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLPreControlPressureSources
open LeanShared HyperbolicBasicSet
open HLPhysicalPressureSources
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



namespace Data
variable (p : Data m h)

omit [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
private theorem constructed_reference_aux : (p.constructed m h).reference = p.reference := rfl

omit [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
theorem constructed_reference : (p.constructed m h).reference = p.reference :=
  constructed_reference_aux m h p

omit [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
private theorem constructed_equilibrium_aux : (p.constructed m h).equilibrium = p.equilibrium := rfl

omit [CompactSpace M] [∀ k, CompleteSpace (LocalReg k)] [BorelSpace M] in
theorem constructed_equilibrium : (p.constructed m h).equilibrium = p.equilibrium :=
  constructed_equilibrium_aux m h p

end Data
end ConditionedStochasticStabilityHyperbolic.Paper.HLPreControlPressureSources
