module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldModel
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNormInstances

/-! Recover the exact regular test-space structures already used in a physical model. -/
@[expose] public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
open LeanShared DyadicCompletion
variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]

namespace Data
variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]

/-- Project the regular test-space dictionary already carried by the model. -/
@[instance_reducible] def regularNormedParent (_model : Data (E := E) (U := U) (M := M)
    (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg)
    (A := A) (Ω := Ω) V S μ) : NormedAddCommGroup Reg := inferInstance

@[instance_reducible] def regularSeminormedParent (_model : Data (E := E) (U := U) (M := M)
    (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg)
    (A := A) (Ω := Ω) V S μ) : SeminormedAddCommGroup Reg := inferInstance

@[instance_reducible] def regularScalarParent (_model : Data (E := E) (U := U) (M := M)
    (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg)
    (A := A) (Ω := Ω) V S μ) : NormedSpace ℂ Reg := inferInstance

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
