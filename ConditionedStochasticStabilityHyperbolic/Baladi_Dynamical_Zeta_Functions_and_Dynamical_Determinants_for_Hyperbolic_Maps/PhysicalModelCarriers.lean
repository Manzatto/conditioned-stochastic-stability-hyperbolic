module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelStrongParents
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldWeakening
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNormInstances

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
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

/-- Seal the type coercion while the regular test space is abstract. -/
abbrev strongCarrier : Type _ := m.StrongSpace

abbrev weakCarrier : Type _ := closedCore
  (m.loweredCore m.lossW m.lossW_positive m.extraW m.extraW_nonnegative)

@[instance_reducible] def strongCarrierNormed : NormedAddCommGroup m.strongCarrier :=
  m.strongNormedParent
@[instance_reducible] def strongCarrierSemi : SeminormedAddCommGroup m.strongCarrier :=
  m.strongSeminormedParent
@[instance_reducible] def strongCarrierScalar :
    letI := m.strongCarrierSemi
    NormedSpace ℂ m.strongCarrier := m.strongScalarParent

@[instance_reducible] def weakCarrierNormed : NormedAddCommGroup m.weakCarrier := inferInstance
@[instance_reducible] def weakCarrierSemi : SeminormedAddCommGroup m.weakCarrier :=
  m.weakCarrierNormed.toSeminormedAddCommGroup
@[instance_reducible] def weakCarrierScalar :
    letI := m.weakCarrierSemi
    NormedSpace ℂ m.weakCarrier := by
  letI := m.weakCarrierSemi
  infer_instance

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
