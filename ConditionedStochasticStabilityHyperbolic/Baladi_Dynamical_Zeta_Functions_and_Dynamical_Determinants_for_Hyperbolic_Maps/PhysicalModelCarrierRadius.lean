module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarrierGenerator
public import ConditionedStochasticStabilityHyperbolic.Spectral.RadiusNontrivial
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldWeakening
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNormInstances

public noncomputable section
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

/- Seal the whole radius expression, including the canonical operator-ring
parents, while the ordinary regular test space remains abstract. -/
local instance radiusNormed : NormedAddCommGroup m.strongCarrier := m.strongCarrierNormed
local instance radiusSemi : SeminormedAddCommGroup m.strongCarrier := m.strongCarrierSemi
local instance radiusScalar : NormedSpace ℂ m.strongCarrier := m.strongCarrierScalar

def generatorRadius (a : Ω) : ENNReal := spectralRadius ℂ (m.carrierGenerator a)

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
theorem generatorRadius_positive_nontrivial (a : Ω) (positive : 0 < m.generatorRadius a) :
    Nontrivial m.strongCarrier :=
  nontrivial_of_positive_spectralRadius (m.carrierGenerator a) positive

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
