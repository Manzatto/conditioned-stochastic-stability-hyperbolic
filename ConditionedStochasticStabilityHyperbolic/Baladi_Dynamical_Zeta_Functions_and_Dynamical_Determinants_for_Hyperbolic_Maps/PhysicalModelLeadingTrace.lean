module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarrierLeading
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarrierComplete
public import ConditionedStochasticStabilityHyperbolic.Spectral.ConstructedRegularMultipliers

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

local instance traceNormed : NormedAddCommGroup m.strongCarrier := m.strongCarrierNormed
local instance traceSemi : SeminormedAddCommGroup m.strongCarrier := m.strongCarrierSemi
local instance traceScalar : NormedSpace ℂ m.strongCarrier := m.strongCarrierScalar
local instance traceUniform : UniformSpace m.strongCarrier := m.strongCarrierUniform
local instance traceComplete : CompleteSpace m.strongCarrier := m.strongCarrierComplete

namespace GeneratorLeading
/-- The literal deterministic multiplier pairing, with the physical completion
parents constructed while the ordinary regular space is abstract. -/
def multiplierTrace {a : Ω} (d : GeneratorLeading m a)
    (multiply : SmoothSupportedManifoldCore.core (E := E) V →ₗ[ℂ]
      SmoothSupportedManifoldCore.core (E := E) V) : ℝ :=
  (d.data.mean (ConstructedRegularMultipliers.analyticMultiplier
    (coreLift m.qa) multiply d.data.vector)).re
end GeneratorLeading
end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
