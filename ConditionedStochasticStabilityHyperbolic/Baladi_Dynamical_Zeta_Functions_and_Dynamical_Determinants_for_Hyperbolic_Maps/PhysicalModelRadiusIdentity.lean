module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarrierRadius

import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarrierRadius
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarrierGenerator

/-! The sealed deterministic radius is exactly the ordinary spectral radius
of the literal physical generator. The parent conversion is checked while
the regular test space remains abstract. -/
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


omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
private theorem generatorRadius_eq_native_private (a : Ω) :
    m.generatorRadius a = spectralRadius ℂ (m.generator a) := rfl

omit [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
/-- This identity changes neither the generator nor its operator-ring norm. -/
theorem generatorRadius_eq_native (a : Ω) :
    m.generatorRadius a = spectralRadius ℂ (m.generator a) :=
  generatorRadius_eq_native_private m a

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
