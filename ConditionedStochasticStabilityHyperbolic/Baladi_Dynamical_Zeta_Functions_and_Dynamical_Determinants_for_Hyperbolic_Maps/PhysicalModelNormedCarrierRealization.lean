module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarrierRealization
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarrierComplete
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarrierRadius

/-! Native realizations with a single normed-group parent. This aligns the
carrier dictionaries with generic Banach-space theorems before the regular
space is specialized, avoiding repeated definitional comparisons between
two inherited seminormed parents of the nested completion. -/

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
  [TopologicalSpace M] [ChartedSpace E M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]

namespace Data
variable (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex)
  (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

local instance normedCarrierParent : NormedAddCommGroup m.strongCarrier := m.strongCarrierNormed

@[instance_reducible] def normedCarrierScalar : NormedSpace ℂ m.strongCarrier :=
  m.strongCarrierScalar

local instance normedCarrierScalarInstance : NormedSpace ℂ m.strongCarrier := m.normedCarrierScalar

omit [∀ i, CompleteSpace (LocalReg i)] in
theorem normedCarrierComplete : CompleteSpace m.strongCarrier := m.strongCarrierComplete

def normedCarrierCore : SmoothSupportedManifoldCore.core (E := E) V →ₗ[ℂ] m.strongCarrier :=
  coreLift m.qa

def normedCarrierRealize : Reg →L[ℂ] m.strongCarrier := m.realize

def normedCarrierGenerator (a : Ω) : m.strongCarrier →L[ℂ] m.strongCarrier := m.generator a

theorem normedCarrierRealize_core (c : SmoothSupportedManifoldCore.core (E := E) V) :
    m.normedCarrierRealize (m.regularCore c) = m.normedCarrierCore c := m.realize_core c

theorem normedCarrierGenerator_regular_intertwining
    (rows : PhysicalManifoldRowSources.Data m) (a : Ω) :
    m.normedCarrierRealize.comp (InvariantFiniteRegularTransfer.operator m.view m.view_injective
      m.maps m.weight m.invariant m.regularConstant m.regularBound a) =
      (m.normedCarrierGenerator a).comp m.normedCarrierRealize :=
  m.generator_regular_intertwining rows a

theorem generatorRadius_lower_of_normedCarrier (a : Ω) (r : ℝ)
    (bound : ENNReal.ofReal r ≤ spectralRadius ℂ (m.normedCarrierGenerator a)) :
    ENNReal.ofReal r ≤ m.generatorRadius a := bound

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
