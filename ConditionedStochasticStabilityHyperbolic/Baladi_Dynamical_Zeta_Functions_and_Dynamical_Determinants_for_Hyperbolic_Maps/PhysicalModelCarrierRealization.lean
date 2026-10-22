module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarrierGenerator
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarrierRadius
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarrierRadius
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldMatrixCoefficients

/-! The physical dense core and regular realization on the native carrier, with the actual generator
intertwining proved from physical rows. -/

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

local instance carrierNormed : NormedAddCommGroup m.strongCarrier := m.strongCarrierNormed
local instance carrierSemi : SeminormedAddCommGroup m.strongCarrier := m.strongCarrierSemi
local instance carrierScalar : NormedSpace ℂ m.strongCarrier := m.strongCarrierScalar

def carrierCore : SmoothSupportedManifoldCore.core (E := E) V →ₗ[ℂ] m.strongCarrier :=
  coreLift m.qa

def carrierRealize : Reg →L[ℂ] m.strongCarrier := m.realize

theorem carrierRealize_core (c : SmoothSupportedManifoldCore.core (E := E) V) :
    m.carrierRealize (m.regularCore c) = m.carrierCore c := m.realize_core c

theorem carrierGenerator_regular_intertwining
    (rows : PhysicalManifoldRowSources.Data m) (a : Ω) :
    m.carrierRealize.comp (InvariantFiniteRegularTransfer.operator m.view m.view_injective
      m.maps m.weight m.invariant m.regularConstant m.regularBound a) =
      (m.carrierGenerator a).comp m.carrierRealize :=
  m.generator_regular_intertwining rows a

theorem generatorRadius_lower_of_spectralRadius (a : Ω) (r : ℝ)
    (bound : ENNReal.ofReal r ≤ spectralRadius ℂ (m.carrierGenerator a)) :
    ENNReal.ofReal r ≤ m.generatorRadius a := bound

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
