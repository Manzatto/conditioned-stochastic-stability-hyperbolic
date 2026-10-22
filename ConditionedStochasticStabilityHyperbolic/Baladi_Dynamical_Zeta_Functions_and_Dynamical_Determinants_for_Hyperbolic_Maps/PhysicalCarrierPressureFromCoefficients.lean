module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNormedCarrierRealization
public import LeanShared.Dynamics.BasicHyperbolicSpectralRadiusLower

/-! Seal the native generator-radius conclusion while the ordinary regular
space remains abstract. The geometric input is the literal matrix-coefficient
identity; no spectral lower bound is supplied as a premise. -/

public noncomputable section
open Set IsManifold Bundle MeasureTheory
open scoped Manifold ContDiff

namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
open LeanShared

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]

namespace Data
variable (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex)
  (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

local instance : NormedAddCommGroup m.strongCarrier := m.strongCarrierNormed
local instance : NormedSpace ℂ m.strongCarrier := m.normedCarrierScalar
local instance : CompleteSpace m.strongCarrier := m.normedCarrierComplete

theorem exp_pressure_le_generatorRadius_from_coefficients
    (T : M ≃ₜ M) (Λ : Set M) (b : HyperbolicBasicSet.BasicData (E := E) T Λ V)
    {r q : ℝ} (regularity : 1 < r) (weightOrder : 0 < q)
    (forwardRegular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (inverseRegular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T.symm)
    (mixing : HyperbolicBasicSet.MixingOn T Λ)
    (referenceMeasure : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (ν : Measure E) [ν.IsAddHaarMeasure]
    (weightRegular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q m.weight)
    (positive : ∀ x ∈ Λ, 0 < m.weight x)
    (pressureValue : ℝ)
    (pressure_eq : ThermodynamicDefinitions.pressure T (b.hyperbolic.potential m.weight) Λ =
      (pressureValue : EReal))
    (a : Ω) (pairing : m.strongCarrier →L[ℂ] ℂ) (seed : m.strongCarrier)
    (coefficient : ∀ n : ℕ,
      (∫⁻ x, ENNReal.ofReal
        (∏ j ∈ Finset.range (n + 1), m.weight ((T : M → M)^[j] x))
          ∂(referenceMeasure.measure ν)) =
        ENNReal.ofReal ‖pairing (((m.normedCarrierGenerator a) ^ n) seed)‖) :
    ENNReal.ofReal (Real.exp pressureValue) ≤ m.generatorRadius a := by
  apply m.generatorRadius_lower_of_normedCarrier a (Real.exp pressureValue)
  exact b.exp_pressure_le_spectralRadius_from_coefficients regularity weightOrder
    forwardRegular inverseRegular mixing referenceMeasure ν m.weight weightRegular positive
    pressureValue pressure_eq (m.normedCarrierGenerator a) pairing seed coefficient

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
