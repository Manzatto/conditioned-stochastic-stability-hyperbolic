module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldInclusionTower

/-! Literal physical weaker exponents identify the canonical weak completion
with a fresh physical anisotropic model. This supplies the norm equality
needed to apply the analytic producer at a second admissible exponent pair. -/

public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators
namespace ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
open LeanShared DyadicCompletion CompletedChartPairTransfer FiniteRegularTransferRealization

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

variable (a b : m.localization.indices → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
  (ea eb : m.localization.indices → Bool → ℝ)
  (hea : ∀ i j, 0 ≤ ea i j) (heb : ∀ i j, 0 ≤ eb i j)

/-- Choose the actual strong model with two successive losses before its
primitive sources are instantiated. No norms or operators are changed. -/
@[expose] def twoStepModel :
    Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex)
      (Reg := Reg) (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ :=
  { m with
    lossH := a
    lossW := fun i => a i + b i
    lossH_positive := ha
    lossW_positive := fun i => add_pos (ha i) (hb i)
    extraH := ea
    extraW := fun i j => ea i j + eb i j
    extraH_nonnegative := hea
    extraW_nonnegative := fun i j => add_nonneg (hea i j) (heb i j) }

end Data
end ConditionedStochasticStabilityHyperbolic.PhysicalManifoldModel
